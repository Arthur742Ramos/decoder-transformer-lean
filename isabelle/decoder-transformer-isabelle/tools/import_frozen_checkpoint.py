#!/usr/bin/env python3
"""Import a compact, reproducible trace from a frozen public checkpoint.

The full model is intentionally not copied into the AFP entry.  This importer
checks the frozen TinyStories-1M GPT-Neo configuration and state-dict hash,
then renders one complete layer-0, position-0 linear activation slice:
embedding plus position input, and one Q/K/V/MLP projection row.  Every scalar
is preserved as its exact binary32 sign/exponent/fraction triple, so the
generated Isabelle theory can replay the FMA certificate without trusting
decimal re-parsing.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import struct
from pathlib import Path
from typing import Any, Iterable

MODEL_ID = "roneneldan/TinyStories-1M"
REVISION = "77f1b168e219585646439073245fe87e56b3023e"
CONFIG_URL = (
    "https://huggingface.co/roneneldan/TinyStories-1M/resolve/"
    f"{REVISION}/config.json"
)
CHECKPOINT_URL = (
    "https://huggingface.co/roneneldan/TinyStories-1M/resolve/"
    f"{REVISION}/pytorch_model.bin"
)
EXPECTED_CONFIG = {
    "architectures": ["GPTNeoForCausalLM"],
    "activation_function": "gelu_new",
    "attention_dropout": 0,
    "attention_layers": [
        "global", "local", "global", "local",
        "global", "local", "global", "local",
    ],
    "attention_types": [[["global", "local"], 4]],
    "bos_token_id": 50256,
    "embed_dropout": 0,
    "eos_token_id": 50256,
    "intermediate_size": None,
    "layer_norm_epsilon": 1e-5,
    "max_position_embeddings": 2048,
    "model_type": "gpt_neo",
    "hidden_size": 64,
    "num_layers": 8,
    "num_heads": 16,
    "resid_dropout": 0,
    "torch_dtype": "float32",
    "use_cache": True,
    "vocab_size": 50257,
    "window_size": 256,
}
EXPECTED_CONFIG_SHA256 = (
    "ff74c30d5ebb5ab1da0f2ea479adf7197c504b42b5522a858c334ab91ed4958c"
)
EXPECTED_CHECKPOINT_SHA256 = (
    "07f9609ea882b8163ff3b23d40e2b82cb715d409631beb15c84b164f3877dae7"
)
TOKEN_ID = 464
POSITION = 0
ROW = 0
KERNELS = (
    ("layer0_query_row0", "transformer.h.0.attn.attention.q_proj.weight"),
    ("layer0_key_row0", "transformer.h.0.attn.attention.k_proj.weight"),
    ("layer0_value_row0", "transformer.h.0.attn.attention.v_proj.weight"),
    ("layer0_mlp_fc_row0", "transformer.h.0.mlp.c_fc.weight"),
)
EXPECTED_KERNEL_SHAPES = {
    "transformer.h.0.attn.attention.q_proj.weight": (64, 64),
    "transformer.h.0.attn.attention.k_proj.weight": (64, 64),
    "transformer.h.0.attn.attention.v_proj.weight": (64, 64),
    "transformer.h.0.mlp.c_fc.weight": (256, 64),
}


class CheckpointError(ValueError):
    """A malformed or mismatched frozen checkpoint."""


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _bits(value: float) -> list[int]:
    if not math.isfinite(float(value)):
        raise CheckpointError("checkpoint contains a non-finite scalar")
    raw = struct.unpack("<I", struct.pack("<f", float(value)))[0]
    return [(raw >> 31) & 1, (raw >> 23) & 0xFF, raw & 0x7FFFFF]


def _bits_vector(values: Any) -> list[list[int]]:
    # Keep PyTorch optional: load_trace imports it only after the provenance
    # and hash checks, while rendering/tests can use this helper with an
    # already validated float32 tensor without a module-global dependency.
    values = values.detach().cpu().reshape(-1)
    return [_bits(float(value)) for value in values]


def _validate_config(config: dict[str, Any]) -> None:
    for key, expected in EXPECTED_CONFIG.items():
        if config.get(key) != expected:
            raise CheckpointError(
                f"config[{key!r}] must be {expected!r}, got {config.get(key)!r}"
            )


def load_trace(checkpoint: Path, config_path: Path) -> dict[str, Any]:
    try:
        config = json.loads(config_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CheckpointError(f"cannot read config: {error}") from error
    if not isinstance(config, dict):
        raise CheckpointError("config root must be an object")
    _validate_config(config)
    config_sha256 = _sha256(config_path)
    if config_sha256 != EXPECTED_CONFIG_SHA256:
        raise CheckpointError(
            "config SHA-256 does not match the pinned TinyStories revision: "
            f"expected {EXPECTED_CONFIG_SHA256}, got {config_sha256}"
        )

    checkpoint_sha256 = _sha256(checkpoint)
    if checkpoint_sha256 != EXPECTED_CHECKPOINT_SHA256:
        raise CheckpointError(
            "checkpoint SHA-256 does not match the pinned TinyStories revision: "
            f"expected {EXPECTED_CHECKPOINT_SHA256}, got {checkpoint_sha256}"
        )

    try:
        import torch
    except ModuleNotFoundError as error:
        raise CheckpointError(
            "PyTorch is required only for loading the frozen checkpoint; "
            "renderer and metadata checks do not require it"
        ) from error

    try:
        state = torch.load(checkpoint, map_location="cpu")
    except (OSError, RuntimeError, EOFError) as error:
        raise CheckpointError(f"cannot load PyTorch checkpoint: {error}") from error
    if not isinstance(state, dict):
        raise CheckpointError("checkpoint state must be a mapping")

    required = [
        "transformer.wte.weight",
        "transformer.wpe.weight",
        *(parameter for _, parameter in KERNELS),
    ]
    missing = [parameter for parameter in required if parameter not in state]
    if missing:
        raise CheckpointError(f"checkpoint is missing: {', '.join(missing)}")

    embedding = state["transformer.wte.weight"]
    position_embedding = state["transformer.wpe.weight"]
    if tuple(embedding.shape) != (EXPECTED_CONFIG["vocab_size"], EXPECTED_CONFIG["hidden_size"]):
        raise CheckpointError(f"unexpected token embedding shape: {tuple(embedding.shape)}")
    if tuple(position_embedding.shape) != (
        EXPECTED_CONFIG["max_position_embeddings"], EXPECTED_CONFIG["hidden_size"]
    ):
        raise CheckpointError(f"unexpected position embedding shape: {tuple(position_embedding.shape)}")
    if embedding.dtype != torch.float32 or position_embedding.dtype != torch.float32:
        raise CheckpointError("the selected embeddings must be binary32")

    token_embedding = embedding[TOKEN_ID]
    position_vector = position_embedding[POSITION]
    input_activation = (token_embedding + position_vector).to(torch.float32)
    if max(abs(float(value)) for value in input_activation) >= 1:
        raise CheckpointError("selected input activation is outside the certificate range")

    kernels: list[dict[str, Any]] = []
    for label, parameter in KERNELS:
        tensor = state[parameter]
        if tensor.dtype != torch.float32 or tensor.ndim != 2:
            raise CheckpointError(f"{parameter}: expected a binary32 matrix")
        expected_shape = EXPECTED_KERNEL_SHAPES[parameter]
        if tuple(tensor.shape) != expected_shape:
            raise CheckpointError(
                f"{parameter}: expected shape {expected_shape}, got {tuple(tensor.shape)}"
            )
        row = tensor[ROW]
        if row.numel() != EXPECTED_CONFIG["hidden_size"]:
            raise CheckpointError(f"{parameter}: selected row has the wrong length")
        if max(abs(float(value)) for value in row) >= 1:
            raise CheckpointError(f"{parameter}: selected row is outside the certificate range")
        reference = torch.dot(input_activation, row).to(torch.float32)
        kernels.append(
            {
                "label": label,
                "parameter": parameter,
                "row": ROW,
                "weights": _bits_vector(row),
                "reference_output": _bits(float(reference)),
            }
        )

    return {
        "name": "frozen_tinystories_1m_trace",
        "provenance": {
            "model": MODEL_ID,
            "revision": REVISION,
            "config_url": CONFIG_URL,
            "checkpoint_url": CHECKPOINT_URL,
            "config_sha256": config_sha256,
            "checkpoint_sha256": checkpoint_sha256,
            "architecture": "GPT-Neo causal language model",
            "scope": (
                "exact binary32 layer-0 position-0 linear activation slice; "
                "four selected Q/K/V/MLP projection rows"
            ),
            "bound_interpretation": (
                "replayable local FMA certificate demonstration; "
                "not a numerical accuracy estimate"
            ),
        },
        "config": EXPECTED_CONFIG,
        "trace": {
            "token_id": TOKEN_ID,
            "token_text": "The",
            "position": POSITION,
            "hidden_dimension": EXPECTED_CONFIG["hidden_size"],
            "embedding": _bits_vector(token_embedding),
            "position_embedding": _bits_vector(position_vector),
            "input_activation": _bits_vector(input_activation),
            "kernels": kernels,
            "rounding_budget": 1,
            "witness_policy": "previous FMA accumulator",
            "error_bound_interpretation": (
                "64 is the worst-case 64-step sum of unit local budgets; "
                "it is not an observed or end-to-end accuracy bound"
            ),
        },
    }


def _tuple_term(value: list[int]) -> str:
    return "(" + ", ".join(str(component) for component in value) + ")"


def _scalar_vector_definitions(
    name: str, values: list[list[int]]
) -> tuple[list[str], list[str]]:
    """Render scalar lifts followed by a transparent list of those scalars."""
    scalar_names = [f"{name}_{index}" for index in range(len(values))]
    definitions = [
        f'lift_definition {scalar} :: frozen_binary32\n'
        f'  is "{_tuple_term(value)}" .\n'
        for scalar, value in zip(scalar_names, values)
    ]
    definitions.append(
        f'definition {name} :: "frozen_binary32 vector" where\n'
        f'  "{name} = [{", ".join(scalar_names)}]"\n'
    )
    return definitions, scalar_names


def _scalar_field_facts(scalar_names: list[str]) -> str:
    facts: list[str] = []
    for scalar in scalar_names:
        facts.append(
            f'''lemma {scalar}_finite:
  "IEEE.is_finite {scalar}"
  unfolding IEEE.is_finite_def IEEE.is_normal_def
      IEEE.is_denormal_def IEEE.is_zero_def
  by transfer (simp add: emax_eq)

lemma {scalar}_small:
  "\\<bar>IEEE.valof {scalar}\\<bar> < 1"
  by transfer (simp add: valof_eq IEEE.bias_def; arith)

'''
        )
    return "".join(facts)


def _simp_fact_list(facts: list[str]) -> str:
    return " ".join(facts)


def render_theory(data: dict[str, Any], source_name: str) -> str:
    trace = data["trace"]
    definitions: list[str] = []
    embedding_definitions, _ = _scalar_vector_definitions(
        "frozen_embedding", trace["embedding"]
    )
    position_definitions, _ = _scalar_vector_definitions(
        "frozen_position_embedding", trace["position_embedding"]
    )
    input_definitions, input_scalars = _scalar_vector_definitions(
        "frozen_input_activation", trace["input_activation"]
    )
    definitions.extend(embedding_definitions)
    definitions.extend(position_definitions)
    definitions.extend(input_definitions)
    kernel_names: list[str] = []
    kernel_scalars: list[list[str]] = []
    for index, kernel in enumerate(trace["kernels"]):
        name = f"frozen_kernel_{index}"
        kernel_names.append(name)
        kernel_definitions, scalars = _scalar_vector_definitions(
            name, kernel["weights"]
        )
        definitions.extend(kernel_definitions)
        kernel_scalars.append(scalars)
    definitions.append(
        'definition frozen_trace_kernels :: "frozen_binary32 vector list" where\n'
        f'  "frozen_trace_kernels = [{", ".join(kernel_names)}]"\n'
    )
    definitions.append(
        'definition frozen_trace_witnesses :: "frozen_binary32 vector list" where\n'
        '  "frozen_trace_witnesses =\n'
        '    map (ieee_fma_dot_tail_witnesses frozen_input_activation)\n'
        '      frozen_trace_kernels"\n'
    )
    definitions.append(
        'lift_definition frozen_threshold_128 :: frozen_binary32\n'
        '  is "(0, 134, 0)" .\n'
    )

    cert_lemmas: list[str] = []
    for index, name in enumerate(kernel_names):
        cert_lemmas.append(
            f"""lemma frozen_kernel_{index}_certificate:
  "ieee_fma_dot_certificate
      (IEEE.threshold TYPE(frozen_binary32)) 1
      frozen_input_activation {name}
      (ieee_fma_dot_tail_witnesses frozen_input_activation {name})"
  by (rule ieee_fma_dot_tail_certificate,
      simp_all add: frozen_input_activation_def {name}_def
        frozen_input_finite {name}_finite frozen_input_small
        {name}_small frozen_threshold_129_bound)
"""
        )

    scalar_facts = _scalar_field_facts(input_scalars)
    scalar_facts += "".join(
        _scalar_field_facts(scalars) for scalars in kernel_scalars
    )
    kernel_facts = "".join(
        f"""lemma frozen_kernel_{index}_finite:
  "\\<forall>x \\<in> set frozen_kernel_{index}. IEEE.is_finite x"
  by (simp add: frozen_kernel_{index}_def
      {_simp_fact_list([f"{scalar}_finite" for scalar in kernel_scalars[index]])})

lemma frozen_kernel_{index}_small:
  "\\<forall>x \\<in> set frozen_kernel_{index}. \\<bar>IEEE.valof x\\<bar> < 1"
  by (simp add: frozen_kernel_{index}_def
      {_simp_fact_list([f"{scalar}_small" for scalar in kernel_scalars[index]])})

"""
        for index in range(len(kernel_names))
    )
    input_finite_facts = _simp_fact_list(
        [f"{scalar}_finite" for scalar in input_scalars]
    )
    input_small_facts = _simp_fact_list(
        [f"{scalar}_small" for scalar in input_scalars]
    )
    trace_case_proofs = "".join(
        f'''      assume i{index}: "i = {index}"
      show ?thesis using i{index} frozen_kernel_{index}_certificate
        by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)
'''
        + ("      next\n" if index + 1 < len(kernel_names) else "")
        for index in range(len(kernel_names))
    )

    return (
        "(* Generated deterministically by tools/import_frozen_checkpoint.py. *)\n"
        f"(* Model: {data['provenance']['model']}; "
        f"revision: {data['provenance']['revision']} *)\n"
        f"(* Checkpoint URL: {data['provenance']['checkpoint_url']} *)\n"
        f"(* Config SHA256: {data['provenance']['config_sha256']} *)\n"
        f"(* Checkpoint SHA256: {data['provenance']['checkpoint_sha256']} *)\n\n"
        "theory Frozen_TinyStories_Trace\n"
        "  imports IEEE_Trace_Certificate\n"
        "begin\n\n"
        "section \\<open>Frozen TinyStories-1M binary32 activation trace\\<close>\n\n"
        "text \\<open>\n"
        "  This theory is generated from a public frozen TinyStories-1M\n"
        "  GPT-Neo checkpoint.  It preserves exact binary32 bit fields for\n"
        "  token The, position zero, and four layer-zero projection rows.\n"
        "  The certificate covers every FMA step in this selected linear\n"
        "  activation slice; it does not silently claim a full GPT-Neo\n"
        "  attention/GELU/softmax proof.\n"
        "  The error theorem below is intentionally a replayable local FMA\n"
        "  certificate demonstration, not a numerical accuracy estimate: its\n"
        "  bound 64 is the worst-case sum of one unit budget for each of the\n"
        "  64 certified steps in a selected row.\n"
        "\\<close>\n\n"
        "type_synonym frozen_binary32 = \"(8, 23) IEEE.float\"\n\n"
        + "\n".join(definitions)
        + "\n"
        + scalar_facts
        + "lemma frozen_input_shape:\n"
        "  \"length frozen_input_activation = 64\"\n"
        "  by (simp add: frozen_input_activation_def)\n\n"
        "lemma frozen_kernel_shapes:\n"
        "  \"length frozen_trace_kernels = 4 \\<and>\n"
        "   (\\<forall>k \\<in> set frozen_trace_kernels. length k = 64)\"\n"
        "  by (simp add: frozen_trace_kernels_def frozen_kernel_0_def\n"
        "      frozen_kernel_1_def frozen_kernel_2_def frozen_kernel_3_def)\n\n"
        "lemma frozen_input_finite:\n"
        "  \"\\<forall>x \\<in> set frozen_input_activation. IEEE.is_finite x\"\n"
        f"  by (simp add: frozen_input_activation_def {input_finite_facts})\n\n"
        "lemma frozen_input_small:\n"
        "  \"\\<forall>x \\<in> set frozen_input_activation. \\<bar>IEEE.valof x\\<bar> < 1\"\n"
        f"  by (simp add: frozen_input_activation_def {input_small_facts})\n\n"
        "lemma frozen_threshold_128_bound:\n"
        "  \"128 < IEEE.threshold TYPE(frozen_binary32)\"\n"
        "proof -\n"
        "  have exponent: \"IEEE.exponent frozen_threshold_128 = 134\"\n"
        "    by transfer simp\n"
        "  have fraction: \"IEEE.fraction frozen_threshold_128 = 0\"\n"
        "    by transfer simp\n"
        "  have sign: \"IEEE.sign frozen_threshold_128 = 0\"\n"
        "    by transfer simp\n"
        "  have finite: \"IEEE.is_finite frozen_threshold_128\"\n"
        "    unfolding IEEE.is_finite_def IEEE.is_normal_def\n"
        "      IEEE.is_denormal_def IEEE.is_zero_def\n"
        "    using exponent fraction by (simp add: emax_eq)\n"
        "  have val: \"IEEE.valof frozen_threshold_128 = 128\"\n"
        "    using exponent fraction sign by (simp add: valof_eq IEEE.bias_def)\n"
        "  have bound:\n"
        "    \"\\<bar>IEEE.valof frozen_threshold_128\\<bar> <\n"
        "      IEEE.threshold TYPE(frozen_binary32)\"\n"
        "    using float_val_lt_threshold[where a=frozen_threshold_128]\n"
        "      finite val by simp\n"
        "  show ?thesis using bound val by simp\n"
        "qed\n\n"
        "lemma frozen_threshold_129_bound:\n"
        "  \"129 < IEEE.threshold TYPE(frozen_binary32)\"\n"
        "  by (simp add: threshold_def bias_def emax_eq; arith)\n\n"
        + kernel_facts
        + "".join(cert_lemmas)
        + "theorem frozen_trace_certificate:\n"
        "  \"length frozen_trace_witnesses = 4 \\<and>\n"
        "   (\\<forall>i < 4. ieee_fma_dot_certificate\n"
        "      (IEEE.threshold TYPE(frozen_binary32)) 1\n"
        "      frozen_input_activation (frozen_trace_kernels ! i)\n"
        "      (frozen_trace_witnesses ! i))\"\n"
        "proof (rule conjI)\n"
        "  show \"length frozen_trace_witnesses = 4\"\n"
        "    by (simp add: frozen_trace_witnesses_def frozen_trace_kernels_def)\n"
        "  show \"\\<forall>i < 4. ieee_fma_dot_certificate\n"
        "      (IEEE.threshold TYPE(frozen_binary32)) 1\n"
        "      frozen_input_activation (frozen_trace_kernels ! i)\n"
        "      (frozen_trace_witnesses ! i)\"\n"
        "  proof (intro allI impI)\n"
        "    fix i :: nat\n"
        "    assume i_lt: \"i < 4\"\n"
        "    have i_cases: \"i = 0 \\<or> i = 1 \\<or> i = 2 \\<or> i = 3\"\n"
        "      using i_lt by arith\n"
        "    from i_cases\n"
        "    show \"ieee_fma_dot_certificate\n"
        "        (IEEE.threshold TYPE(frozen_binary32)) 1\n"
        "        frozen_input_activation (frozen_trace_kernels ! i)\n"
        "        (frozen_trace_witnesses ! i)\"\n"
        "    proof (elim disjE)\n"
        f"{trace_case_proofs}"
        "    qed\n"
        "  qed\n"
        "qed\n\n"
        "theorem frozen_trace_safe:\n"
        "  \"\\<forall>i < 4. ieee_fma_dot_safe\n"
        "      (IEEE.threshold TYPE(frozen_binary32)) 1\n"
        "      frozen_input_activation (frozen_trace_kernels ! i)\"\n"
        "  using frozen_trace_certificate\n"
        "  by (auto simp: ieee_fma_dot_certificate_imp_safe\n"
        "      frozen_trace_witnesses_def)\n\n"
        "text \\<open>\n"
        "  This is a certificate-replay result only.  The number 64 is a\n"
        "  deliberately conservative compositional envelope, not an estimate\n"
        "  of the TinyStories checkpoint's observed floating-point error.\n"
        "\\<close>\n\n"
        "theorem frozen_trace_error:\n"
        "  \"\\<forall>i < 4. \\<bar>dot_product\n"
        "      (map IEEE.valof frozen_input_activation)\n"
        "      (map IEEE.valof (frozen_trace_kernels ! i)) -\n"
        "      IEEE.valof (ieee_fma_dot frozen_input_activation\n"
        "        (frozen_trace_kernels ! i))\\<bar> \\<le> 64\"\n"
        "proof (intro allI impI)\n"
        "  fix i :: nat\n"
        "  assume i: \"i < 4\"\n"
        "  have cert:\n"
        "    \"ieee_fma_dot_certificate\n"
        "      (IEEE.threshold TYPE(frozen_binary32)) 1\n"
        "      frozen_input_activation (frozen_trace_kernels ! i)\n"
        "      (frozen_trace_witnesses ! i)\"\n"
        "    using frozen_trace_certificate i by simp\n"
        "  have safe:\n"
        "    \"ieee_fma_dot_safe\n"
        "      (IEEE.threshold TYPE(frozen_binary32)) 1\n"
        "      frozen_input_activation (frozen_trace_kernels ! i)\"\n"
        "    by (rule ieee_fma_dot_certificate_imp_safe[OF cert])\n"
        "  have error:\n"
        "    \"\\<bar>dot_product (map IEEE.valof frozen_input_activation)\n"
        "        (map IEEE.valof (frozen_trace_kernels ! i)) -\n"
        "        IEEE.valof (ieee_fma_dot frozen_input_activation\n"
        "          (frozen_trace_kernels ! i))\\<bar> \\<le>\n"
        "      real (min (length frozen_input_activation)\n"
        "        (length (frozen_trace_kernels ! i))) * 1\"\n"
        "    using ieee_fma_dot_error[where epsilon=1, OF _ safe]\n"
        "      by simp\n"
        "  have lengths:\n"
        "    \"min (length frozen_input_activation)\n"
        "        (length (frozen_trace_kernels ! i)) = 64\"\n"
        "    using frozen_input_shape i by (simp add: frozen_kernel_shapes)\n"
        "  from error lengths\n"
        "  show \"\\<bar>dot_product (map IEEE.valof frozen_input_activation)\n"
        "      (map IEEE.valof (frozen_trace_kernels ! i)) -\n"
        "      IEEE.valof (ieee_fma_dot frozen_input_activation\n"
        "        (frozen_trace_kernels ! i))\\<bar> \\<le> 64\"\n"
        "    by simp\n"
        "qed\n\n"
        "end\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--json-output", type=Path, required=True)
    parser.add_argument("--theory-output", type=Path, required=True)
    args = parser.parse_args()
    try:
        data = load_trace(args.checkpoint, args.config)
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.theory_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(
            json.dumps(data, indent=2, sort_keys=False) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        args.theory_output.write_text(
            render_theory(data, args.checkpoint.name),
            encoding="utf-8",
            newline="\n",
        )
    except (CheckpointError, OSError, RuntimeError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
