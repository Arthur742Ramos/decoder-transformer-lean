#!/usr/bin/env python3
"""Render a small decoder checkpoint JSON file as an Isabelle theory.

The importer is deliberately conservative.  It checks every declared shape,
dimension, and numeric leaf before rendering Isabelle syntax, and it uses a
fixed identity-RoPE convention for this first checkpoint format.  The output
is deterministic so that a generated theory can be reviewed and rebuilt from
the JSON source without hidden preprocessing state.
"""

from __future__ import annotations

import argparse
import json
import math
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any, Iterable


SCALAR_FIELDS = (
    "query_head_count",
    "kv_head_count",
    "model_dimension",
    "head_dimension",
    "hidden_dimension",
)
VECTOR_FIELDS = ("attention_gain", "mlp_gain")
TENSOR_FIELDS = ("query_weights", "key_weights", "value_weights")
MATRIX_FIELDS = (
    "output_weights",
    "gate_weights",
    "up_weights",
    "down_weights",
    "embedding",
    "vocabulary_weights",
)


class CheckpointError(ValueError):
    """A malformed checkpoint with a user-actionable error message."""


def _finite_number(value: Any, path: str) -> int | float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise CheckpointError(f"{path}: expected a finite JSON number")
    if not math.isfinite(float(value)):
        raise CheckpointError(f"{path}: number is not finite")
    return value


def _positive_int(value: Any, path: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise CheckpointError(f"{path}: expected a positive integer")
    return value


def _vector(value: Any, path: str) -> list[int | float]:
    if not isinstance(value, list):
        raise CheckpointError(f"{path}: expected a JSON array")
    return [_finite_number(item, f"{path}[{index}]") for index, item in enumerate(value)]


def _matrix(value: Any, path: str) -> list[list[int | float]]:
    if not isinstance(value, list):
        raise CheckpointError(f"{path}: expected a JSON array of rows")
    return [_vector(row, f"{path}[{index}]") for index, row in enumerate(value)]


def _tensor3(value: Any, path: str) -> list[list[list[int | float]]]:
    if not isinstance(value, list):
        raise CheckpointError(f"{path}: expected a JSON array of matrices")
    return [_matrix(matrix, f"{path}[{index}]") for index, matrix in enumerate(value)]


def _check_vector_shape(value: list[int | float], expected: int, path: str) -> None:
    if len(value) != expected:
        raise CheckpointError(f"{path}: expected length {expected}, got {len(value)}")


def _check_matrix_shape(
    value: list[list[int | float]], rows: int, cols: int, path: str
) -> None:
    if len(value) != rows:
        raise CheckpointError(f"{path}: expected {rows} rows, got {len(value)}")
    for index, row in enumerate(value):
        if len(row) != cols:
            raise CheckpointError(
                f"{path}[{index}]: expected {cols} columns, got {len(row)}"
            )


def _check_tensor_shape(
    value: list[list[list[int | float]]],
    dims: tuple[int, int, int],
    path: str,
) -> None:
    if len(value) != dims[0]:
        raise CheckpointError(f"{path}: expected first dimension {dims[0]}, got {len(value)}")
    for index, matrix in enumerate(value):
        _check_matrix_shape(matrix, dims[1], dims[2], f"{path}[{index}]")


def load_checkpoint(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CheckpointError(f"cannot read {path}: {error}") from error
    if not isinstance(data, dict):
        raise CheckpointError("checkpoint root must be a JSON object")

    missing = [field for field in (*SCALAR_FIELDS, "norm_epsilon", *VECTOR_FIELDS, *TENSOR_FIELDS, *MATRIX_FIELDS) if field not in data]
    if missing:
        raise CheckpointError(f"missing required fields: {', '.join(missing)}")

    for field in SCALAR_FIELDS:
        data[field] = _positive_int(data[field], field)
    data["norm_epsilon"] = _finite_number(data["norm_epsilon"], "norm_epsilon")
    if float(data["norm_epsilon"]) <= 0:
        raise CheckpointError("norm_epsilon: expected a positive number")

    dimensions = {
        "q": data["query_head_count"],
        "kv": data["kv_head_count"],
        "model": data["model_dimension"],
        "head": data["head_dimension"],
        "hidden": data["hidden_dimension"],
    }
    if dimensions["model"] != dimensions["q"] * dimensions["head"]:
        raise CheckpointError("model_dimension must equal query_head_count * head_dimension")
    if dimensions["q"] % dimensions["kv"] != 0:
        raise CheckpointError("kv_head_count must divide query_head_count")

    for field in VECTOR_FIELDS:
        data[field] = _vector(data[field], field)
        _check_vector_shape(data[field], dimensions["model"], field)

    tensor_shapes = {
        "query_weights": (dimensions["q"], dimensions["model"], dimensions["head"]),
        "key_weights": (dimensions["kv"], dimensions["model"], dimensions["head"]),
        "value_weights": (dimensions["kv"], dimensions["model"], dimensions["head"]),
    }
    for field, shape in tensor_shapes.items():
        data[field] = _tensor3(data[field], field)
        _check_tensor_shape(data[field], shape, field)

    for field in ("embedding", "vocabulary_weights"):
        data[field] = _matrix(data[field], field)
        if len(data[field]) != 2:
            raise CheckpointError(
                f"{field}: this generated theory format requires exactly two rows"
            )

    matrix_shapes = {
        "output_weights": (dimensions["q"] * dimensions["head"], dimensions["model"]),
        "gate_weights": (dimensions["model"], dimensions["hidden"]),
        "up_weights": (dimensions["model"], dimensions["hidden"]),
        "down_weights": (dimensions["hidden"], dimensions["model"]),
        "embedding": (len(data["embedding"]), dimensions["model"]),
        "vocabulary_weights": (len(data["vocabulary_weights"]), dimensions["model"]),
    }
    for field, shape in matrix_shapes.items():
        if field not in ("embedding", "vocabulary_weights"):
            data[field] = _matrix(data[field], field)
        _check_matrix_shape(data[field], shape[0], shape[1], field)
    if not data["embedding"]:
        raise CheckpointError("embedding: expected at least one row")
    if not data["vocabulary_weights"]:
        raise CheckpointError("vocabulary_weights: expected at least one row")

    name = data.get("name", "imported_decoder_checkpoint")
    if not isinstance(name, str) or not name.isidentifier():
        raise CheckpointError("name: expected an Isabelle-safe identifier")
    provenance = data.get("provenance", "unspecified fixture")
    if not isinstance(provenance, str):
        raise CheckpointError("provenance: expected a string when present")
    data["name"] = name
    data["provenance"] = provenance
    return data


def _real_literal(value: int | float) -> str:
    """Render a finite JSON number without relying on Isabelle eval."""
    decimal = Decimal(str(value))
    if not decimal.is_finite():
        raise CheckpointError(f"non-finite numeric literal: {value!r}")
    rendered = format(decimal, "f")
    if "." in rendered:
        rendered = rendered.rstrip("0").rstrip(".")
    if rendered in {"", "-0"}:
        return "0"
    return rendered


def _isabelle_list(value: Iterable[Any]) -> str:
    return "[" + ", ".join(
        _isabelle_list(item) if isinstance(item, list) else _real_literal(item)
        for item in value
    ) + "]"


def render_theory(data: dict[str, Any], source_name: str) -> str:
    name = data["name"]
    fields = {
        "query_weights": "imported_query_weights",
        "key_weights": "imported_key_weights",
        "value_weights": "imported_value_weights",
        "output_weights": "imported_output_weights",
        "gate_weights": "imported_gate_weights",
        "up_weights": "imported_up_weights",
        "down_weights": "imported_down_weights",
    }
    definitions: list[str] = []
    for field in TENSOR_FIELDS:
        definitions.append(
            f'definition {fields[field]} :: "real tensor3" where\n'
            f'  "{fields[field]} = {_isabelle_list(data[field])}"\n'
        )
    for field in ("output_weights", "gate_weights", "up_weights", "down_weights"):
        definitions.append(
            f'definition {fields[field]} :: "real matrix" where\n'
            f'  "{fields[field]} = {_isabelle_list(data[field])}"\n'
        )
    definitions.extend(
        [
            'definition imported_attention_gain :: "real vector" where\n'
            f'  "imported_attention_gain = {_isabelle_list(data["attention_gain"])}"\n',
            'definition imported_mlp_gain :: "real vector" where\n'
            f'  "imported_mlp_gain = {_isabelle_list(data["mlp_gain"])}"\n',
            'definition imported_embedding_rows :: "real matrix" where\n'
            f'  "imported_embedding_rows = {_isabelle_list(data["embedding"])}"\n',
            'definition imported_embedding :: "nat \\<Rightarrow> real vector" where\n'
            '  "imported_embedding token =\n'
            '    (if token < length imported_embedding_rows\n'
            '     then imported_embedding_rows ! token else [])"\n',
            'definition imported_vocabulary_weights :: "real matrix" where\n'
            f'  "imported_vocabulary_weights = {_isabelle_list(data["vocabulary_weights"])}"\n',
        ]
    )
    definitions.append(
        'definition imported_modern_layer :: modern_decoder_layer_parameters where\n'
        '  "imported_modern_layer =\n'
        '    \\<lparr>modern_query_head_count = '
        f'{data["query_head_count"]},\n'
        '      modern_kv_head_count = '
        f'{data["kv_head_count"]},\n'
        '      modern_model_dimension = '
        f'{data["model_dimension"]},\n'
        '      modern_head_dimension = '
        f'{data["head_dimension"]},\n'
        '      modern_hidden_dimension = '
        f'{data["hidden_dimension"]},\n'
        '      modern_norm_epsilon = '
        f'{_real_literal(data["norm_epsilon"])},\n'
        '      modern_rope = (\\<lambda>position x. x),\n'
        '      modern_attention_gain = imported_attention_gain,\n'
        '      modern_mlp_gain = imported_mlp_gain,\n'
        '      modern_query_weights = imported_query_weights,\n'
        '      modern_key_weights = imported_key_weights,\n'
        '      modern_value_weights = imported_value_weights,\n'
        '      modern_output_weights = imported_output_weights,\n'
        '      modern_gate_weights = imported_gate_weights,\n'
        '      modern_up_weights = imported_up_weights,\n'
        '      modern_down_weights = imported_down_weights\\<rparr>"\n'
    )
    definitions.append(
        'definition imported_modern_layers :: "modern_decoder_layer_parameters list" where\n'
        '  "imported_modern_layers = [imported_modern_layer]"\n'
    )

    return (
        "(* Generated deterministically by tools/import_decoder_checkpoint.py. *)\n"
        f"(* Source: {source_name}; provenance: {data['provenance']} *)\n\n"
        "theory Imported_Decoder_Checkpoint\n"
        "  imports Tiny_Decoder_Checkpoint\n"
        "begin\n\n"
        "section \\<open>Imported nonzero checkpoint\\<close>\n\n"
        "text \\<open>\n"
        "  This theory is generated from a shape-checked JSON fixture.  The\n"
        "  fixture is intentionally synthetic rather than a claim about a\n"
        "  trained model; every listed projection is nonzero and RoPE is the\n"
        "  explicit identity convention of this importer format.\n"
        "\\<close>\n\n"
        + "\n".join(definitions)
        + "\n"
        "lemma imported_modern_layer_valid:\n"
        "  \"valid_modern_decoder_layer imported_modern_layer\"\n"
        "  by (simp add: valid_modern_decoder_layer_def imported_modern_layer_def\n"
        "      imported_attention_gain_def imported_mlp_gain_def\n"
        "      imported_query_weights_def imported_key_weights_def\n"
        "      imported_value_weights_def imported_output_weights_def\n"
        "      imported_gate_weights_def imported_up_weights_def\n"
        "      imported_down_weights_def vector_shape_def matrix_shape_def\n"
        "      tensor3_shape_def)\n\n"
        "lemma imported_modern_stack_valid:\n"
        "  \"valid_modern_decoder_stack imported_modern_layers\"\n"
        "  using imported_modern_layer_valid\n"
        "  by (simp add: imported_modern_layers_def valid_modern_decoder_stack_def)\n\n"
        "lemma imported_embedding_rows_shape:\n"
        "  \"matrix_shape 2 2 imported_embedding_rows\"\n"
        "  by (simp add: imported_embedding_rows_def matrix_shape_def)\n\n"
        "lemma imported_embedding_zero [simp]:\n"
        "  \"imported_embedding 0 = [1, 0]\"\n"
        "  by (simp add: imported_embedding_def imported_embedding_rows_def)\n\n"
        "lemma imported_embedding_one [simp]:\n"
        "  \"imported_embedding 1 = [0, 1]\"\n"
        "  by (simp add: imported_embedding_def imported_embedding_rows_def)\n\n"
        "lemma imported_vocabulary_weights_shape:\n"
        "  \"matrix_shape 2 2 imported_vocabulary_weights\"\n"
        "  by (simp add: imported_vocabulary_weights_def matrix_shape_def)\n\n"
        "lemma imported_checkpoint_has_nonzero_weights:\n"
        "  \"imported_query_weights \\<noteq> [[[0, 0], [0, 0]]] \\<and>\n"
        "   imported_key_weights \\<noteq> [[[0, 0], [0, 0]]] \\<and>\n"
        "   imported_value_weights \\<noteq> [[[0, 0], [0, 0]]] \\<and>\n"
        "   imported_output_weights \\<noteq> [[0, 0], [0, 0]] \\<and>\n"
        "   imported_gate_weights \\<noteq> [[0, 0], [0, 0]] \\<and>\n"
        "   imported_up_weights \\<noteq> [[0, 0], [0, 0]] \\<and>\n"
        "   imported_down_weights \\<noteq> [[0, 0], [0, 0]]\"\n"
        "  by (simp add: imported_query_weights_def imported_key_weights_def\n"
        "      imported_value_weights_def imported_output_weights_def\n"
        "      imported_gate_weights_def imported_up_weights_def\n"
        "      imported_down_weights_def)\n\n"
        "theorem imported_cached_prompt_refinement:\n"
        "  \"fst (cached_modern_decoder_stack_run imported_modern_layers start\n"
        "      (empty_modern_transformer_cache imported_modern_layers)\n"
        "      (map imported_embedding tokens)) =\n"
        "    full_modern_decoder_stack imported_modern_layers start\n"
        "      (map imported_embedding tokens)\"\n"
        "  by (rule initialized_modern_cached_run_equals_full\n"
        "      [OF imported_modern_stack_valid])\n\n"
        "theorem imported_cached_prompt_cache:\n"
        "  \"modern_transformer_cache_matches imported_modern_layers start\n"
        "      (map imported_embedding tokens)\n"
        "      (snd (cached_modern_decoder_stack_run imported_modern_layers start\n"
        "        (empty_modern_transformer_cache imported_modern_layers)\n"
        "        (map imported_embedding tokens)))\"\n"
        "  by (rule initialized_modern_cached_run_cache_invariant\n"
        "      [OF imported_modern_stack_valid])\n\n"
        "theorem imported_cached_next_token_refinement:\n"
        "  assumes cache:\n"
        "    \"modern_generation_cache_matches imported_embedding\n"
        "      imported_modern_layers start tokens caches\"\n"
        "  shows \"fst (cached_modern_generation_evaluate imported_modern_layers\n"
        "      imported_embedding start 2 imported_vocabulary_weights tokens caches) =\n"
        "    next_token_distribution 2 imported_vocabulary_weights\n"
        "      (last (full_modern_decoder_stack imported_modern_layers start\n"
        "        (map imported_embedding tokens)))\"\n"
        "  by (rule cached_modern_next_token_distribution_correct[OF cache])\n\n"
        "theorem imported_initialized_generation_state_valid:\n"
        "  assumes nonempty: \"tokens \\<noteq> []\"\n"
        "  shows \"modern_generation_cache_matches imported_embedding\n"
        "      imported_modern_layers start\n"
        "      (fst (initialize_modern_generation_state imported_modern_layers\n"
        "        imported_embedding start tokens))\n"
        "      (snd (initialize_modern_generation_state imported_modern_layers\n"
        "        imported_embedding start tokens))\"\n"
        "  by (rule initialize_modern_generation_state_correct\n"
        "      [OF imported_modern_stack_valid nonempty])\n\n"
        "end\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path, help="checkpoint JSON file")
    parser.add_argument(
        "--output",
        type=Path,
        help="generated theory path (default: sibling Imported_Decoder_Checkpoint.thy)",
    )
    args = parser.parse_args()
    try:
        data = load_checkpoint(args.checkpoint)
        output = args.output or args.checkpoint.parent.parent / "Imported_Decoder_Checkpoint.thy"
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            render_theory(data, args.checkpoint.name), encoding="utf-8", newline="\n"
        )
    except (CheckpointError, OSError, InvalidOperation) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
