#!/usr/bin/env python3
"""Import a deterministic multi-layer modern decoder checkpoint.

The format is intentionally small and reviewable: a shared two-row embedding
and vocabulary matrix plus a list of complete modern decoder layer records.
Every layer carries a finite angle table; the generated theory uses the
existing ``rope_rotate`` semantics and proves each layer's shape contract
before applying the general stack and cache-refinement theorems.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any, Iterable

from import_decoder_checkpoint import (
    CheckpointError,
    _check_matrix_shape,
    _check_tensor_shape,
    _check_vector_shape,
    _finite_number,
    _isabelle_list,
    _matrix,
    _positive_int,
    _real_literal,
    _tensor3,
    _vector,
)


LAYER_SCALARS = (
    "query_head_count",
    "kv_head_count",
    "model_dimension",
    "head_dimension",
    "hidden_dimension",
)
LAYER_VECTORS = ("attention_gain", "mlp_gain")
LAYER_TENSORS = ("query_weights", "key_weights", "value_weights")
LAYER_MATRICES = ("output_weights", "gate_weights", "up_weights", "down_weights")


def _read_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CheckpointError(f"cannot read {path}: {error}") from error
    if not isinstance(data, dict):
        raise CheckpointError("checkpoint root must be a JSON object")
    return data


def _validate_layer(layer: Any, index: int) -> dict[str, Any]:
    path = f"layers[{index}]"
    if not isinstance(layer, dict):
        raise CheckpointError(f"{path}: expected an object")
    required = (*LAYER_SCALARS, "norm_epsilon", "rope_angle_table", *LAYER_VECTORS,
                *LAYER_TENSORS, *LAYER_MATRICES)
    missing = [field for field in required if field not in layer]
    if missing:
        raise CheckpointError(f"{path}: missing fields: {', '.join(missing)}")
    for field in LAYER_SCALARS:
        layer[field] = _positive_int(layer[field], f"{path}.{field}")
    layer["norm_epsilon"] = _finite_number(layer["norm_epsilon"], f"{path}.norm_epsilon")
    if float(layer["norm_epsilon"]) <= 0:
        raise CheckpointError(f"{path}.norm_epsilon: expected a positive number")
    q = layer["query_head_count"]
    kv = layer["kv_head_count"]
    model = layer["model_dimension"]
    head = layer["head_dimension"]
    hidden = layer["hidden_dimension"]
    if model != q * head:
        raise CheckpointError(f"{path}: model_dimension must equal query_head_count * head_dimension")
    if q % kv != 0:
        raise CheckpointError(f"{path}: kv_head_count must divide query_head_count")
    layer["rope_angle_table"] = _vector(layer["rope_angle_table"], f"{path}.rope_angle_table")
    if len(layer["rope_angle_table"]) != head // 2:
        raise CheckpointError(
            f"{path}.rope_angle_table: expected {head // 2} entries for pairwise RoPE"
        )
    for field in LAYER_VECTORS:
        layer[field] = _vector(layer[field], f"{path}.{field}")
        _check_vector_shape(layer[field], model, f"{path}.{field}")
    tensor_shapes = {
        "query_weights": (q, model, head),
        "key_weights": (kv, model, head),
        "value_weights": (kv, model, head),
    }
    for field, shape in tensor_shapes.items():
        layer[field] = _tensor3(layer[field], f"{path}.{field}")
        _check_tensor_shape(layer[field], shape, f"{path}.{field}")
    matrix_shapes = {
        "output_weights": (q * head, model),
        "gate_weights": (model, hidden),
        "up_weights": (model, hidden),
        "down_weights": (hidden, model),
    }
    for field, shape in matrix_shapes.items():
        layer[field] = _matrix(layer[field], f"{path}.{field}")
        _check_matrix_shape(layer[field], shape[0], shape[1], f"{path}.{field}")
    return layer


def load_checkpoint(path: Path) -> dict[str, Any]:
    data = _read_json(path)
    required = ("name", "provenance", "embedding", "vocabulary_weights", "layers")
    missing = [field for field in required if field not in data]
    if missing:
        raise CheckpointError(f"missing required fields: {', '.join(missing)}")
    if not isinstance(data["name"], str) or not data["name"].isidentifier():
        raise CheckpointError("name: expected an Isabelle-safe identifier")
    if not isinstance(data["provenance"], str):
        raise CheckpointError("provenance: expected a string")
    if not isinstance(data["layers"], list) or not data["layers"]:
        raise CheckpointError("layers: expected a nonempty array")
    data["embedding"] = _matrix(data["embedding"], "embedding")
    data["vocabulary_weights"] = _matrix(data["vocabulary_weights"], "vocabulary_weights")
    if len(data["embedding"]) != 2:
        raise CheckpointError("embedding must have exactly two rows")
    layers = [_validate_layer(layer, index) for index, layer in enumerate(data["layers"])]
    model = layers[0]["model_dimension"]
    head = layers[0]["head_dimension"]
    if any(layer["model_dimension"] != model or layer["head_dimension"] != head for layer in layers):
        raise CheckpointError("all layers must share model_dimension and head_dimension")
    if len(data["vocabulary_weights"]) != model:
        raise CheckpointError(
            f"vocabulary_weights: expected {model} rows (one per model coordinate)"
        )
    _check_matrix_shape(data["embedding"], 2, model, "embedding")
    _check_matrix_shape(data["vocabulary_weights"], model, 2, "vocabulary_weights")
    data["layers"] = layers
    return data


def _definition(name: str, type_text: str, value: str) -> str:
    return f'definition {name} :: "{type_text}" where\n  "{name} = {value}"\n'


def _layer_definitions(layer: dict[str, Any], index: int) -> list[str]:
    prefix = f"imported_layer{index}"
    names = {
        "query_weights": f"{prefix}_query_weights",
        "key_weights": f"{prefix}_key_weights",
        "value_weights": f"{prefix}_value_weights",
        "output_weights": f"{prefix}_output_weights",
        "gate_weights": f"{prefix}_gate_weights",
        "up_weights": f"{prefix}_up_weights",
        "down_weights": f"{prefix}_down_weights",
        "attention_gain": f"{prefix}_attention_gain",
        "mlp_gain": f"{prefix}_mlp_gain",
        "rope_angle_table": f"{prefix}_rope_angle_table",
        "angles": f"{prefix}_angles",
        "layer": prefix,
    }
    result = [
        _definition(names["query_weights"], "real tensor3", _isabelle_list(layer["query_weights"])),
        _definition(names["key_weights"], "real tensor3", _isabelle_list(layer["key_weights"])),
        _definition(names["value_weights"], "real tensor3", _isabelle_list(layer["value_weights"])),
        _definition(names["output_weights"], "real matrix", _isabelle_list(layer["output_weights"])),
        _definition(names["gate_weights"], "real matrix", _isabelle_list(layer["gate_weights"])),
        _definition(names["up_weights"], "real matrix", _isabelle_list(layer["up_weights"])),
        _definition(names["down_weights"], "real matrix", _isabelle_list(layer["down_weights"])),
        _definition(names["attention_gain"], "real vector", _isabelle_list(layer["attention_gain"])),
        _definition(names["mlp_gain"], "real vector", _isabelle_list(layer["mlp_gain"])),
        _definition(names["rope_angle_table"], "real vector", _isabelle_list(layer["rope_angle_table"])),
    ]
    result.append(
        f'definition {names["angles"]} :: "nat \\<Rightarrow> nat \\<Rightarrow> real" where\n'
        f'  "{names["angles"]} pair position =\n'
        f'    (if pair < length {names["rope_angle_table"]}\n'
        f'     then {names["rope_angle_table"]} ! pair else 0)"\n'
    )
    result.append(
        f'definition {prefix} :: modern_decoder_layer_parameters where\n'
        f'  "{prefix} =\n'
        f'    \\<lparr>modern_query_head_count = {layer["query_head_count"]},\n'
        f'      modern_kv_head_count = {layer["kv_head_count"]},\n'
        f'      modern_model_dimension = {layer["model_dimension"]},\n'
        f'      modern_head_dimension = {layer["head_dimension"]},\n'
        f'      modern_hidden_dimension = {layer["hidden_dimension"]},\n'
        f'      modern_norm_epsilon = {_real_literal(layer["norm_epsilon"])},\n'
        f'      modern_rope = rope_rotate {names["angles"]},\n'
        f'      modern_attention_gain = {names["attention_gain"]},\n'
        f'      modern_mlp_gain = {names["mlp_gain"]},\n'
        f'      modern_query_weights = {names["query_weights"]},\n'
        f'      modern_key_weights = {names["key_weights"]},\n'
        f'      modern_value_weights = {names["value_weights"]},\n'
        f'      modern_output_weights = {names["output_weights"]},\n'
        f'      modern_gate_weights = {names["gate_weights"]},\n'
        f'      modern_up_weights = {names["up_weights"]},\n'
        f'      modern_down_weights = {names["down_weights"]}\\<rparr>"\n'
    )
    return result


def _validity_lemma(layer: dict[str, Any], index: int) -> str:
    prefix = f"imported_layer{index}"
    all_defs = " ".join(
        f"{prefix}_{field}_def"
        for field in (
            "attention_gain",
            "mlp_gain",
            "query_weights",
            "key_weights",
            "value_weights",
            "output_weights",
            "gate_weights",
            "up_weights",
            "down_weights",
        )
    )
    rope_shape = (
        f"  have rope_shape:\n"
        f"    \"\\<forall>position x. vector_shape {layer['head_dimension']} x \\<longrightarrow>\n"
        f"      vector_shape {layer['head_dimension']}\n"
        f"        (rope_rotate {prefix}_angles position x)\"\n"
        f"    by (intro allI impI; rule rope_rotate_preserves_shape)\n"
    )
    return (
        f"lemma imported_layer{index}_valid:\n"
        f"  \"valid_modern_decoder_layer {prefix}\"\n"
        f"proof -\n"
        f"{rope_shape}"
        f"  show ?thesis\n"
        f"    unfolding valid_modern_decoder_layer_def {prefix}_def\n"
        f"      {all_defs}\n"
        f"    using rope_shape\n"
        f"    by (simp add: vector_shape_def matrix_shape_def tensor3_shape_def)\n"
        f"qed\n"
    )


def render_theory(data: dict[str, Any], source_name: str) -> str:
    layer_defs: list[str] = []
    validity: list[str] = []
    for index, layer in enumerate(data["layers"]):
        layer_defs.extend(_layer_definitions(layer, index))
        validity.append(_validity_lemma(layer, index))
    layer_names = [f"imported_layer{index}" for index in range(len(data["layers"]))]
    layer_valid_names = [f"imported_layer{index}_valid" for index in range(len(data["layers"]))]
    model = data["layers"][0]["model_dimension"]
    head = data["layers"][0]["head_dimension"]
    stack_literal = "[" + ", ".join(layer_names) + "]"
    stack_valid = " ".join(layer_valid_names)
    return (
        "(* Generated deterministically by tools/import_multilayer_checkpoint.py. *)\n"
        f"(* Source: {source_name}; provenance: {data['provenance']} *)\n\n"
        "theory Two_Layer_GQA_Checkpoint\n"
        "  imports Tiny_Decoder_Checkpoint\n"
        "begin\n\n"
        "section \\<open>Two-layer GQA, RoPE, and SwiGLU checkpoint\\<close>\n\n"
        "text \\<open>\n"
        "  This generated theory is a deterministic integration fixture.  It\n"
        "  has two modern layers, two query heads sharing one key-value head,\n"
        "  explicit nonzero SwiGLU matrices, and nonzero pairwise RoPE angles.\n"
        "  The fixture is synthetic and carries no trained-model provenance.\n"
        "\\<close>\n\n"
        + _definition("imported_embedding_rows", "real matrix", _isabelle_list(data["embedding"]))
        + _definition(
            "imported_embedding",
            "nat \\<Rightarrow> real vector",
            "(\\<lambda>token. if token < length imported_embedding_rows then\n"
            "      imported_embedding_rows ! token else [])",
        )
        + _definition("imported_vocabulary_weights", "real matrix", _isabelle_list(data["vocabulary_weights"]))
        + "\n".join(layer_defs)
        + _definition("imported_modern_layers", "modern_decoder_layer_parameters list", stack_literal)
        + "\n"
        + "\n".join(validity)
        + "\n"
        + "lemma imported_modern_stack_valid:\n"
        + "  \"valid_modern_decoder_stack imported_modern_layers\"\n"
        + f"  using {stack_valid}\n"
        + "  by (simp add: imported_modern_layers_def valid_modern_decoder_stack_def)\n\n"
        + "lemma imported_gqa_grouping:\n"
        + "  \"grouped_query_head_index 4 2 0 = 0 \\<and>\n"
        + "   grouped_query_head_index 4 2 1 = 0 \\<and>\n"
        + "   grouped_query_head_index 4 2 2 = 1 \\<and>\n"
        + "   grouped_query_head_index 4 2 3 = 1\"\n"
        + "  by (simp add: grouped_query_head_index_def)\n\n"
        + f"lemma imported_embedding_shape:\n  \"matrix_shape 2 {model} imported_embedding_rows\"\n"
        + "  by (simp add: imported_embedding_rows_def matrix_shape_def)\n\n"
        + f"lemma imported_vocabulary_shape:\n  \"matrix_shape {model} 2 imported_vocabulary_weights\"\n"
        + "  by (simp add: imported_vocabulary_weights_def matrix_shape_def)\n\n"
        + "lemma imported_layer0_rope_angle:\n"
        + "  \"imported_layer0_angles 0 0 = 1 / 2\"\n"
        + "  by (simp add: imported_layer0_angles_def imported_layer0_rope_angle_table_def)\n\n"
        + "theorem imported_cached_prompt_refinement:\n"
        + "  \"fst (cached_modern_decoder_stack_run imported_modern_layers start\n"
        + "      (empty_modern_transformer_cache imported_modern_layers)\n"
        + "      (map imported_embedding tokens)) =\n"
        + "    full_modern_decoder_stack imported_modern_layers start\n"
        + "      (map imported_embedding tokens)\"\n"
        + "  by (rule initialized_modern_cached_run_equals_full\n"
        + "      [OF imported_modern_stack_valid])\n\n"
        + "theorem imported_cached_prompt_cache:\n"
        + "  \"modern_transformer_cache_matches imported_modern_layers start\n"
        + "      (map imported_embedding tokens)\n"
        + "      (snd (cached_modern_decoder_stack_run imported_modern_layers start\n"
        + "        (empty_modern_transformer_cache imported_modern_layers)\n"
        + "        (map imported_embedding tokens)))\"\n"
        + "  by (rule initialized_modern_cached_run_cache_invariant\n"
        + "      [OF imported_modern_stack_valid])\n\n"
        + "theorem imported_cached_next_token_refinement:\n"
        + "  assumes cache:\n"
        + "    \"modern_generation_cache_matches imported_embedding\n"
        + "      imported_modern_layers start tokens caches\"\n"
        + "  shows \"fst (cached_modern_generation_evaluate imported_modern_layers\n"
        + "      imported_embedding start 2 imported_vocabulary_weights tokens caches) =\n"
        + "    next_token_distribution 2 imported_vocabulary_weights\n"
        + "      (last (full_modern_decoder_stack imported_modern_layers start\n"
        + "        (map imported_embedding tokens)))\"\n"
        + "  by (rule cached_modern_next_token_distribution_correct[OF cache])\n\n"
        + "theorem imported_initialized_generation_state_valid:\n"
        + "  assumes nonempty: \"tokens \\<noteq> []\"\n"
        + "  shows \"modern_generation_cache_matches imported_embedding\n"
        + "      imported_modern_layers start\n"
        + "      (fst (initialize_modern_generation_state imported_modern_layers\n"
        + "        imported_embedding start tokens))\n"
        + "      (snd (initialize_modern_generation_state imported_modern_layers\n"
        + "        imported_embedding start tokens))\"\n"
        + "  by (rule initialize_modern_generation_state_correct\n"
        + "      [OF imported_modern_stack_valid nonempty])\n\n"
        + "end\n"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        data = load_checkpoint(args.checkpoint)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(
            render_theory(data, args.checkpoint.name), encoding="utf-8", newline="\n"
        )
    except (CheckpointError, OSError, InvalidOperation, ValueError) as error:
        parser.error(str(error))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
