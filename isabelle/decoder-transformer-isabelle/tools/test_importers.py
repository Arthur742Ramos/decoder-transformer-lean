#!/usr/bin/env python3
"""Regression tests for the deterministic checkpoint importers.

These tests deliberately use only the Python standard library.  They verify
that checked-in generated theories are reproducible, that the non-degenerate
GQA routing witness is emitted, and that malformed layer dimensions are
rejected before Isabelle syntax is generated.
"""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path


TOOLS = Path(__file__).resolve().parent
PROJECT = TOOLS.parent
sys.path.insert(0, str(TOOLS))

from import_decoder_checkpoint import (  # noqa: E402
    CheckpointError as DecoderCheckpointError,
    load_checkpoint as load_decoder_checkpoint,
    render_theory as render_decoder_theory,
)
from import_multilayer_checkpoint import (  # noqa: E402
    CheckpointError as MultilayerCheckpointError,
    load_checkpoint as load_multilayer_checkpoint,
    render_theory as render_multilayer_theory,
)
from import_frozen_checkpoint import (  # noqa: E402
    CheckpointError as FrozenCheckpointError,
    EXPECTED_CONFIG,
    load_trace as load_frozen_trace,
    render_theory as render_frozen_theory,
)


class ImporterTests(unittest.TestCase):
    def test_single_layer_generation_is_reproducible(self) -> None:
        source = PROJECT / "checkpoints" / "nonzero_tiny_decoder.json"
        generated = PROJECT / "Imported_Decoder_Checkpoint.thy"
        data = load_decoder_checkpoint(source)
        self.assertEqual(
            generated.read_text(encoding="utf-8"),
            render_decoder_theory(data, source.name),
        )

    def test_multilayer_generation_is_reproducible(self) -> None:
        source = PROJECT / "checkpoints" / "two_layer_gqa_rope_swiglu.json"
        generated = PROJECT / "Two_Layer_GQA_Checkpoint.thy"
        data = load_multilayer_checkpoint(source)
        rendered = render_multilayer_theory(data, source.name)
        self.assertEqual(generated.read_text(encoding="utf-8"), rendered)
        self.assertIn("grouped_query_head_index 4 2 0 = 0", rendered)
        self.assertIn("grouped_query_head_index 4 2 3 = 1", rendered)

    def test_multilayer_import_rejects_non_dividing_kv_heads(self) -> None:
        source = PROJECT / "checkpoints" / "two_layer_gqa_rope_swiglu.json"
        data = json.loads(source.read_text(encoding="utf-8"))
        data = copy.deepcopy(data)
        data["layers"][0]["kv_head_count"] = 3
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / source.name
            candidate.write_text(json.dumps(data), encoding="utf-8")
            with self.assertRaises(MultilayerCheckpointError):
                load_multilayer_checkpoint(candidate)

    def test_single_layer_import_rejects_wrong_projection_shape(self) -> None:
        source = PROJECT / "checkpoints" / "nonzero_tiny_decoder.json"
        data = json.loads(source.read_text(encoding="utf-8"))
        data = copy.deepcopy(data)
        data["query_weights"][0].pop()
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / source.name
            candidate.write_text(json.dumps(data), encoding="utf-8")
            with self.assertRaises(DecoderCheckpointError):
                load_decoder_checkpoint(candidate)

    def test_frozen_trace_generation_is_reproducible(self) -> None:
        source = PROJECT / "checkpoints" / "tinystories_1m_linear_trace.json"
        generated = PROJECT / "Frozen_TinyStories_Trace.thy"
        data = json.loads(source.read_text(encoding="utf-8"))
        self.assertEqual(
            generated.read_text(encoding="utf-8"),
            render_frozen_theory(data, source.name),
        )
        self.assertEqual(
            data["provenance"]["bound_interpretation"],
            "replayable local FMA certificate demonstration; "
            "not a numerical accuracy estimate",
        )
        self.assertIn(
            "certificate demonstration, not a numerical accuracy estimate",
            generated.read_text(encoding="utf-8"),
        )

    def test_frozen_importer_rejects_tampered_config_before_torch(self) -> None:
        config = copy.deepcopy(EXPECTED_CONFIG)
        config["hidden_size"] += 1
        with tempfile.TemporaryDirectory() as directory:
            config_path = Path(directory) / "config.json"
            checkpoint_path = Path(directory) / "checkpoint.bin"
            config_path.write_text(json.dumps(config), encoding="utf-8")
            checkpoint_path.write_bytes(b"not a checkpoint")
            with self.assertRaises(FrozenCheckpointError):
                load_frozen_trace(checkpoint_path, config_path)


if __name__ == "__main__":
    raise SystemExit(unittest.main())
