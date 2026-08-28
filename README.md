# Decoder Transformer Lean

This repository is the checked Lean 4 counterpart of the complete
decoder-transformer Isabelle/HOL development at
[isabelle-afp-monorepo/projects/decoder-transformer-isabelle](https://github.com/Arthur742Ramos/isabelle-afp-monorepo/tree/b69c6e519c9c810019f3f92e94d6c01e56030947/projects/decoder-transformer-isabelle).

The source contains 34 Isabelle theories and 15,676 lines. Every source
theory has a corresponding Lean module; the source-to-module map is in
[PORT_COVERAGE.md](PORT_COVERAGE.md). The public library aggregator
[DecoderTransformer.lean](DecoderTransformer.lean) imports the complete
dependency graph.

The port covers:

- prefix-local operators and exact causal attention/cache refinement;
- shaped vectors, matrices, tensors, exact softmax attention, multi-head
  attention, normalization, residual decoder blocks, and incremental caches;
- autoregressive generation, numerical error bounds, projection stability,
  prompt initialization, and vocabulary-safe decoding;
- GPT-Neo learned-position components, full and sliding-window caches,
  stacks, model evaluation, and generation;
- grouped-query attention, rotary position embeddings, SwiGLU, modern
  incremental stacks, and greedy generation;
- dyadic finite-precision refinement, IEEE-facing projection certificates,
  concrete certificate fixtures, Tiny decoder/GQA fixtures, and the frozen
  TinyStories trace payload.

The frozen TinyStories module preserves all 448 sign/exponent/mantissa
triples from the source checkpoint trace, with decoded values, finite and
smallness proofs, four dot-product certificates, and the trace safety/error
theorems.

## IEEE backend boundary

The Isabelle source imports a parameterized AFP bit-level IEEE-754 library.
The pinned Lean dependency set does not provide that library. The Lean port
therefore exposes an explicit abstract IEEE format and decoded finite value,
proves the same certificate/refinement interfaces, and makes no claim of
bit-identical FP16/FP32 execution. The dyadic module provides an executable
finite-grid error model; replacing the abstract IEEE backend with a bit-level
implementation is a separate backend task, not an unrecorded assumption.

## Palomar surface

The Palomar comparator remains intentionally focused on the three core
semantic theorems:

    DecoderTransformer.causalAttention_is_causal
    DecoderTransformer.cachedAttention_eq_causalAttention
    DecoderTransformer.finalCache_eq_fullProjections

The full port is included in the repository and built by CI; the comparator
challenge is a self-contained independent statement surface for that core
boundary. `Challenge.lean` and `Solution.lean` contain no proof holes or
extra axioms beyond the permitted logical axioms.

No Palomar intake, registration, or external submission is performed by this
repository preparation.

## Verification

With the pinned Lean toolchain and Mathlib revision:

    lake build
    lake env lean DecoderTransformer/Examples.lean
    lake env lean Challenge.lean
    lake env lean Solution.lean
    bash scripts/verify-local.sh

The source attribution and exact checkpoint provenance are retained in the
module comments, `formalization.yaml`, `PALOMAR.md`, and
`PORT_COVERAGE.md`.
