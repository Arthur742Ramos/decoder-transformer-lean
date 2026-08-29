# Decoder Transformer Lean

This repository is the checked Lean 4 counterpart of the complete
decoder-transformer Isabelle/HOL development.  The source formalization is
included as a public, source-only artifact at
[`isabelle/decoder-transformer-isabelle`](isabelle/decoder-transformer-isabelle).

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

## Authors

Arthur Freitas Ramos (maintainer), David Barros Hulak, and Ruy J. G. B. de
Queiroz.

## Isabelle source artifact

The directory
[`isabelle/decoder-transformer-isabelle`](isabelle/decoder-transformer-isabelle)
contains the 34 Isabelle theories, ROOT session description, documentation,
checkpoint data, and source tooling used by the translation.  It is vendored
from source revision `b69c6e519c9c810019f3f92e94d6c01e56030947`; the provenance
and the small public attribution update to the document metadata are recorded
in [`isabelle/SOURCE_PROVENANCE.md`](isabelle/SOURCE_PROVENANCE.md).

## IEEE backend boundary

The Isabelle source imports a parameterized AFP bit-level IEEE-754 library.
The pinned Lean dependency set does not import that external AFP session. The
Lean port instead contains a self-contained field-level model with explicit
IEEE formats and bitfields. `ieeeVal` implements the normal and subnormal
decoding formulas, the model classifies zeros, finite values, infinities, and
NaNs, and the FMA layer preserves the source's special-value branches. Its
finite rounding path selects a closest representable finite value and proves
the corresponding metric error property. The source leaves the exact
halfway-tie preference explicit; the Lean model preserves that same boundary.

This is a kernel-checked IEEE semantic model for the source certificate
boundary, not a claim that Lean executes hardware FP16/FP32 operations
bit-for-bit. The dyadic module remains an executable finite-grid error model.

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
