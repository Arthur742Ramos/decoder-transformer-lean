# Decoder Transformer Lean

This repository contains a checked Lean 4 and Mathlib formalization of
decoder-transformer semantics and refinement. The public library aggregator
[`DecoderTransformer.lean`](DecoderTransformer.lean) imports the complete
dependency graph.

The development covers:

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
triples from the checkpoint trace, with decoded values, finite and smallness
proofs, four dot-product certificates, and the trace safety/error theorems.

## Authors

Arthur Freitas Ramos (maintainer), David Barros Hulak, and Ruy J. G. B. de
Queiroz.

## Semantic contract

The Palomar Challenge surface is concrete and auditable. Vectors, matrices,
and rank-three tensors are finite lists with explicit shape predicates.
`validModernStack` requires every layer to have positive dimensions, valid
head divisibility, positive normalization epsilon, correctly shaped gains and
weights, and shape-preserving rotary embeddings. `modernStackCompatible`
additionally requires every layer to use the declared common model dimension.
The advertised predicate `palomarModernStackWellFormed` requires a nonempty
stack together with both conditions.

`modernTransformerCacheMatches` recursively requires each cache to be exactly
the projected key/value history of the transformed prefix for its layer;
the prefix supplied to the next layer is the preceding layer's full output.
`fullModernDecoderStack` evaluates causal grouped-query attention, rotary
queries/keys, residual connections, and SwiGLU over the whole prefix.
`cachedModernDecoderStackStep` appends the current projected key/value to each
cache and applies the same layer computation to the current token.

`modernGenerationCacheMatches` requires a nonempty token history and the exact
cache relation. The generation theorem is stated only with
`0 < vocabularySize`. The totalized implementation still defines
`firstArgmax [] = 0`, but that empty-vocabulary default is outside the
advertised generation claim. Similarly, all list operations remain total for
dimension-incompatible inputs, while the advertised refinement claims are
restricted to `palomarModernStackWellFormed` stacks.

`matrixShape modelDim vocabularySize W` states the exact projection shape.
`vectorErrorBound` means equal output lengths and a coordinatewise absolute
error at most its epsilon. `dyadicUnitRoundoff p` is
`(2 * 2^p)⁻¹`; `dyadicNextTokenLogits` is the vocabulary projection computed
with nearest-grid fused multiply-add steps. The dyadic theorem also requires
positive vocabulary and the stated matrix shape.

## IEEE backend boundary

The IEEE-facing modules contain a self-contained field-level model with
explicit formats and bitfields. `ieeeVal` implements normal and subnormal
decoding; the model classifies zeros, finite values, infinities, and NaNs;
and the FMA layer preserves the corresponding special-value cases. Its finite
rounding path selects a closest representable finite value and proves the
corresponding metric error property. This is a kernel-checked semantic model,
not a claim that Lean executes hardware FP16/FP32 operations bit-for-bit. The
dyadic module remains an executable finite-grid error model.

## Palomar surface

The comparator selects these three strengthened theorem wrappers:

    DecoderTransformer.palomarIncrementalModernDecoderRefinesFull
    DecoderTransformer.palomarModernGreedyGenerateStepsRefinesFull
    DecoderTransformer.palomarCachedModernDyadicNextTokenLogitError

Together they state cached/full refinement for a well-formed modern stack,
its composition across positive-vocabulary greedy generation steps, and the
corresponding positive-vocabulary dyadic next-token logit error bound.
`Challenge.lean` contains the independent concrete contract and theorem
declarations; `Solution.lean` imports the kernel-checked wrappers. The exact
interfaces and permitted axiom set are recorded in `comparator.json`.

This repository makes no claim of successful Palomar intake, review, or
registration. Those are external steps tied to the exact submitted commit.

## Verification

With the pinned Lean toolchain and Mathlib revision:

    lake build
    lake env lean DecoderTransformer/Examples.lean
    lake env lean Challenge.lean
    lake env lean Solution.lean
    bash scripts/verify-local.sh
    PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
