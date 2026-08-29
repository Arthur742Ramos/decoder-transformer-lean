# Palomar preparation

This repository is a checked Lean 4 and Mathlib development of
decoder-transformer semantics, cached evaluation, generation, and numerical
refinement. The complete dependency graph is imported by
`DecoderTransformer.lean`.

The comparator selects these strengthened theorem wrappers:

    DecoderTransformer.palomarIncrementalModernDecoderRefinesFull
    DecoderTransformer.palomarModernGreedyGenerateStepsRefinesFull
    DecoderTransformer.palomarCachedModernDyadicNextTokenLogitError

The first theorem compares one cached modern decoder step with full-prefix
evaluation. The second composes that equality across greedy generation. The
third compares exact and dyadic next-token logits under the explicit model-
dimension error budget.

The contract is intentionally explicit. `validModernStack` checks each
layer's positive dimensions, head divisibility, normalization epsilon, gain
and weight shapes, and rotary shape preservation. `modernStackCompatible`
requires all layers to share the declared model dimension, and
`palomarModernStackWellFormed` additionally requires a nonempty stack.
`modernTransformerCacheMatches` is exact equality with the projected
key/value histories, recursively using each preceding layer's transformed
prefix for the next layer.

`modernGenerationCacheMatches` requires a nonempty token history. The
generation and dyadic-logit wrappers both require `0 < vocabularySize`.
`firstArgmax` remains a total function with the documented convention
`firstArgmax [] = 0`, but the empty-vocabulary case is excluded from those
advertised claims. List operations are likewise total on malformed or
dimension-incompatible inputs; those evaluations are outside the stated
well-formed-stack refinement scope.

The independent `Challenge.lean` module contains concrete definitions for
the compared shapes, semantics, cache relation, generation procedures,
argmax, error relation, and dyadic projection. `Solution.lean` imports the
kernel-checked wrappers, and `comparator.json` records the exact declaration
surface and permitted axioms.

The IEEE-facing modules provide a self-contained field-level model with
explicit formats, bitfields, special-value classification, fused multiply-add
cases, and closest-finite-value rounding. This does not claim hardware
bit-identical FP16/FP32 execution. The dyadic module is an executable
finite-grid error model.

No public registration is claimed. Any Palomar intake or review status is
external and tied to the exact immutable commit submitted.

## Local checks

    lake build
    lake env lean DecoderTransformer/Examples.lean
    lake env lean Challenge.lean
    lake env lean Solution.lean
    bash scripts/verify-local.sh
    PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh

Before an intake, record the public repository, full immutable commit SHA,
`comparator.json` path, and the maintainer authorization relationship for that
exact artifact.
