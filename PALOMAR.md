# Palomar preparation

This repository contains the full checked Lean translation of the 34-theory
Isabelle/HOL decoder-transformer development. See `PORT_COVERAGE.md` for
the complete source-to-module map.

The Palomar comparator is deliberately scoped to the representation-
independent semantic kernel:

    DecoderTransformer.causalAttention_is_causal
    DecoderTransformer.cachedAttention_eq_causalAttention
    DecoderTransformer.finalCache_eq_fullProjections

The full library is still imported by `DecoderTransformer.lean` and built by
CI. The challenge surface is self-contained, and its three theorems are now
proved by structural induction rather than placeholders. `Solution.lean`
imports the same kernel-checked development.

The architecture-specific modules cover shaped tensors, exact attention,
multi-head and residual blocks, GPT-Neo full/windowed caches and generation,
modern grouped-query/RoPE/SwiGLU stacks, dyadic refinement, IEEE-facing
certificates, concrete fixtures, and the frozen TinyStories trace.

The source Isabelle theory imports a parameterized AFP IEEE-754 library. The
Lean dependency set does not contain that library, so the IEEE-facing Lean
modules use an explicit abstract format with decoded finite real values and
preserve the source certificate/refinement boundaries without claiming
bit-identical FP16/FP32 execution. This limitation is recorded in the source
comments and `PORT_COVERAGE.md`; it is not hidden by the Palomar metadata.

Source relationship:

<https://github.com/Arthur742Ramos/isabelle-afp-monorepo/tree/b69c6e519c9c810019f3f92e94d6c01e56030947/projects/decoder-transformer-isabelle>

No independent mathematical discovery is claimed. No Palomar intake,
registration, authentication, or external submission is performed by this
repository-preparation step.

## Local checks

    lake build
    lake env lean DecoderTransformer/Examples.lean
    lake env lean Challenge.lean
    lake env lean Solution.lean
    bash scripts/verify-local.sh
    PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh

The macOS Comparator fallback is an explicitly unsandboxed local replay;
Linux CI and Palomar use real Landrun sandboxing. Before any future intake,
record the public repository, full immutable commit SHA, `comparator.json`
path, and the author's authorization relationship for that exact artifact.
