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
Lean dependency set does not import that external AFP session, so the IEEE
modules provide a self-contained field-level model: explicit formats and
bitfields, normal/subnormal decoding, special-value classification, source-
compatible FMA branches, and a closest-finite-value rounding theorem. The
source leaves exact halfway-tie preference explicit, and the Lean model keeps
that boundary. This is a kernel-checked semantic model of the source
certificate boundary, not a claim of hardware bit-identical FP16/FP32
execution. The scope is recorded in the source comments and
`PORT_COVERAGE.md`; it is not hidden by the Palomar metadata.

Source artifact:

`isabelle/decoder-transformer-isabelle/` contains the public source-only
snapshot of the Isabelle/HOL development.  Its pinned source revision and
the document-attribution update are recorded in
`isabelle/SOURCE_PROVENANCE.md`; the Lean metadata points to this directory,
so the source relationship is inspectable without access to another repo.

No independent mathematical discovery is claimed. This preparation snapshot
makes no claim of successful Palomar intake, review, or registration. Those are
external steps tied to the exact submitted commit and the author's explicit
authorization.

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
