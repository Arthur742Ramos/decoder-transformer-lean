# Palomar preparation

This repository contains a focused Lean translation of the generic semantic
kernel from the Isabelle/HOL decoder-transformer development.  The compared
results are:

```text
DecoderTransformer.causalAttention_is_causal
DecoderTransformer.cachedAttention_eq_causalAttention
DecoderTransformer.finalCache_eq_fullProjections
```

In words, parametric causal attention is prefix-local, and an incremental
run that appends projected keys and values to an exact cache returns the same
sequence as full-prefix evaluation.  The final cache is exactly the pair of
projected input histories.  The theorem is extensional over mathematical
values; it does not make a hardware floating-point or reduction-order claim.

`Challenge.lean` is self-contained and statement-only.  `Solution.lean`
imports the proved modules under `DecoderTransformer/`.  `comparator.json`
selects the three theorem declarations and the definitions occurring in their
statement surface.  The challenge intentionally contains `sorry` placeholders
that Comparator replaces with the proved solution; the substantive library and
solution contain no proof holes.

The source relationship is a translation of the core results in the pinned
Isabelle/HOL project:

<https://github.com/Arthur742Ramos/isabelle-afp-monorepo/tree/b69c6e519c9c810019f3f92e94d6c01e56030947/projects/decoder-transformer-isabelle>

No claim of independent mathematical discovery is made.  The architecture-
specific tensor, GPT-Neo, rotary, grouped-query, generation, and numerical
theories remain explicitly outside this first Palomar entry.

## Local checks

```sh
bash scripts/verify-palomar.sh
bash scripts/verify-local.sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
git status --short
git rev-parse HEAD
```

The macOS Comparator fallback is an explicit unsandboxed local replay; Linux
CI and Palomar use real Landrun sandboxing.  The local checks do not submit,
authenticate, register, or create a Palomar entry.  Before intake, record the
public repository, full immutable commit SHA, `comparator.json` path, and the
author's authorization relationship for that exact artifact.
