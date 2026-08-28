# Decoder Transformer Lean

This repository is the Lean translation of the core semantic result from the
Isabelle/HOL development in
[`Arthur742Ramos/isabelle-afp-monorepo`](https://github.com/Arthur742Ramos/isabelle-afp-monorepo/tree/master/projects/decoder-transformer-isabelle).

The first Palomar-sized contribution formalizes the representation-independent
refinement boundary for decoder-only inference:

- `prefixEq` and `causal` express prefix-local sequence semantics;
- `causalAttentionFrom` and `causalAttention` define parametric causal
  attention over an abstract query, key, value, and aggregator interface;
- `KVCache`, `cacheOf`, and `cachedRun` define projected key--value storage;
- `cachedAttention_eq_causalAttention` proves that an empty-cache incremental
  run returns exactly the full-prefix causal result;
- `finalCache_eq_fullProjections` proves the resulting cache contains exactly
  the key and value projections of the processed sequence.

The result is extensional equality over mathematical values.  It does not
claim bit-identical equality for floating-point kernels with different
reduction orders.  Tensor shapes, exact softmax, multi-head blocks, rotary
position embeddings, grouped-query attention, GPT-Neo, generation, and
finite-precision error bounds are planned follow-on modules, not silently
included in this initial statement surface.

## Layout

- `DecoderTransformer/Prefix.lean`: prefix equality, causality, and causal
  composition;
- `DecoderTransformer/Attention.lean`: parametric causal attention and
  future-token independence;
- `DecoderTransformer/Cache.lean`: exact cache semantics and refinement
  proofs;
- `Challenge.lean`: self-contained Palomar statement surface;
- `Solution.lean`: proved declarations imported from the library;
- `comparator.json`: Palomar Comparator configuration;
- `formalization.yaml`: project description, source correspondence, scope,
  and verification metadata.

## Verification

With the pinned Lean toolchain and Mathlib revision:

```sh
lake build
lake env lean Challenge.lean
lake env lean Solution.lean
```

`Challenge.lean` intentionally contains `sorry` placeholders as its
statement-only surface.  The development modules and `Solution.lean` contain
the checked proofs; the final Palomar artifact will be audited with the
Comparator and NanoDa before any external intake is considered.

## Attribution and status

This is a translation and re-expression of the core semantic theorem already
formalized in Isabelle/HOL by Arthur Freitas Ramos.  The Lean files do not
claim an independent mathematical discovery.  No Palomar submission or
registration is performed by this repository preparation step.
