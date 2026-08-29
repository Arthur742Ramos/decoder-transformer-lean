# Verified Decoder-Transformer Inference Semantics

This project develops exact, parametric Isabelle/HOL semantics for
decoder-only transformer inference.  Its central target is a refinement
theorem showing that incremental key--value-cache evaluation returns the same
mathematical result as full causal evaluation.

Authors: Arthur Freitas Ramos (maintainer), David Barros Hulak, and Ruy J. G.
B. de Queiroz.

## Verified milestones

The semantic kernel deliberately abstracts from tensors and scalar arithmetic:

- `Prefix_Sequences.thy` defines prefix causality and proves that causal
  blocks compose.
- `Causal_Attention.thy` defines attention over the current prefix and proves
  future-token independence.
- `KV_Cache.thy` defines cache validity, incremental evaluation, and the
  full/cached refinement theorem.
- `Shaped_Tensors.thy` supplies dimension-explicit list representations,
  shape-preserving linear operations, and inverse head splitting/concatenation.
- `Exact_Attention.thy` instantiates the kernel with exact real scaled
  dot-product softmax attention, proves positive normalized weights, preserves
  output shapes, and specializes the full/cached equality theorem.
- `Multi_Head_Attention.thy` defines shape-checked per-head projections,
  concatenation, and output projection, then proves model-dimension
  preservation and causal independence.
- `Decoder_Block.thy` adds exact RMSNorm, a parametric pointwise MLP,
  shape-preserving residual sublayers, and a pre-normalized decoder block whose
  shape preservation and causality are proved compositionally.
- `Incremental_Decoder.thy` maintains one key--value cache per head and layer,
  proves the invariant against each layer's normalized prefix, and proves that
  an incremental stack step equals the newest full-stack output.
- `Autoregressive_Generation.thy` adds vocabulary softmax, deterministic and
  sampling semantics, and preserves the cache invariant across any finite
  number of generation steps.
- `Numerical_Refinement.thy` defines the floating-implementation interface and
  proves the compositional logit bound `L * hidden_error + rounding_error`.
- `Model_Validity.thy` collects global nondegeneracy and parameter-shape
  obligations, proves RMS denominators and attention scales positive, and
  lifts shape preservation through arbitrary valid stacks.
- `Prompt_Cache.thy` constructs empty per-head/per-layer caches, proves an
  entire cached prompt run equal to full-stack evaluation, and derives a
  correct initialized generation state.
- `Projection_Stability.thy` derives an explicit vocabulary-projection
  Lipschitz constant from maximum column L1 norms and instantiates the abstract
  end-to-end logit bound.
- `Rotary_Position_Embedding.thy` defines pairwise RoPE with a parametric angle
  schedule, proves dimension and squared-norm preservation, and verifies both
  cached/full equality and absolute cache-position alignment.
- `Modern_Decoder_Components.thy` adds causal, shape-safe grouped-query
  attention and a shape-safe SwiGLU feed-forward operator.
- `Decoding_Policies.thy` proves greedy first-argmax selection is vocabulary
  bounded and develops normalized, positive temperature distributions.
- `Modern_Incremental_Decoder.thy` unifies RMSNorm, pairwise RoPE,
  grouped-query attention, SwiGLU, residuals, and compatible dimensions in one
  decoder-layer record.  It proves exact single-layer and arbitrary-stack
  refinement for position-aware grouped key--value caches, including complete
  prompt execution from canonical empty caches.
- `Modern_Generation.thy` carries the unified-stack refinement through
  initialized next-token evaluation and arbitrary finite autoregressive runs,
  preserving both every modern cache invariant and vocabulary safety.  It also
  defines full-prefix first-argmax generation and proves the explicit
  arbitrary-`n` equality `modern_greedy_generate_steps_eq_full`.
- `GPT_Neo_Components.thy` keeps the pinned public-checkpoint architecture
  separate from the modern rotary path: it formalizes affine projections,
  learned token-plus-position embeddings, mean/variance LayerNorm, GELU-New,
  global or sliding-window causal attention, biased ordinary multi-head
  attention, the pre-LayerNorm residual block, vocabulary logits, and causal
  full-layer shape preservation.
- `GPT_Neo_Incremental.thy` proves the corresponding exact refinement.  It
  retains the normalized-prefix construction as a semantic bridge and also
  defines a genuine per-head projected key--value cache whose old projections
  are reused rather than recomputed.
- `GPT_Neo_Stack.thy` lifts the GPT-Neo block and cache invariant through an
  arbitrary compatible layer stack, including whole-prompt ingestion and
  repeated cached runs.
- `GPT_Neo_Windowed_Cache.thy` proves the positive-window storage refinement
  for that projected cache: trimming after every append is idempotent, the
  bounded cache equals the full-prefix attention context, and bounded
  attention/block steps refine the full GPT-Neo semantics.
- `GPT_Neo_Windowed_Stack.thy` composes that bounded storage invariant through
  every layer and every prompt token.
- `GPT_Neo_Model.thy` adds learned token and position embeddings, final
  LayerNorm, vocabulary logits, full-history and bounded prompt caches, and
  next-token logit refinement for both cache representations.
- `GPT_Neo_Generation.thy` proves vocabulary-safe finite greedy generation for
  both transitions and gives an explicit n-step theorem equating bounded
  cached token histories with full-prefix greedy generation.
- `GPT_Neo_Tiny_Checkpoint.thy` is a concrete non-trained one-layer GPT-Neo
  fixture that proves model validity, bounded prompt initialization, and a
  bounded one-step generation invariant.
- `Dyadic_Finite_Precision.thy` defines a concrete nearest-dyadic rounding
  grid and fused multiply-add dot product, proves the accumulated error
  `min(length xs, length ws) / 2^(p+1)`, lifts it to vocabulary projection,
  and derives the end-to-end logit bound
  `L * hidden_error + model_dim / 2^(p+1)`.  Its 23-fraction-bit corollary has
  the closed projection term `model_dim / 16777216`; a dedicated theorem
  connects the exact cached/full modern-stack equality directly to these
  certified dyadic logits.
- `IEEE_754_Projection.thy` connects the real-valued decoder semantics to the
  AFP `IEEE_Floating_Point` model.  It proves finiteness and nearest-value
  error for actual bounded-format `fmul_add RNE`, accumulates the certified
  error through dot products and vocabulary projection, derives the bound
  `L * hidden_error + model_dim * epsilon`, and provides explicit binary32
  and cached-modern-stack specializations.  It also defines replayable witness
  traces: one finite same-format witness per FMA step and one trace per output
  column, with a theorem reducing certificate validation to the same bound.
- `Tiny_Decoder_Checkpoint.thy` supplies a complete two-token,
  two-dimensional, one-layer checkpoint.  Isabelle proves its parameter
  record valid, its residual layer and full stack exactly identity, cached
  prompt execution equal to full execution with a matching final cache,
  identity-head logits, and the closed greedy trace
  `tokens @ replicate n 0` for its uniform generation head.  The concrete
  three-step instance evaluates to `[1, 0, 0, 0]`.
- `checkpoints/nonzero_tiny_decoder.json` and
  `tools/import_decoder_checkpoint.py` provide a deterministic, shape-checked
  checkpoint interchange path.  The generated
  `Imported_Decoder_Checkpoint.thy` instantiates every modern-layer weight
  with nonzero values, proves the imported record and stack valid, and reuses
  the exact cached/full prompt and next-token refinement theorems.  This is a
  synthetic fixture for importer and proof integration, not a claim of trained
  model provenance.

- checkpoints/two_layer_gqa_rope_swiglu.json and
  tools/import_multilayer_checkpoint.py extend that path to a deterministic
  two-layer fixture with two query heads sharing one key--value head, explicit
  nonzero RoPE angles, and nonzero SwiGLU matrices.  Isabelle checks both
  generated layer records, the stack validity predicate, GQA grouping, prompt
  cache refinement, next-token refinement, and initialized generation state.
  This fixture is synthetic and is not a trained checkpoint.
- Concrete_IEEE_Certificate.thy is a replayable binary32 projection
  certificate.  It fixes a transparent one-hot head and finite same-format
  FMA witnesses, proves the certificate predicate, and derives the concrete
  dimension-explicit 4 * epsilon projection bound with epsilon = 1.
- `tools/import_frozen_checkpoint.py` imports a pinned public
  `roneneldan/TinyStories-1M` GPT-Neo checkpoint (revision
  `77f1b168e219585646439073245fe87e56b3023e`) into exact binary32 bit fields.
  `Frozen_TinyStories_Trace.thy` replays the token-`The`, position-zero
  activation through four selected layer-zero Q/K/V/MLP projection rows, with
  all 64 FMA steps per row covered by finite witnesses, the strict threshold
  premise, and the conservative error envelope `<= 64`.  This number is
  explicitly a replayable local FMA certificate demonstration: it is not a
  numerical-accuracy estimate, because it sums one unit budget for each of the
  64 certified steps.  The JSON records both source hashes:
  config `ff74c30d5ebb5ab1da0f2ea479adf7197c504b42b5522a858c334ab91ed4958c`
  and checkpoint
  `07f9609ea882b8163ff3b23d40e2b82cb715d409631beb15c84b164f3877dae7`.
  This is a genuine frozen checkpoint slice, not a full GPT-Neo
  attention/GELU/softmax or all-layer certificate.

- `tools/test_importers.py` runs six standard-library regression tests for
  deterministic theory regeneration, malformed shapes, GQA divisibility, the
  frozen trace renderer, and tampered provenance metadata.  PyTorch is loaded
  lazily by the frozen importer, so these reproducibility checks do not require
  the optional checkpoint-loading dependency.

The theorem is parametric in query, key, and value projections and in the
attention aggregator.  Every Blueprint target is mapped to a kernel-checked
fact, including the architecture-specific GPT-Neo layer and the public
frozen-checkpoint trace with its replayable certificate.

## Trusted boundary and numerical scope

The exact cache and generation theorems are kernel-checked Isabelle/HOL
results over mathematical real vectors and matrices.  They prove semantic
full-prefix/cached equality; they do not claim bit-identical execution by
arbitrary CPU, CUDA, or PyTorch kernels.

Checkpoint extraction is an external reproducibility boundary:
`tools/import_frozen_checkpoint.py` validates the pinned config and checkpoint
hashes, tensor shapes, binary32 dtype, finite-value preconditions, and emits
exact sign/exponent/fraction triples.  Isabelle checks the generated
data-bearing theory and its certificate, but the importer and hash comparison
are not themselves Isabelle theorems.

The IEEE results use the AFP bounded-format `fmul_add RNE` model and explicit
finite, range, and nearest-value witnesses.  They are conditional certificate
theorems rather than hardware-conformance claims.  The TinyStories result
stops at four selected layer-zero linear rows, so it does not certify full
attention, GELU, softmax, all eight layers, or end-to-end logits.

## Scope boundary

`cached_attention_eq_full_attention` is an equality in exact extensional
semantics: both paths call the same projections and aggregator on the same
ordered lists.  It is not a claim that two optimized FP16 kernels with
different reduction orders are bit-identical.  Floating-point execution is a
separate refinement problem requiring explicit error bounds.

The projection theory discharges the Lipschitz obligation concretely from
column L1 norms.  The dyadic theory supplies a simple fixed-fraction FMA
kernel, while the IEEE theory uses the published bounded-format model with
subnormals, infinities, NaNs, signed zeros, overflow thresholds, and fused
multiply-add.  Its theorem assumes a checkable no-overflow threshold and a
same-format finite witness within `epsilon` at every accumulation step; under
those obligations, the actual AFP `fmul_add RNE` result is finite and within
the accumulated error budget.  The AFP source documents an unresolved caveat
in the exact halfway preference of its `RNE` definition.  Our metric
nearest-value proof is independent of that preference and does not claim to
repair it.  Model-specific work must still establish the hidden-state relation
and the per-step range/witness certificate.

The modern-stack equality is likewise an exact-real refinement theorem.  Its
RoPE schedule is parametric and its GQA grouping uses the proved contiguous
group map
`query_head div (query_heads div kv_heads)` under the divisibility premise.
Model-specific checkpoints must instantiate the parameter record and verify
its shape predicate and head-layout convention.
`Tiny_Decoder_Checkpoint` and the generated fixtures demonstrate the
instantiation and importer paths end to end.  The pinned TinyStories import
now demonstrates exact bit-field extraction and complete replay for a real
  public checkpoint slice.  `GPT_Neo_Components` and the GPT-Neo model
  theories provide the architecture-faithful exact-real target plus a concrete
  synthetic fixture.  The checked-in public artifact still stops at four
  selected layer-zero linear rows; full trained-checkpoint
  attention/GELU/softmax execution and all-layer arithmetic certification
  remain separate scaling tasks.

## Dependency policy

The semantic tensor foundation depends only on Isabelle/HOL.  The concrete
IEEE refinement additionally imports the published AFP session
`IEEE_Floating_Point` (and its `Word_Lib` dependency).  The resolved session
graph has been checked and does not contain the prohibited
`Group-Ring-Module` session.

The build uses the Isabelle2025-2-compatible AFP releases dated 6 February
2026.  The exact archive URLs, SHA-256 hashes, expected directory layout, and
Windows bootstrap commands are recorded in `DEPENDENCIES.md`.  No developer
machine path is part of the checked-in configuration.

## Build

After extracting the pinned AFP bundle described in `DEPENDENCIES.md`, build
the project from its directory (or from the containing Isabelle/AFP monorepo):

```powershell
$env:DECODER_TRANSFORMER_AFP_ROOT = "C:\path\to\decoder-transformer-afp"
Set-Location (Resolve-Path .).Path
isabelle build -D . `
  -d "$env:DECODER_TRANSFORMER_AFP_ROOT\Word_Lib" `
  -d "$env:DECODER_TRANSFORMER_AFP_ROOT\IEEE_Floating_Point" `
  Decoder_Transformer
```

When this directory is placed in the original Isabelle/AFP monorepo, the
project-local convenience wrapper performs the same dependency checks:

```powershell
cd projects\decoder-transformer-isabelle
.\tools\build.ps1 -NoDocument
.\tools\build.ps1
```

The importer regression suite is independent of Isabelle and PyTorch:

```powershell
py -3 tools\test_importers.py
```

Run `isabelle-blueprint check .` from the project directory to reconcile the
dependency plan with the checked theory facts after configuring the local AFP
root in `isabelle-blueprint.toml`.
