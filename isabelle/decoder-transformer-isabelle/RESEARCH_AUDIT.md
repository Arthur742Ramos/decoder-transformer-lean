# Research and dependency audit

Checked on 2026-08-12.

## Isabelle and AFP

- AFP's `Neural_Networks` entry formalizes feed-forward neural networks,
  alternative representations, matrix-based reasoning, and TensorFlow.js
  import.  It does not advertise masked attention or KV-cache semantics.
- AFP's `Transformer_Semantics` entry concerns predicate transformers for
  program semantics.  Its title is a terminology collision, not a neural
  transformer formalization.
- A current local AFP session query for the requirements of `Neural_Networks`
  did not include `Group-Ring-Module`.  The dependency must be checked again
  against the AFP revision used for any submission.
- No dedicated neural-transformer/attention/KV-cache AFP entry was found in
  the current AFP index and source tree.  This supports an AFP gap claim, not
  an unrestricted claim of worldwide priority.
- AFP's `IEEE_Floating_Point` entry provides an executable bounded-format
  model with normal and subnormal values, signed zeros, infinities, NaNs,
  rounding modes, and fused multiply-add.  Its resolved dependency graph does
  not contain `Group-Ring-Module`, so it is admissible for this project.
- The current AFP source itself marks its `RNE` definition with a caveat for
  some exact halfway cases.  The closest-representable-value bound used here
  is insensitive to which equally close value is selected; no claim is made
  that the upstream ties-to-even preference has been repaired.

## Broader literature

- There is substantial mathematical work on transformer expressiveness and
  verified or proof-generating DSLs.  That literature is related but does not
  by itself establish a proof-assistant refinement theorem for exact KV-cache
  inference.
- Recent numerical work reports systematic divergence between cached and
  cache-free FP16 inference caused by different accumulation orders.  The
  Isabelle theorem is therefore scoped to exact semantics with a shared
  aggregator; floating-point implementations require approximation theorems.

## Primary sources

- A. D. Brucker and A. Stell, “Verifying Feedforward Neural Networks for
  Classification in Isabelle/HOL,” FM 2023; AFP entry `Neural_Networks`, 2025.
- A. Vaswani et al., “Attention Is All You Need,” NeurIPS 2017.
- N. Shazeer, “Fast Transformer Decoding: One Write-Head is All You Need,”
  arXiv:1911.02150, 2019.
- J. Su et al., “RoFormer: Enhanced Transformer with Rotary Position
  Embedding,” Neurocomputing 568, 2024.
- J. Ainslie et al., “GQA: Training Generalized Multi-Query Transformer Models
  from Multi-Head Checkpoints,” EMNLP 2023.
- N. Shazeer, “GLU Variants Improve Transformer,” arXiv:2002.05202, 2020.
- R. Chodavarapu and L. Xu, “The Illusion of Equivalence: Systematic FP16
  Divergence in KV-Cached Autoregressive Inference,” arXiv:2604.15409, 2026.
- L. Yu, “A Formal Model of IEEE Floating Point Arithmetic,” Archive of
  Formal Proofs, 2013, entry `IEEE_Floating_Point`.

The audit should be refreshed before a paper makes novelty or priority claims.

## Current formal boundary

- The exact development now covers shaped real tensors, scaled dot-product
  softmax, multi-head attention, pre-normalized decoder blocks, one key--value
  cache per head and layer, arbitrary-layer incremental refinement, and finite
  autoregressive generation.  It additionally covers valid-model contracts,
  initialized whole-prompt caches, position-aligned RoPE, grouped-query
  attention, SwiGLU, and bounded greedy decoding.  These components are now
  integrated in one modern layer semantics with per-KV-head rotary caches,
  arbitrary compatible layer stacks, initialized prompt evaluation, and
  finite end-to-end generation refinement.
- `GPT_Neo_Components.thy` now formalizes the architecture family represented
  by the pinned public trace independently of the rotary/RMSNorm/SwiGLU path:
  learned token-plus-position embeddings, affine LayerNorm, GELU-New,
  learned-window causal attention, biased ordinary multi-head projections, the
  pre-LayerNorm residual block, vocabulary-logit shape, and causal full layer
  shape preservation.  This is the semantic target for future full checkpoint
  integration; it is not itself a claim that the public weights have already
  been instantiated in Isabelle.
- `GPT_Neo_Incremental.thy` closes the exact GPT-Neo cache boundary:
  LayerNorm-normalized prefix representations remain as a semantic bridge,
  while the implementation-level cache stores one projected key--value history
  per head.  Global or sliding-window attention is proved equal to full-prefix
  attention, and the projected cached pre-LayerNorm block step equals the
  newest full-layer result while preserving the cache relation.
- `GPT_Neo_Stack.thy` and `GPT_Neo_Model.thy` lift that result through
  arbitrary compatible GPT-Neo stacks, learned token/position embeddings,
  final LayerNorm, vocabulary logits, prompt caches, and next-token
  evaluation.
- `GPT_Neo_Windowed_Cache.thy` proves the storage refinement previously
  identified as open: positive-window trimming of projected keys and values is
  append-stable and idempotent, and bounded attention/block steps preserve the
  full-prefix semantics without reprojecting old cache entries.
- `GPT_Neo_Windowed_Stack.thy` composes the projected bounded cache relation
  through every GPT-Neo layer and repeated prompt execution.  The bounded
  model and generation interfaces then prove vocabulary-safe finite greedy
  transitions.
- `GPT_Neo_Generation.thy` additionally defines full-prefix greedy generation
  and proves equality with the n-step bounded cached generator under the
  explicit context-budget invariant.
- `Modern_Generation.thy` now states the corresponding unrestricted
  arbitrary-n theorem `modern_greedy_generate_steps_eq_full`: from any valid
  modern generation state, cached first-argmax generation produces exactly the
  same token history as repeated full-prefix evaluation.
- `GPT_Neo_Tiny_Checkpoint.thy` is a concrete one-layer, non-trained fixture
  exercising model validity, bounded prompt initialization, and a bounded
  generation step.
- The numerical development begins with an error-relation interface.  It
  proves the compositional logit bound
  `L * hidden_error + rounding_error` and derives `L` from
  vocabulary-matrix column norms.  A concrete nearest-dyadic FMA vocabulary
  projection now discharges the local-rounding obligation with accumulated
  coordinate error `model_dim / 2^(p+1)`; at 23 fractional bits the term is
  `model_dim / 16777216`.
- This dyadic kernel has unbounded integer range and omits IEEE-754 bounded
  exponents, subnormals, infinities, NaNs, signed zeros, overflow, and
  round-to-nearest-ties-to-even.  It is not a concrete FP16 or complete
  binary32 certificate.  The hidden-state relation and hardware-format
  semantics remain checkpoint/backend obligations.
- The new IEEE layer closes that representation gap for vocabulary projection:
  it invokes the AFP model's actual bounded-format `fmul_add RNE`, proves the
  result finite under a strict format-threshold premise, and bounds a dot
  product by one supplied nearest-value budget per FMA step.  Matrix lifting
  gives `model_dim * epsilon` per logit, and composition with the column-norm
  stability theorem gives `L * hidden_error + model_dim * epsilon`.  A direct
  binary32 corollary and a cached-modern-stack corollary are checked.
- The existential per-step obligations also have a data-bearing form.  A dot
  certificate records one finite same-format nearest-value witness per actual
  accumulator step; a projection certificate supplies one such trace per
  output column.  Isabelle proves that replaying this explicit certificate
  establishes the safety predicate and the projection error theorem.
- This is a conditional backend certificate, not yet a checkpoint theorem:
  concrete weights and activations must supply the finite hidden-state
  relation and each accumulator's range/representability witness.  The exact
  upstream halfway preference caveat also prevents describing the imported
  `RNE` definition as a fully repaired ties-to-even implementation.
- A concrete checkpoint milestone is now present independently of the IEEE
  backend.  The checked two-token, two-dimensional, one-layer modern decoder
  has explicit embeddings and matrices, a proved-valid parameter record,
  exact full/cached prompt execution, concrete logits, a uniform generation
  distribution, and the arbitrary finite trace `tokens @ replicate n 0`.
  In addition, `tools/import_decoder_checkpoint.py` validates a deterministic
  JSON schema and generates a second, nonzero Isabelle instantiation whose
  record and stack validity plus cached/full prompt and next-token refinement
  are kernel-checked.  That fixture is synthetic and carries no trained-model
  provenance; importing and certifying a genuinely trained external checkpoint
  remains a separate scaling task.
- The importer frontier now includes checkpoints/two_layer_gqa_rope_swiglu.json
  and tools/import_multilayer_checkpoint.py.  Isabelle checks two generated
  modern records with two query heads sharing one key--value head, explicit
  nonzero RoPE angles, nonzero SwiGLU projections, the non-degenerate
  four-query/two-KV contiguous routing pattern, recursive stack validity,
  prompt cache refinement, next-token refinement, and initialized generation
  state.  This remains a deterministic synthetic integration fixture rather
  than a trained-checkpoint claim.
- Concrete_IEEE_Certificate.thy supplies a separate transparent binary32
  witness fixture: a one-hot four-dimensional vocabulary head, finite
  same-format witnesses for every recursive FMA step, a checked projection
  certificate, and its derived 4 * epsilon bound at epsilon = 1.  This is
  now a genuine replayable IEEE certificate, but it is deliberately not being
  presented as a full internal two-layer checkpoint arithmetic certificate.
- The public-checkpoint frontier is now exercised by
  `tools/import_frozen_checkpoint.py` against the immutable
  `roneneldan/TinyStories-1M` GPT-Neo revision
  `77f1b168e219585646439073245fe87e56b3023e`.  The importer records the
  config SHA-256
  `ff74c30d5ebb5ab1da0f2ea479adf7197c504b42b5522a858c334ab91ed4958c` and
  checkpoint SHA-256
  `07f9609ea882b8163ff3b23d40e2b82cb715d409631beb15c84b164f3877dae7` and
  emits exact IEEE binary32 bit triples.  `Frozen_TinyStories_Trace.thy`
  replays the token `The` at position zero through four selected layer-zero
  Q/K/V/MLP rows, proving finite operands, a strict threshold margin, one
  witness for every 64 FMA steps, safety, and an error bound of at most 64.
  This is deliberately a selected linear activation slice: it is not a claim
  of full GPT-Neo attention, GELU, softmax, every layer, or end-to-end logits.
- `tools/test_importers.py` provides six dependency-light regression tests for
  renderer reproducibility, malformed synthetic fixtures, GQA divisibility,
  frozen-trace regeneration, and provenance tampering.  The frozen importer
  defers its optional PyTorch dependency until an actual checkpoint load.
- Accordingly, exact cached/full equality and floating implementation error
  bounds are distinct claims throughout the source and document.

## Trusted boundary and numerical scope

The exact cache and generation results are kernel-checked Isabelle/HOL
theorems over mathematical real vectors and matrices.  They establish semantic
full-prefix/cached equality, not bit-identical execution by arbitrary CPU,
CUDA, or PyTorch kernels.

Checkpoint extraction is an external reproducibility boundary:
`tools/import_frozen_checkpoint.py` validates the pinned configuration and
checkpoint SHA-256 digests, tensor shapes, binary32 dtype, finite-value
preconditions, and emits exact sign/exponent/fraction triples.  Isabelle checks
the generated data-bearing theory and its certificate; the importer and hash
comparison are not themselves Isabelle theorems.

The TinyStories theorem is explicitly a replayable local FMA certificate
demonstration.  Its `64` envelope is the worst-case sum of one unit budget
for each of 64 certified steps, not an observed numerical-accuracy estimate.
The result remains limited to four selected layer-zero Q/K/V/MLP rows, not full
attention, GELU, softmax, all eight layers, or end-to-end logits.
