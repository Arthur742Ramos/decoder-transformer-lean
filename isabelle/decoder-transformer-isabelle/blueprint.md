# Verified decoder-transformer inference semantics

This blueprint targets an AFP entry for exact, parametric semantics of
decoder-only transformers and a refinement proof for incremental KV-cache
inference.  The exact theorem concerns extensional mathematics over a common
arithmetic semantics.  Floating-point kernels with different reduction orders
are a later approximation problem and are not claimed to be equal bit-for-bit.

## Structural sequence semantics

::: definition {#def-prefix-causality}
title: Prefix equality and causal sequence operators
isabelle:
  theory: Prefix_Sequences
  fact: causal_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Two sequences agree through a prefix when their corresponding `take` values
are equal.  A sequence operator is causal when it preserves this relation for
every prefix length.
:::

::: theorem {#thm-causal-composition}
title: Causal blocks compose into a causal decoder stack
uses:
  - def-prefix-causality
isabelle:
  theory: Prefix_Sequences
  fact: causal_apply_blocks
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Any finite stack whose blocks are causal is itself causal.
:::

::: definition {#def-parametric-attention}
title: Parametric masked attention
uses:
  - def-prefix-causality
isabelle:
  theory: Causal_Attention
  fact: causal_attention_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

At each position, attention receives the current query and only the keys and
values projected from the prefix ending at that position.  The aggregator is
parametric in the arithmetic and tensor representation.
:::

::: theorem {#thm-causal-independence}
title: Causal independence from future tokens
uses:
  - def-parametric-attention
isabelle:
  theory: Causal_Attention
  fact: causal_attention_independence
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

If two inputs agree through position `i`, their masked-attention outputs at
`i` are equal, regardless of their later tokens.
:::

## Exact incremental refinement

::: definition {#def-kv-cache}
title: Key--value cache invariant and incremental step
uses:
  - def-parametric-attention
isabelle:
  theory: KV_Cache
  fact: cache_matches_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A valid cache contains exactly the key and value projections of the processed
prefix.  One incremental step appends the new projections and evaluates the
same aggregator on the extended cache.
:::

::: theorem {#thm-cached-attention-refinement}
title: Cached attention equals full prefix attention
uses:
  - def-kv-cache
isabelle:
  theory: KV_Cache
  fact: cached_attention_eq_full_attention
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For every input sequence, query/key/value projections, and aggregator, the
incremental run returns the same output sequence as full causal attention.
Its final cache is exactly the full sequence of key and value projections.
:::

## Exact numeric attention

::: definition {#def-shaped-tensors}
title: Shape-safe vectors, matrices, and sequence tensors
uses:
  - def-parametric-attention
isabelle:
  theory: Shaped_Tensors
  fact: tensor3_shape_split_sequence_heads
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Nested finite lists with explicit predicates provide an AFP-compatible tensor
foundation.  Projection, matrix multiplication, residual addition, head
splitting, and head concatenation preserve their stated shapes; concatenating
a well-shaped split recovers the original sequence.  The foundation uses only
Isabelle/HOL and introduces no AFP dependency.
:::

::: definition {#def-softmax-attention}
title: Scaled dot-product attention and softmax
uses:
  - def-shaped-tensors
isabelle:
  theory: Exact_Attention
  fact: exact_causal_attention_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The parametric aggregator is instantiated with exact real-valued dot products,
square-root scaling, exponentiation, normalization, and weighted value sums.
Its concrete cached evaluator is proved equal to the corresponding full exact
causal attention evaluator.
:::

::: theorem {#thm-attention-normalization}
title: Attention weights form a probability vector
uses:
  - def-softmax-attention
isabelle:
  theory: Exact_Attention
  fact: attention_weights_normalized
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For a nonempty causal prefix, every softmax weight is positive and the weights
sum to one.
:::

::: definition {#def-multi-head-attention}
title: Multi-head causal attention
uses:
  - def-softmax-attention
isabelle:
  theory: Multi_Head_Attention
  fact: multi_head_causal_attention_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Per-head query, key, and value projections feed exact attention.  The head
results are concatenated and mapped through an output projection under an
explicit parameter-shape predicate.  The resulting sequence preserves the
model dimension and remains causal.
:::

## Decoder blocks and generation

::: definition {#def-decoder-block}
title: Normalization, residual, MLP, and decoder block
uses:
  - def-multi-head-attention
isabelle:
  theory: Decoder_Block
  fact: decoder_block_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Exact RMSNorm, a parametric pointwise MLP, and two residual sublayers form a
pre-normalized decoder block.  Explicit parameter hypotheses imply preservation
of sequence length and model dimension.  LayerNorm and SwiGLU remain possible
conservative extensions.
:::

::: theorem {#thm-decoder-causality}
title: Decoder stacks are causal
uses:
  - thm-causal-composition
  - def-decoder-block
isabelle:
  theory: Decoder_Block
  fact: decoder_block_is_causal
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Lift masked-attention causality through normalization, MLP, residuals,
multi-head composition, and an arbitrary finite decoder stack.
:::

::: theorem {#thm-incremental-transformer}
title: Incremental decoder equals full decoder
uses:
  - thm-cached-attention-refinement
  - def-decoder-block
isabelle:
  theory: Incremental_Decoder
  fact: incremental_decoder_equals_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Each layer maintains one key--value cache per head, matched against that
layer's normalized processed prefix.  A cached token step is proved equal to
the last output of full evaluation through an arbitrary layer stack, while
preserving every layer cache invariant.
:::

::: definition {#def-autoregressive-generation}
title: Autoregressive generation and next-token distributions
uses:
  - thm-incremental-transformer
  - thm-attention-normalization
isabelle:
  theory: Autoregressive_Generation
  fact: generate_steps_cache_invariant
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Vocabulary projection and softmax produce positive normalized next-token
weights.  Deterministic selection and discrete sampling support are defined,
and the layer-cache invariant is preserved across any finite number of
generation transitions.
:::

## Numerical refinement

::: definition {#def-floating-semantics}
title: Floating-point implementation relation
uses:
  - thm-incremental-transformer
isabelle:
  theory: Numerical_Refinement
  fact: floating_transformer_relation_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Relate exact hidden vectors to real-valued observations of a floating
implementation by a coordinatewise error budget.  A concrete IEEE-754 backend
must prove this relation and its local rounding obligations; the interface does
not assert literal cached/full equality across different accumulation orders.
:::

::: theorem {#thm-logit-error}
title: End-to-end logit error bound
uses:
  - def-floating-semantics
isabelle:
  theory: Numerical_Refinement
  fact: next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

If the hidden-state relation has error `delta`, the exact vocabulary projection
is `L`-Lipschitz, and the floating projection contributes local rounding error
`rho`, then every output logit differs by at most `L * delta + rho`.  Norm,
range, denominator, and IEEE-rounding analyses belong to a concrete backend's
proof of these interface assumptions.
:::

## Valid models and initialized execution

::: definition {#def-valid-model}
title: Globally valid decoder parameters
uses:
  - def-decoder-block
isabelle:
  theory: Model_Validity
  fact: valid_decoder_layer_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Every layer has positive head, model, head-vector, and hidden dimensions; its
model dimension factors into head count times head dimension; RMS epsilon is
positive; and every parameter tensor has its required shape.
:::

::: theorem {#thm-positive-denominators}
title: RMS and attention denominators are nondegenerate
uses:
  - def-valid-model
isabelle:
  theory: Model_Validity
  fact: valid_layer_rms_denominator_nonzero
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Positive layer epsilon makes the RMS denominator strictly positive for every
vector, including the empty vector; positive head dimension makes the
attention square-root scale strictly positive.
:::

::: theorem {#thm-valid-stack-shape}
title: Valid decoder stacks preserve global tensor shape
uses:
  - def-valid-model
  - def-decoder-block
isabelle:
  theory: Model_Validity
  fact: valid_transformer_preserves_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

An arbitrary nonempty stack of compatible valid layers preserves both the
sequence length and the common model dimension.
:::

::: definition {#def-empty-transformer-cache}
title: Canonical empty per-layer cache
uses:
  - thm-incremental-transformer
isabelle:
  theory: Prompt_Cache
  fact: empty_transformer_cache_matches
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Replicating an empty key--value pair once per head and once per layer satisfies
the recursive transformer cache invariant for the empty prefix.
:::

::: theorem {#thm-prompt-refinement}
title: Initialized cached prompt evaluation equals full evaluation
uses:
  - def-empty-transformer-cache
  - thm-incremental-transformer
isabelle:
  theory: Prompt_Cache
  fact: initialized_cached_run_equals_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Running every prompt vector from the canonical empty cache produces exactly
the full decoder-stack output sequence and finishes with caches matched to the
entire prompt.
:::

::: theorem {#thm-initialized-generation}
title: Prompt initialization yields a correct next-token evaluation
uses:
  - thm-prompt-refinement
  - def-autoregressive-generation
isabelle:
  theory: Prompt_Cache
  fact: initialized_generation_evaluate_correct
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For a nonempty token prompt, consuming all but the final token creates exactly
the cache needed for incremental next-token evaluation, whose distribution is
the full decoder distribution.
:::

## Concrete numerical stability

::: definition {#def-projection-l1-bound}
title: Column L1 stability certificate
uses:
  - def-floating-semantics
isabelle:
  theory: Projection_Stability
  fact: projection_l1_bound_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A projection certificate bounds the L1 norm of every output column by a common
nonnegative constant.
:::

::: theorem {#thm-concrete-logit-error}
title: Column norms instantiate the end-to-end logit bound
uses:
  - def-projection-l1-bound
  - thm-logit-error
isabelle:
  theory: Projection_Stability
  fact: concrete_next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The maximum vocabulary-column L1 norm is a proved Lipschitz constant for
coordinatewise hidden-state error, eliminating that abstract obligation from
the numerical refinement theorem.
:::

::: definition {#def-dyadic-rounding}
title: Concrete nearest-dyadic rounding grid
uses:
  - def-floating-semantics
isabelle:
  theory: Dyadic_Finite_Precision
  fact: dyadic_round_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

At fractional precision `p`, real values are rounded to the nearest multiple
of `2^-p` using Isabelle's integer rounding operation.  The model has an
unbounded integer range and explicitly excludes IEEE exceptional values and
ties-to-even semantics.
:::

::: theorem {#thm-dyadic-fma-error}
title: Dyadic FMA accumulation has a closed error certificate
uses:
  - def-dyadic-rounding
isabelle:
  theory: Dyadic_Finite_Precision
  fact: dyadic_fma_dot_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A dot product evaluated by fused multiply-add with one dyadic rounding per
term differs from the exact dot product by at most
`min(length xs, length ws) / 2^(p+1)`.  The theorem covers unequal input
lengths as well as well-shaped model vectors.
:::

::: theorem {#thm-dyadic-projection-error}
title: Dyadic vocabulary projection discharges the rounding relation
uses:
  - thm-dyadic-fma-error
  - thm-concrete-logit-error
isabelle:
  theory: Dyadic_Finite_Precision
  fact: concrete_dyadic_next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For model dimension `d`, the concrete vocabulary projection contributes at
most `d / 2^(p+1)` coordinatewise error.  Composed with the hidden-state
relation and the proved column-norm Lipschitz constant, the final bound is
`L * hidden_error + d / 2^(p+1)`.
:::

::: theorem {#thm-binary32-fraction-grid}
title: Closed 23-fraction-bit projection bound
uses:
  - thm-dyadic-projection-error
isabelle:
  theory: Dyadic_Finite_Precision
  fact: binary32_fraction_grid_next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Instantiating the grid at 23 fractional bits gives the explicit projection
term `model_dim / 16777216`.  This matches binary32's normal significand
resolution in the unit binade, but is not presented as a complete IEEE-754
binary32 semantics.
:::

::: theorem {#thm-cached-modern-dyadic-logits}
title: Cached modern hidden states feed certified dyadic logits
uses:
  - thm-dyadic-projection-error
  - thm-modern-stack-refinement
isabelle:
  theory: Dyadic_Finite_Precision
  fact: cached_modern_dyadic_next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The exact cached/full modern-stack refinement removes hidden-state error at
the projection boundary.  Applying the concrete dyadic vocabulary kernel to
the cached hidden vector therefore differs from projecting the full modern
hidden vector by at most `model_dim / 2^(p+1)` per logit, with no abstract
local-rounding premise.
:::

::: definition {#def-ieee-fma-safety}
title: Checkable safety contract for bounded IEEE fused multiply-add
uses:
  - def-floating-semantics
isabelle:
  theory: IEEE_754_Projection
  fact: ieee_fma_step_safe_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A certified FMA step has finite operands, a strict no-overflow bound on its
exact fused real value, and a same-format finite witness within the chosen
local error budget.  The definition is polymorphic in exponent and fraction
width and therefore applies directly to binary32 and binary64.
:::

::: theorem {#thm-ieee-fma-step}
title: Actual bounded-format FMA is finite and nearest-value bounded
uses:
  - def-ieee-fma-safety
isabelle:
  theory: IEEE_754_Projection
  fact: ieee_fma_step_safe_guarantees
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Under the safety contract, the value returned by the AFP model's actual
`fmul_add RNE` operation is finite and differs from the exact fused real value
by at most `epsilon`.  The proof uses the model's closest-value theorem and is
independent of its documented unresolved preference between equally close
halfway candidates.
:::

::: theorem {#thm-ieee-fma-dot}
title: Repeated IEEE fused multiply-add has a linear error certificate
uses:
  - thm-ieee-fma-step
isabelle:
  theory: IEEE_754_Projection
  fact: ieee_fma_dot_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

If every recursive accumulator step satisfies the bounded-format safety
contract, the decoded FMA dot product differs from the exact decoded dot
product by at most `min(length xs, length ws) * epsilon`.
:::

::: definition {#def-ieee-witness-certificate}
title: Replayable IEEE FMA witness traces
uses:
  - def-ieee-fma-safety
isabelle:
  theory: IEEE_754_Projection
  fact: ieee_projection_certificate_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A dot certificate contains one finite same-format nearest-value witness for
each recursive fused accumulator step.  A projection certificate contains one
such trace for every output column, with lengths and column indices checked by
the predicate.
:::

::: theorem {#thm-ieee-certificate-replay}
title: Replaying an explicit certificate proves the projection bound
uses:
  - def-ieee-witness-certificate
  - thm-ieee-fma-dot
isabelle:
  theory: IEEE_754_Projection
  fact: ieee_fma_projection_error_from_certificate
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Kernel checking of the certificate matrix implies every existential safety
obligation and yields the same `real model_dim * epsilon` coordinatewise
projection error.  A checkpoint can therefore ship deterministic witness data
rather than an opaque existence proof.
:::

::: theorem {#thm-ieee-projection}
title: Bounded IEEE FMA projection has dimension-explicit error
uses:
  - thm-ieee-fma-dot
  - thm-concrete-logit-error
isabelle:
  theory: IEEE_754_Projection
  fact: ieee_fma_projection_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For a shaped vocabulary matrix and model vector, a safe actual IEEE FMA dot
product in every output column contributes at most
`real model_dim * epsilon` coordinatewise projection error.
:::

::: theorem {#thm-ieee-modern-logit}
title: Cached modern states feed certified bounded IEEE logits
uses:
  - thm-ieee-projection
  - thm-modern-stack-refinement
isabelle:
  theory: IEEE_754_Projection
  fact: cached_modern_ieee_fma_next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The exact cached/full modern-stack equality composes with the concrete IEEE
projection and column-L1 stability result.  With hidden-state error
`hidden_error`, the actual FMA logits are within
`L * hidden_error + real model_dim * epsilon` of the full exact logits.
:::

::: theorem {#thm-binary32-ieee-logit}
title: Actual binary32 projection specialization
uses:
  - thm-ieee-modern-logit
isabelle:
  theory: IEEE_754_Projection
  fact: binary32_fma_next_token_logit_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The projection theorem is specialized to the AFP model's 8-exponent-bit,
23-fraction-bit format.  Unlike the earlier fraction-grid corollary, this
statement uses the bounded binary32 representation and its exceptional-value
and fused-operation semantics; its range and per-step witness premises remain
explicit certificate obligations.
:::

## Position-aware and modern decoder components

::: definition {#def-rope}
title: Pairwise rotary position embedding
uses:
  - def-shaped-tensors
isabelle:
  theory: Rotary_Position_Embedding
  fact: rope_rotate_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Adjacent coordinates are rotated by a position- and pair-dependent angle
schedule; an unmatched final coordinate is preserved.
:::

::: theorem {#thm-rope-isometry}
title: Rotary embeddings preserve shape and squared norm
uses:
  - def-rope
isabelle:
  theory: Rotary_Position_Embedding
  fact: rope_rotate_preserves_squared_norm
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For every angle schedule and position, pairwise rotary embedding preserves the
number of coordinates and their squared Euclidean norm.
:::

::: theorem {#thm-positioned-cache}
title: Cache extension uses the exact next absolute position
uses:
  - def-rope
  - def-kv-cache
isabelle:
  theory: Rotary_Position_Embedding
  fact: positioned_cache_extension
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A cache matched to an indexed prefix extends with the pair whose index is the
start offset plus prefix length, and the resulting cache equals the full
indexed-prefix projections.
:::

::: definition {#def-grouped-query-attention}
title: Grouped-query attention parameterization
uses:
  - def-softmax-attention
isabelle:
  theory: Modern_Decoder_Components
  fact: grouped_query_parameters_shape_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Query heads use distinct query matrices while keys and values are shared by a
positive number of contiguous key--value groups.  Each KV head is repeated for
`query_heads div kv_heads` consecutive query heads, under the divisibility
condition recorded by the validity predicate.
:::

::: theorem {#thm-grouped-query-shape}
title: Grouped-query attention is causal and shape-safe
uses:
  - def-grouped-query-attention
isabelle:
  theory: Modern_Decoder_Components
  fact: grouped_query_causal_attention_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Well-shaped grouped-query projections preserve sequence length and model
dimension; the complete sequence operator is causal.
:::

::: definition {#def-swiglu}
title: SwiGLU gated feed-forward operator
uses:
  - def-decoder-block
isabelle:
  theory: Modern_Decoder_Components
  fact: swiglu_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The SiLU-transformed gate projection is multiplied coordinatewise with a
parallel up projection and returned through the down projection.
:::

::: theorem {#thm-swiglu-shape}
title: SwiGLU preserves the model dimension
uses:
  - def-swiglu
isabelle:
  theory: Modern_Decoder_Components
  fact: swiglu_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Compatible gate, up, and down matrices map every model vector back to the same
model dimension.
:::

::: theorem {#thm-greedy-vocabulary-safety}
title: Greedy decoding remains inside the vocabulary
uses:
  - def-autoregressive-generation
  - def-valid-model
isabelle:
  theory: Decoding_Policies
  fact: greedy_generate_steps_preserves_vocabulary
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

First-maximum selection is in range on every nonempty distribution, so every
finite greedy generation run preserves token vocabulary membership.
:::

::: theorem {#thm-first-argmax-maximal}
title: Greedy selection returns a maximal logit
uses:
  - thm-greedy-vocabulary-safety
isabelle:
  theory: Decoding_Policies
  fact: first_argmax_maximal
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

On every nonempty logit vector, the coordinate selected by first-argmax is at
least as large as every in-range coordinate; ties are resolved toward the
first occurrence.
:::

## Unified modern decoder refinement

::: definition {#def-unified-modern-layer}
title: Unified rotary GQA SwiGLU decoder layer
uses:
  - def-valid-model
  - def-rope
  - def-grouped-query-attention
  - def-swiglu
isabelle:
  theory: Modern_Incremental_Decoder
  fact: valid_modern_decoder_layer_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A single parameter record connects positive model dimensions, divisible query
and key--value head counts, shape-preserving rotary embeddings, RMS gains,
grouped query/key/value projections, output projection, and SwiGLU matrices.
:::

::: theorem {#thm-unified-modern-layer-shape}
title: Unified modern layers preserve sequence shape
uses:
  - def-unified-modern-layer
isabelle:
  theory: Modern_Incremental_Decoder
  fact: valid_full_modern_decoder_layer_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Every valid unified layer preserves sequence length and model dimension under
full position-indexed evaluation.
:::

::: definition {#def-modern-layer-cache}
title: Position-aware grouped rotary layer cache
uses:
  - def-unified-modern-layer
  - def-kv-cache
isabelle:
  theory: Modern_Incremental_Decoder
  fact: modern_layer_cache_matches_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

One cache entry per key--value head stores exactly the rotated key projections
and value projections of the processed layer prefix at their absolute
positions.
:::

::: theorem {#thm-modern-layer-step}
title: Cached unified layer steps equal full layer extension
uses:
  - def-modern-layer-cache
  - thm-positioned-cache
isabelle:
  theory: Modern_Incremental_Decoder
  fact: cached_modern_decoder_layer_step_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Extending every grouped cache at the next absolute position yields the same
attention, residual, SwiGLU, and final hidden vector as full layer evaluation,
while preserving the cache invariant.
:::

::: theorem {#thm-modern-stack-shape}
title: Compatible modern stacks preserve global shape
uses:
  - thm-unified-modern-layer-shape
isabelle:
  theory: Modern_Incremental_Decoder
  fact: compatible_full_modern_decoder_stack_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

An arbitrary list of valid layers sharing one model dimension preserves the
complete input matrix shape.
:::

::: theorem {#thm-modern-stack-refinement}
title: Incremental modern decoder stacks equal full evaluation
uses:
  - thm-modern-layer-step
  - thm-modern-stack-shape
isabelle:
  theory: Modern_Incremental_Decoder
  fact: incremental_modern_decoder_equals_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

At every position, a cached step through an arbitrary valid modern layer stack
returns the last vector of full position-indexed stack evaluation and preserves
each layer's grouped rotary cache invariant.
:::

::: theorem {#thm-modern-prompt-refinement}
title: Empty-cache modern prompt execution equals the full trace
uses:
  - thm-modern-stack-refinement
  - def-empty-transformer-cache
isabelle:
  theory: Modern_Incremental_Decoder
  fact: initialized_modern_cached_run_equals_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Iterating the modern cached stack from canonical empty per-layer caches returns
the entire full prompt output matrix and finishes with caches matched to the
complete prompt.
:::

::: definition {#def-modern-generation-state}
title: Unified modern generation cache invariant
uses:
  - thm-modern-prompt-refinement
  - def-autoregressive-generation
isabelle:
  theory: Modern_Generation
  fact: modern_generation_cache_matches_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A nonempty token history carries a valid modern stack cache matched to the
embedded prefix ending immediately before the current final token.
:::

::: theorem {#thm-modern-next-token-refinement}
title: Cached modern next-token evaluation equals full evaluation
uses:
  - def-modern-generation-state
  - thm-modern-stack-refinement
isabelle:
  theory: Modern_Generation
  fact: cached_modern_next_token_distribution_correct
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The cached modern evaluator returns exactly the vocabulary distribution formed
from the last hidden vector of full modern-stack evaluation and advances every
layer cache to the entire token history.
:::

::: theorem {#thm-modern-generation-invariant}
title: Finite modern generation preserves every cache invariant
uses:
  - thm-modern-next-token-refinement
isabelle:
  theory: Modern_Generation
  fact: modern_generate_steps_cache_invariant
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Any finite number of modern autoregressive transitions preserves the complete
recursive position-aware cache relation.
:::

::: theorem {#thm-modern-generation-safety}
title: Greedy modern generation remains inside the vocabulary
uses:
  - thm-modern-generation-invariant
  - thm-first-argmax-maximal
isabelle:
  theory: Modern_Generation
  fact: greedy_modern_generation_is_safe
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For a positive vocabulary, every finite first-argmax run through the unified
modern cached decoder produces only in-range token identifiers.
:::

::: definition {#def-modern-full-generation}
title: Full-prefix modern greedy generator
uses:
  - def-modern-generation-state
isabelle:
  theory: Modern_Generation
  fact: modern_full_next_token_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The full reference generator appends the first-argmax token obtained from the
last vector of full-prefix modern-stack evaluation.
:::

::: theorem {#thm-modern-generation-transition-full}
title: One cached modern greedy transition equals full-prefix greedy
uses:
  - thm-modern-next-token-refinement
  - def-modern-full-generation
isabelle:
  theory: Modern_Generation
  fact: modern_generation_transition_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Under the modern generation cache invariant, the cached first-argmax transition
appends the same token as the full-prefix reference transition.
:::

::: theorem {#thm-modern-generation-refinement}
title: N-step cached modern greedy generation equals full generation
uses:
  - thm-modern-generation-transition-full
  - thm-modern-generation-invariant
  - def-modern-full-generation
isabelle:
  theory: Modern_Generation
  fact: modern_greedy_generate_steps_eq_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For every finite n and every valid modern generation state, the cached
first-argmax run has exactly the same token history as repeated full-prefix
first-argmax evaluation.  Unlike the GPT-Neo theorem, no absolute-position
budget is needed for this parametric modern path.
:::

## GPT-Neo model, bounded storage, and generation

::: definition {#def-gpt-neo-stack}
title: GPT-Neo compatible layer stack
uses:
  - def-gpt-neo-layer
isabelle:
  theory: GPT_Neo_Stack
  fact: gpt_neo_full_stack_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The GPT-Neo block is composed through an arbitrary finite list of valid,
model-dimension-compatible layers.  The cache relation for a later layer is
indexed by the full output sequence of all preceding layers.
:::

::: definition {#def-gpt-neo-projected-cache}
title: GPT-Neo projected per-head KV cache
uses:
  - def-gpt-neo-layer
isabelle:
  theory: GPT_Neo_Incremental
  fact: gpt_neo_projected_cache_matches_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The implementation-level GPT-Neo cache stores one projected key history and one
projected value history per attention head.  The normalized-input cache is
retained as a semantic bridge, but an old cache entry is not reprojected when a
new token is appended.
:::

::: theorem {#thm-gpt-neo-projected-block}
title: Projected GPT-Neo cache refines a block step
uses:
  - def-gpt-neo-projected-cache
  - thm-gpt-neo-cache-step
isabelle:
  theory: GPT_Neo_Incremental
  fact: gpt_neo_projected_cached_block_step_output
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Querying the current normalized input and reusing the projected per-head
histories returns the newest full GPT-Neo block vector and extends the cache to
the exact projected prefix.

## Proof

Unfold the projected cache extension, apply the generic cache refinement to the
already-projected keys and values, and then use the GPT-Neo block decomposition
to identify the resulting vector with the newest full-layer output.
:::

::: theorem {#thm-gpt-neo-stack-refinement}
title: GPT-Neo cached stacks equal full evaluation
uses:
  - def-gpt-neo-stack
  - thm-gpt-neo-projected-block
isabelle:
  theory: GPT_Neo_Stack
  fact: gpt_neo_cached_stack_step_output
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

An incremental token through every GPT-Neo layer equals the newest full-stack
output and preserves each layer's projected per-head cache invariant.

## Proof

Induct over the layer list.  The head layer uses the projected block
refinement, and the induction hypothesis handles the suffix on the head-layer
output prefix.
:::

::: theorem {#thm-gpt-neo-stack-prompt}
title: Empty-cache GPT-Neo prompt execution equals full evaluation
uses:
  - thm-gpt-neo-stack-refinement
isabelle:
  theory: GPT_Neo_Stack
  fact: initialized_gpt_neo_cached_run_equals_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Iterating from canonical empty layer caches returns the complete full-stack
prompt trace and leaves a matching cache at every layer.

## Proof

Apply the repeated-run refinement to the canonical empty-cache relation and
simplify the empty full-stack output.
:::

::: definition {#def-gpt-neo-model}
title: GPT-Neo model embeddings, normalization, and logits
uses:
  - def-gpt-neo-stack
  - def-gpt-neo-embedding
  - def-gpt-neo-logits
isabelle:
  theory: GPT_Neo_Model
  fact: valid_gpt_neo_model_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A valid model has nonempty compatible layers, learned token and absolute
position tables, a positive final normalization epsilon, and a shaped
model-to-vocabulary projection.
:::

::: theorem {#thm-gpt-neo-model-shape}
title: GPT-Neo model logits preserve vocabulary shape
uses:
  - def-gpt-neo-model
isabelle:
  theory: GPT_Neo_Model
  fact: valid_gpt_neo_full_model_logits_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Bounded token and position inputs produce a full hidden trace and one
well-shaped logit vector per input token.

## Proof

First prove the learned token-plus-position input shape by induction over the
token list, then compose compatible stack shape preservation with final
LayerNorm and vocabulary projection.
:::

::: theorem {#thm-gpt-neo-model-next-token}
title: GPT-Neo cached next-token logits equal full logits
uses:
  - def-gpt-neo-model
  - thm-gpt-neo-stack-refinement
isabelle:
  theory: GPT_Neo_Model
  fact: gpt_neo_cached_model_evaluate_logits_correct
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For a nonempty token sequence and matching cache, cached evaluation returns the
last full-model logit vector and advances the complete stack cache relation.

## Proof

Split the token sequence into its butlast prefix and last token, apply the
stack-step refinement, and use last_map for the final vocabulary projection.
:::

::: definition {#def-gpt-neo-bounded-cache}
title: Bounded GPT-Neo sliding-window cache
uses:
  - def-gpt-neo-cache
isabelle:
  theory: GPT_Neo_Windowed_Cache
  fact: gpt_neo_projected_bounded_cache_matches_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For positive windows, the stored cache is the full projected key--value cache
trimmed to the active tail.  Window zero retains the global full history.
:::

::: theorem {#thm-gpt-neo-window-trim}
title: GPT-Neo window trimming is append-stable and idempotent
uses:
  - def-gpt-neo-bounded-cache
isabelle:
  theory: GPT_Neo_Windowed_Cache
  fact: gpt_neo_local_context_append_trim
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Appending a new normalized representation to an already trimmed cache and
trimming again gives the same tail as trimming the complete prefix once.
The attention-context operation is also idempotent.

## Proof

Case-split on global versus positive-window attention and on whether the
prefix is shorter than the window.  The remaining natural-number subtraction
reduces to the standard drop_append and drop_drop identities.
:::

::: theorem {#thm-gpt-neo-bounded-block}
title: Bounded GPT-Neo block steps refine full evaluation
uses:
  - def-gpt-neo-bounded-cache
  - thm-gpt-neo-window-trim
  - thm-gpt-neo-cache-step
isabelle:
  theory: GPT_Neo_Windowed_Cache
  fact: gpt_neo_projected_bounded_cached_block_step_output
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The bounded attention and residual block output equals the newest full GPT-Neo
block output, and the projected bounded cache relation is preserved without
reprojecting old entries.

## Proof

Use append-stable trimming to identify the bounded keys and values with the
full attention context, invoke the cached attention equality, and then unfold
the common GPT-Neo residual/MLP block.
:::

::: theorem {#thm-gpt-neo-bounded-stack}
title: Bounded GPT-Neo caches compose through stacks
uses:
  - thm-gpt-neo-bounded-block
  - thm-gpt-neo-stack-refinement
isabelle:
  theory: GPT_Neo_Windowed_Stack
  fact: gpt_neo_bounded_cached_stack_step_output
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Every compatible GPT-Neo layer can retain only its active window while the
complete stack output remains equal to full evaluation.

## Proof

Induct over layers and carry the bounded cache relation for the suffix at the
head-layer full output prefix.  The bounded block theorem supplies both the
new head output and the updated head cache.
:::

::: theorem {#thm-gpt-neo-bounded-generation}
title: Bounded GPT-Neo generation preserves safety
uses:
  - thm-gpt-neo-bounded-stack
  - thm-gpt-neo-model-next-token
isabelle:
  theory: GPT_Neo_Generation
  fact: gpt_neo_bounded_generate_steps_valid
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Finite bounded-cache transitions preserve model validity, vocabulary bounds,
the context budget, and the projected bounded cache relation; first-argmax is a
valid specialization.  A separate n-step theorem equates the bounded cached
greedy token history with the full-prefix greedy generator.

## Proof

Prove one transition from the bounded next-token refinement and selector
length theorem, then induct over the number of steps.  The first-argmax
corollary supplies the selector premise for positive vocabularies.
:::

::: theorem {#thm-gpt-neo-generation-refinement}
title: Bounded cached greedy generation equals full generation
uses:
  - thm-gpt-neo-bounded-generation
  - thm-gpt-neo-bounded-stack
isabelle:
  theory: GPT_Neo_Generation
  fact: gpt_neo_bounded_greedy_generate_steps_eq_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For every valid bounded generation state and every number of steps that fits
the absolute-position budget, the token history produced by the projected
bounded cache is exactly the history produced by full-prefix greedy
evaluation.

## Proof

Induct on the step count.  The one-step theorem identifies the cached
first-argmax token with the full-prefix token; the generation-validity theorem
supplies the cache invariant and remaining context budget for the induction
hypothesis.
:::

::: theorem {#thm-gpt-neo-initialized-generation-refinement}
title: Initialized bounded generation equals full generation
uses:
  - thm-gpt-neo-generation-refinement
  - thm-gpt-neo-bounded-stack
isabelle:
  theory: GPT_Neo_Generation
  fact: gpt_neo_bounded_initialized_greedy_generate_steps_eq_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Initializing the projected bounded cache from a valid nonempty prompt and
running any number of steps within the absolute-position budget produces the
same token history as repeated full-prefix greedy evaluation.
:::

::: theorem {#thm-gpt-neo-tiny-bounded}
title: Concrete GPT-Neo fixture exercises bounded generation
uses:
  - thm-gpt-neo-bounded-generation
isabelle:
  theory: GPT_Neo_Tiny_Checkpoint
  fact: gpt_neo_tiny_bounded_one_step
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

A concrete valid one-layer GPT-Neo record initializes a bounded prompt cache
and proves one finite greedy generation step preserves the invariant.

## Proof

Unfold the explicit one-layer record to discharge all shape and positivity
obligations, then apply bounded initialization and one-step generation safety.
:::

## GPT-Neo architecture fidelity

::: definition {#def-gpt-neo-layer-norm}
title: GPT-Neo affine LayerNorm and GELU-New components
uses:
  - def-shaped-tensors
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_layer_norm_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The GPT-Neo path uses mean/variance LayerNorm with learned gain and bias,
affine projections, and the checkpoint's GELU-New activation rather than the
RMSNorm and SwiGLU components of the modern rotary path.
:::

::: definition {#def-gpt-neo-embedding}
title: GPT-Neo learned token-position input embedding
uses:
  - def-shaped-tensors
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_input_embedding_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The input representation adds a bounded token-embedding row to the learned
absolute-position row, making both table bounds and the model dimension
explicit.
:::

::: theorem {#thm-gpt-neo-embedding-shape}
title: GPT-Neo input embeddings preserve model dimension
uses:
  - def-gpt-neo-embedding
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_input_embedding_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Valid token and position indices select equally shaped rows, so their sum is a
well-shaped hidden vector.

## Proof

Select the token and position rows with `matrix_shape_nth`, then apply
`vector_add_shape` to their equal model-dimension lengths.
:::

::: definition {#def-gpt-neo-logits}
title: GPT-Neo vocabulary projection
uses:
  - def-shaped-tensors
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_logits_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The semantic vocabulary matrix is oriented as model-dimension by vocabulary
size, making the projection orientation explicit even when checkpoint files
store the transposed PyTorch weight.
:::

::: theorem {#thm-gpt-neo-logits-shape}
title: GPT-Neo logits have the configured vocabulary size
uses:
  - def-gpt-neo-logits
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_logits_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

An input hidden vector with the model dimension maps to exactly one logit per
vocabulary entry under the explicit matrix-shape contract.

## Proof

Apply `linear_project_shape` to the model-by-vocabulary matrix and the
well-shaped hidden vector.
:::

::: definition {#def-gpt-neo-windowed-attention}
title: GPT-Neo global and sliding-window attention context
uses:
  - def-gpt-neo-layer-norm
  - def-multi-head-attention
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_attention_context_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Window zero denotes global attention; a positive window retains the most
recent window entries of each causal prefix, including its current token.
:::

::: theorem {#thm-gpt-neo-attention-shape}
title: GPT-Neo windowed multi-head attention preserves shape
uses:
  - def-gpt-neo-windowed-attention
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_windowed_multi_head_at_prefix_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Compatible ordinary multi-head Q/K/V tensors and an affine output projection
return one model-dimension vector for every normalized input and prefix.

## Proof

Use the exact-attention shape theorem for every mapped head, concatenate the
equal head vectors, and apply the affine output shape theorem.
:::

::: definition {#def-gpt-neo-layer}
title: Validated pre-LayerNorm GPT-Neo block
uses:
  - def-gpt-neo-windowed-attention
  - def-valid-model
isabelle:
  theory: GPT_Neo_Components
  fact: gpt_neo_block_at_prefix_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The block applies LayerNorm, biased global or local multi-head attention, an
attention residual, a second LayerNorm, affine GELU-New MLP, and an MLP
residual in the order used by GPT-Neo.
:::

::: theorem {#thm-gpt-neo-layer-shape}
title: Valid GPT-Neo blocks preserve model dimension
uses:
  - def-gpt-neo-layer
isabelle:
  theory: GPT_Neo_Components
  fact: valid_gpt_neo_block_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The explicit GPT-Neo parameter contract is sufficient for every block output
to have the same dimension as its input.

## Proof

LayerNorm preserves vector length, attention preserves the model dimension,
and the two residual shape theorems compose with the MLP.
:::

::: theorem {#thm-gpt-neo-full-layer}
title: GPT-Neo full-layer evaluation is causal and shape-safe
uses:
  - thm-gpt-neo-layer-shape
isabelle:
  theory: GPT_Neo_Components
  fact: valid_gpt_neo_full_layer_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Prefix evaluation of a valid GPT-Neo block preserves the complete matrix
shape, and its full sequence operator satisfies the generic causality theorem.

## Proof

Induct over the input sequence; each prefix-local block output has the model
dimension, then use the generic `causal_attention` shape and causality lemmas.
:::

::: definition {#def-gpt-neo-cache}
title: GPT-Neo normalized-prefix attention cache
uses:
  - def-gpt-neo-layer
  - def-kv-cache
isabelle:
  theory: GPT_Neo_Incremental
  fact: gpt_neo_cache_matches_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Because LayerNorm is token-local, the cache stores the first-normalized
representations of the processed prefix.  It is deliberately a full-history
semantic cache; bounded-window storage is a later implementation refinement.
:::

::: theorem {#thm-gpt-neo-cache-attention}
title: GPT-Neo cached attention equals full windowed attention
uses:
  - def-gpt-neo-cache
  - def-gpt-neo-windowed-attention
isabelle:
  theory: GPT_Neo_Incremental
  fact: gpt_neo_cached_attention_correct
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Appending a token to a matching normalized-prefix cache gives exactly the
global or sliding-window attention result over the corresponding full prefix.

## Proof

Commute the sliding-window context through `map`, instantiate the generic
`cached_step` refinement with normalized prefix representations, and rewrite
the aggregator to the full GPT-Neo attention expression.
:::

::: theorem {#thm-gpt-neo-cache-step}
title: GPT-Neo cached block steps refine full-layer extension
uses:
  - thm-gpt-neo-cache-attention
  - thm-gpt-neo-layer-shape
isabelle:
  theory: GPT_Neo_Incremental
  fact: gpt_neo_cached_block_step_output
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The cached pre-LayerNorm attention, residual, GELU-New MLP, and residual step
returns the same vector as full GPT-Neo layer evaluation and preserves the
normalized-prefix cache invariant.

## Proof

Rewrite the cached attention result, unfold the GPT-Neo block, and use the
cache-preservation theorem for the normalized prefix.
:::

::: theorem {#thm-gpt-neo-cache-full}
title: GPT-Neo cached steps equal full-layer sequence extension
uses:
  - thm-gpt-neo-cache-step
isabelle:
  theory: GPT_Neo_Incremental
  fact: gpt_neo_cached_block_step_full
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The exact cached block result can replace the newest element of full
GPT-Neo-layer evaluation, including the chosen local attention context.

## Proof

Expand full-layer append using `causal_attention_append` and replace its
newest block output with the cached-step equality.
:::

## Concrete checkpoint execution

::: definition {#def-tiny-checkpoint}
title: Explicit two-token modern decoder checkpoint
uses:
  - def-unified-modern-layer
isabelle:
  theory: Tiny_Decoder_Checkpoint
  fact: tiny_modern_layer_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

One query head, one key-value head, model and head dimension two, hidden
dimension two, identity RoPE, explicit gains, and concrete zero matrices form
a fully instantiated modern decoder layer.  Two explicit embeddings and a
two-by-two identity vocabulary matrix complete the checkpoint.
:::

::: theorem {#thm-tiny-checkpoint-valid}
title: The concrete checkpoint satisfies every model obligation
uses:
  - def-tiny-checkpoint
  - thm-unified-modern-layer-shape
isabelle:
  theory: Tiny_Decoder_Checkpoint
  fact: tiny_modern_layer_valid
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

All positivity, head-divisibility, dimension, matrix, tensor, gain, and RoPE
shape obligations reduce and are checked for the explicit record.
:::

::: theorem {#thm-tiny-full-identity}
title: Full evaluation of the concrete stack is exactly identity
uses:
  - thm-tiny-checkpoint-valid
  - thm-modern-stack-shape
isabelle:
  theory: Tiny_Decoder_Checkpoint
  fact: tiny_full_stack_identity
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Zero attention and SwiGLU branches vanish, so residual connections return
each two-dimensional input unchanged.  Induction lifts this fact from one
position to arbitrary shaped prompts and the complete one-layer stack.
:::

::: theorem {#thm-tiny-cached-execution}
title: Concrete cached prompt execution returns exact outputs and cache
uses:
  - thm-tiny-full-identity
  - thm-modern-prompt-refinement
isabelle:
  theory: Tiny_Decoder_Checkpoint
  fact: tiny_cached_prompt_execution
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Running the concrete stack from canonical empty caches returns exactly the
embedded prompt and a final grouped key-value cache satisfying the formal
prefix relation.
:::

::: theorem {#thm-tiny-checkpoint-logits}
title: Concrete vocabulary logits expose the final embedding
uses:
  - thm-tiny-full-identity
isabelle:
  theory: Tiny_Decoder_Checkpoint
  fact: tiny_checkpoint_logits
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The explicit identity vocabulary projection maps the final full-stack hidden
state to the exact embedding of the final input token.
:::

::: theorem {#thm-tiny-generation-trace}
title: Arbitrary finite concrete generation has a closed trace
uses:
  - thm-tiny-cached-execution
  - thm-modern-generation-invariant
isabelle:
  theory: Tiny_Decoder_Checkpoint
  fact: tiny_initialized_generation_trace
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The zero vocabulary matrix yields the exact uniform distribution `[1/2,1/2]`,
whose first maximum is token zero.  From any nonempty initialized prompt,
`n` cached generation steps therefore produce `tokens @ replicate n 0`; the
three-step example from `[1]` is `[1,0,0,0]`.
:::

## Deterministic checkpoint import

::: definition {#def-imported-checkpoint}
title: Shape-checked nonzero checkpoint import
uses:
  - def-tiny-checkpoint
isabelle:
  theory: Imported_Decoder_Checkpoint
  fact: imported_modern_layer_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

`tools/import_decoder_checkpoint.py` validates a deterministic JSON schema and
renders the complete modern-layer record, embedding rows, and vocabulary head
as Isabelle constants.  The checked-in fixture is deliberately synthetic (not
a provenance claim about a trained model), but every listed projection is
nonzero and the importer fixes identity RoPE explicitly.
:::

::: theorem {#thm-imported-checkpoint-valid}
title: Imported checkpoint satisfies the modern parameter contract
uses:
  - def-imported-checkpoint
  - thm-unified-modern-layer-shape
isabelle:
  theory: Imported_Decoder_Checkpoint
  fact: imported_modern_layer_valid
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The generated theory proves positivity, divisibility, gain dimensions, all
rank-three and matrix shapes, and the identity-RoPE shape obligation for the
imported record.  A separate fact certifies that each imported projection is
nonzero.
:::

::: theorem {#thm-imported-stack-valid}
title: Imported checkpoint stack is valid
uses:
  - thm-imported-checkpoint-valid
isabelle:
  theory: Imported_Decoder_Checkpoint
  fact: imported_modern_stack_valid
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The one-layer generated list satisfies the recursive stack validity predicate,
so it can be passed directly to the general incremental refinement theorems.
:::

::: theorem {#thm-imported-prompt-refinement}
title: Imported nonzero prompt run equals full evaluation
uses:
  - thm-imported-stack-valid
  - thm-modern-prompt-refinement
isabelle:
  theory: Imported_Decoder_Checkpoint
  fact: imported_cached_prompt_refinement
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

For every token list, running the generated nonzero checkpoint from canonical
empty caches returns exactly the full modern-stack output.  A companion fact
proves the final cache relation for the same run.
:::

::: theorem {#thm-imported-next-token-refinement}
title: Imported next-token evaluation uses the full hidden state
uses:
  - thm-imported-prompt-refinement
  - thm-modern-next-token-refinement
isabelle:
  theory: Imported_Decoder_Checkpoint
  fact: imported_cached_next_token_refinement
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Under the generated checkpoint's cache invariant, the cached vocabulary
distribution with its imported two-row projection equals the distribution
formed from the last hidden vector of full evaluation.  Initialization also
has a checked nonempty-prompt cache invariant.
:::

## Two-layer modern checkpoint fixture

::: definition {#def-two-layer-checkpoint}
title: Deterministic two-layer GQA/RoPE/SwiGLU checkpoint
uses:
  - def-imported-checkpoint
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_modern_layers_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The importer extends the nonzero fixture to two compatible modern layers with
two query heads sharing one key--value head, explicit pairwise RoPE angle
tables, and nonzero SwiGLU projections.  The JSON records provenance as a
synthetic deterministic integration fixture; it is not a trained-checkpoint
claim.
:::

::: theorem {#thm-two-layer-checkpoint-valid}
title: Two-layer checkpoint satisfies the modern stack contract
uses:
  - def-two-layer-checkpoint
  - thm-modern-stack-shape
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_modern_stack_valid
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Both generated records satisfy all positivity, divisibility, tensor-shape, and
RoPE shape obligations, and their list satisfies the recursive stack validity
predicate.
:::

::: theorem {#thm-two-layer-gqa-rope}
title: Two-layer fixture records GQA sharing and a concrete RoPE angle
uses:
  - thm-two-layer-checkpoint-valid
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_gqa_grouping
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The checked two-query/one-KV fixture shares one key--value head, while the
generated routing regression also checks the non-degenerate four-query/two-KV
layout `0, 0, 1, 1`.  The generated layer-zero angle table evaluates its first
pair at the explicit value 1/2.
:::

::: theorem {#thm-two-layer-prompt-refinement}
title: Two-layer imported prompt execution equals full evaluation
uses:
  - thm-two-layer-checkpoint-valid
  - thm-modern-prompt-refinement
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_cached_prompt_refinement
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Starting from canonical empty caches, the two-layer modern cached prompt run
returns the exact full-stack output matrix.
:::

::: theorem {#thm-two-layer-prompt-cache}
title: Two-layer imported prompt run finishes with a matching cache
uses:
  - thm-two-layer-prompt-refinement
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_cached_prompt_cache
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The same generated execution has a kernel-checked position-aware grouped cache
matching the complete prompt at every layer.
:::

::: theorem {#thm-two-layer-next-token}
title: Two-layer imported next-token evaluation refines full logits
uses:
  - thm-two-layer-prompt-cache
  - thm-modern-next-token-refinement
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_cached_next_token_refinement
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Under the generated cache invariant, the imported vocabulary head receives the
same final hidden vector as full two-layer evaluation.
:::

::: theorem {#thm-two-layer-generation-init}
title: Two-layer imported initialization preserves the generation invariant
uses:
  - thm-two-layer-prompt-cache
isabelle:
  theory: Two_Layer_GQA_Checkpoint
  fact: imported_initialized_generation_state_valid
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Every nonempty prompt initializes a valid two-layer modern generation state
with the checked recursive cache relation.
:::

## Concrete binary32 certificate fixture

::: definition {#def-concrete-binary32-certificate}
title: Explicit binary32 projection witness data
uses:
  - def-ieee-witness-certificate
isabelle:
  theory: Concrete_IEEE_Certificate
  fact: concrete_certificates_def
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The theory fixes a small one-hot binary32 vocabulary head, a four-coordinate
hidden vector, and one finite same-format witness per recursive FMA step.  It
is a transparent certificate fixture for replay and does not claim to be the
two-layer synthetic checkpoint's trained weights.
:::

::: theorem {#thm-concrete-binary32-certificate}
title: Kernel checks the explicit binary32 projection certificate
uses:
  - def-concrete-binary32-certificate
  - thm-ieee-certificate-replay
isabelle:
  theory: Concrete_IEEE_Certificate
  fact: concrete_projection_certificate
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The finite binary32 witness matrix satisfies the full projection-certificate
predicate, including output-column length, finite operands, strict threshold
range, and nearest-value witness obligations.
:::

::: theorem {#thm-concrete-binary32-error}
title: Explicit binary32 certificate yields the dimension bound
uses:
  - thm-concrete-binary32-certificate
isabelle:
  theory: Concrete_IEEE_Certificate
  fact: concrete_projection_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The replayed certificate specializes the generic theorem to the concrete
four-dimensional head and proves the coordinatewise projection error bound
4 * epsilon with epsilon = 1.
:::

## Frozen public checkpoint trace

::: definition {#def-frozen-tinystories-trace}
title: Pinned TinyStories-1M binary32 activation trace
uses:
  - thm-ieee-certificate-replay
isabelle:
  theory: Frozen_TinyStories_Trace
  fact: frozen_input_shape
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

`tools/import_frozen_checkpoint.py` pins the public TinyStories-1M GPT-Neo
revision `77f1b168e219585646439073245fe87e56b3023e`, records configuration and
checkpoint SHA-256 digests, and emits exact binary32 bit triples for one token,
one position, and four selected layer-zero Q/K/V/MLP rows.  The generated
theory keeps the data replayable in Isabelle rather than treating a Python
float dump as a proof artifact.
:::

::: theorem {#thm-frozen-trace-certificate}
title: Every selected public-checkpoint FMA trace is certified
uses:
  - def-frozen-tinystories-trace
  - thm-ieee-certificate-replay
isabelle:
  theory: Frozen_TinyStories_Trace
  fact: frozen_trace_certificate
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

The four selected 64-term dot products satisfy the reusable tail-witness
certificate: lengths, finite operands, strict binary32 threshold range, and a
same-format previous-accumulator witness at every FMA step.
:::

::: theorem {#thm-frozen-trace-safe}
title: The frozen public traces are overflow-safe
uses:
  - thm-frozen-trace-certificate
isabelle:
  theory: Frozen_TinyStories_Trace
  fact: frozen_trace_safe
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Replaying the certificate establishes the AFP IEEE safety predicate for every
selected row, including every recursive fused multiply-add step.
:::

::: theorem {#thm-frozen-trace-error}
title: Frozen public traces have a replayable local-FMA envelope
uses:
  - thm-frozen-trace-safe
isabelle:
  theory: Frozen_TinyStories_Trace
  fact: frozen_trace_error
  session: Decoder_Transformer
status:
  blueprint: written
  formal: proved
  agent: solved

Each selected row's IEEE fused dot product differs from its exact real dot
product by at most 64 under the supplied unit per-step budget.  This is
explicitly a replayable local FMA certificate demonstration, not a numerical
accuracy estimate: 64 is the worst-case sum of one unit budget for each of the
64 certified steps.  The theorem is deliberately scoped to this selected
linear slice, not a full attention, GELU, softmax, or all-layer GPT-Neo forward
proof.
:::
