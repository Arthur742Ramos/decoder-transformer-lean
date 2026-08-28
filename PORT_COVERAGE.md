# Isabelle to Lean port coverage

Source: `projects/decoder-transformer-isabelle` at revision
`b69c6e519c9c810019f3f92e94d6c01e56030947`.

The source has 34 theories and 15,676 lines. The Lean names are adapted to
Lean conventions; the semantic definitions and theorem boundaries are
preserved. The source-compatible aliases in the core modules retain the
important Isabelle names where Lean naming differs.

| Isabelle theory | Lean module | Status |
| --- | --- | --- |
| Prefix_Sequences | DecoderTransformer.Prefix | checked |
| Causal_Attention | DecoderTransformer.Attention | checked |
| KV_Cache | DecoderTransformer.Cache | checked |
| Shaped_Tensors | DecoderTransformer.Shaped | checked |
| Exact_Attention | DecoderTransformer.ExactAttention | checked |
| Multi_Head_Attention | DecoderTransformer.MultiHead | checked |
| GPT_Neo_Components | DecoderTransformer.GPTNeoComponents | checked |
| GPT_Neo_Incremental | DecoderTransformer.GPTNeoIncremental | checked |
| GPT_Neo_Windowed_Cache | DecoderTransformer.GPTNeoWindowedCache | checked |
| GPT_Neo_Stack | DecoderTransformer.GPTNeoStack | checked |
| GPT_Neo_Windowed_Stack | DecoderTransformer.GPTNeoWindowedStack | checked |
| GPT_Neo_Model | DecoderTransformer.GPTNeoModel | checked |
| Decoder_Block | DecoderTransformer.DecoderBlock | checked |
| Incremental_Decoder | DecoderTransformer.Incremental | checked |
| Autoregressive_Generation | DecoderTransformer.Autoregressive | checked |
| Numerical_Refinement | DecoderTransformer.Numerical | checked |
| Model_Validity | DecoderTransformer.ModelValidity | checked |
| Prompt_Cache | DecoderTransformer.Prompt | checked |
| Projection_Stability | DecoderTransformer.Projection | checked |
| Rotary_Position_Embedding | DecoderTransformer.Rotary | checked |
| Modern_Decoder_Components | DecoderTransformer.Modern | checked |
| Decoding_Policies | DecoderTransformer.Decoding | checked |
| GPT_Neo_Generation | DecoderTransformer.GPTNeoGeneration | checked |
| GPT_Neo_Tiny_Checkpoint | DecoderTransformer.GPTNeoTinyCheckpoint | checked |
| Modern_Incremental_Decoder | DecoderTransformer.ModernIncremental | checked |
| Modern_Generation | DecoderTransformer.ModernGeneration | checked |
| Dyadic_Finite_Precision | DecoderTransformer.DyadicFinitePrecision | checked |
| IEEE_754_Projection | DecoderTransformer.IEEE754Projection | checked* |
| Tiny_Decoder_Checkpoint | DecoderTransformer.TinyDecoderCheckpoint | checked |
| Imported_Decoder_Checkpoint | DecoderTransformer.ImportedDecoderCheckpoint | checked |
| Two_Layer_GQA_Checkpoint | DecoderTransformer.TwoLayerGQACheckpoint | checked |
| Concrete_IEEE_Certificate | DecoderTransformer.ConcreteIEEECertificate | checked* |
| IEEE_Trace_Certificate | DecoderTransformer.IEEETraceCertificate | checked* |
| Frozen_TinyStories_Trace | DecoderTransformer.FrozenTinyStoriesTrace | checked* |

The asterisk records the IEEE backend boundary: these modules preserve the
source predicates, decoded arithmetic, certificates, and checkpoint data,
but the Lean repository does not import the source AFP's parameterized
bit-level IEEE library. They therefore do not assert hardware-level or
bit-identical FP32 behavior.

The complete import root is `DecoderTransformer.lean`. `Examples.lean` is a
small executable smoke-test module and is not an Isabelle theory.

The declaration audit found 763 unique source definitions and 1,045 named
source lemmas/theorems; their normalized names all have Lean counterparts.
The additional Lean declarations are helper facts, backend interfaces, and
source-compatible aliases used to keep the port readable and independently
checkable.
