import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.GetD

/-!
# Palomar challenge contract

This module is an independent, executable statement surface.  Its compared
definitions are concrete mathematical functions and predicates, not opaque
placeholders:

* vectors, matrices, and rank-three tensors are finite lists with explicit
  shape predicates;
* a modern layer is valid exactly when its positive dimensions, head
  divisibility, normalization constants, parameter shapes, and rotary shape
  preservation constraints hold;
* `modernTransformerCacheMatches` says, recursively for every layer, that the
  cache is exactly the key/value projection of the transformed prefix;
* full evaluation is causal grouped-query attention followed by the residual
  SwiGLU block, while cached evaluation appends the current key/value before
  applying the same computation;
* generation is the recursive cached transition versus recursive full-prefix
  transition, and `firstArgmax [] = 0` is the explicit totalized convention;
* `vectorErrorBound` is equal length plus a coordinatewise absolute bound, and
  dyadic logits are a nearest-grid fused multiply-add projection.

The advertised theorems below use `palomarModernStackWellFormed`, which
requires a nonempty stack, valid layers, and one common model dimension.  The
generation and logit claims additionally require a positive vocabulary size.
The underlying list functions remain total outside those hypotheses, but such
incompatible or empty-vocabulary evaluations are not included in the claims.
-/

namespace DecoderTransformer

noncomputable section

abbrev Vector (α : Type*) := List α
abbrev Matrix (α : Type*) := List (List α)
abbrev Tensor3 (α : Type*) := List (List (List α))

structure KVCache (k v : Type*) where
  keys : List k
  values : List v

structure ModernDecoderLayerParameters where
  queryHeadCount : Nat
  kvHeadCount : Nat
  modelDim : Nat
  headDim : Nat
  hiddenDim : Nat
  normEpsilon : ℝ
  rope : Nat → Vector ℝ → Vector ℝ
  attentionGain : Vector ℝ
  mlpGain : Vector ℝ
  queryWeights : Tensor3 ℝ
  keyWeights : Tensor3 ℝ
  valueWeights : Tensor3 ℝ
  outputWeights : Matrix ℝ
  gateWeights : Matrix ℝ
  upWeights : Matrix ℝ
  downWeights : Matrix ℝ

abbrev ModernLayerCache := List (KVCache (Vector ℝ) (Vector ℝ))
abbrev ModernTransformerCache := List ModernLayerCache
abbrev ModernGenerationState := List Nat × ModernTransformerCache

def vectorShape (n : Nat) (xs : Vector α) : Prop :=
  xs.length = n

def matrixShape (rows cols : Nat) (M : Matrix α) : Prop :=
  M.length = rows ∧ ∀ row ∈ M, row.length = cols

def tensor3Shape (d₁ d₂ d₃ : Nat) (T : Tensor3 α) : Prop :=
  T.length = d₁ ∧ ∀ M ∈ T, matrixShape d₂ d₃ M

def nthOrZero [Zero α] : List α → Nat → α
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nthOrZero xs n

def dotProduct [Mul α] [AddMonoid α] (xs ys : Vector α) : α :=
  (List.zipWith (· * ·) xs ys).sum

def matrixColumns [Zero α] (cols : Nat) (M : Matrix α) : Matrix α :=
  (List.range cols).map (fun j => M.map (fun row => nthOrZero row j))

def linearProject [Mul α] [AddMonoid α]
    (outDim : Nat) (W : Matrix α) (x : Vector α) : Vector α :=
  (matrixColumns outDim W).map (dotProduct x)

def tensorMatrixAt (T : Tensor3 ℝ) (h : Nat) : Matrix ℝ := T.getD h []

def rmsDenominator (epsilon : ℝ) (x : Vector ℝ) : ℝ :=
  Real.sqrt ((x.map (fun v => v * v)).sum / x.length + epsilon)

def rmsNorm (epsilon : ℝ) (gain x : Vector ℝ) : Vector ℝ :=
  List.zipWith (fun g v => g * (v / rmsDenominator epsilon x)) gain x

def vectorAdd (xs ys : Vector ℝ) : Vector ℝ :=
  List.zipWith (· + ·) xs ys

def softmaxDenominator (xs : List ℝ) : ℝ :=
  (xs.map Real.exp).sum

def listSoftmax (xs : List ℝ) : List ℝ :=
  xs.map (fun x => Real.exp x / softmaxDenominator xs)

def scaledDotScore (headDim : Nat) (q k : Vector ℝ) : ℝ :=
  dotProduct q k / Real.sqrt (headDim : ℝ)

def attentionWeights (headDim : Nat) (q : Vector ℝ) (keys : Matrix ℝ) :
    Vector ℝ :=
  listSoftmax (keys.map (scaledDotScore headDim q))

def weightedValueSum (valueDim : Nat) (weights : Vector ℝ)
    (values : Matrix ℝ) : Vector ℝ :=
  (List.range valueDim).map (fun j =>
    (List.zipWith (fun w v => w * nthOrZero v j) weights values).sum)

def exactAttention (headDim valueDim : Nat) (q : Vector ℝ)
    (keys values : Matrix ℝ) : Vector ℝ :=
  weightedValueSum valueDim (attentionWeights headDim q keys) values

def indexedSequence (start : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (start, x) :: indexedSequence (start + 1) xs

def causalAttentionFrom (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) (pref : List x) : List x → List o
  | [] => []
  | y :: ys =>
      A (Q y) (List.map K (pref ++ [y])) (List.map V (pref ++ [y])) ::
        causalAttentionFrom Q K V A (pref ++ [y]) ys

def causalAttention (Q : x → q) (K : x → k) (V : x → v)
    (A : q → List k → List v → o) : List x → List o :=
  causalAttentionFrom Q K V A []

def groupedQueryHeadIndex (queryHeads kvHeads queryHead : Nat) : Nat :=
  queryHead / (queryHeads / kvHeads)

def vectorHadamard (xs ys : Vector ℝ) : Vector ℝ :=
  List.zipWith (· * ·) xs ys

def silu (x : ℝ) : ℝ := x / (1 + Real.exp (-x))

def swiglu (modelDim hiddenDim : Nat)
    (Wgate Wup Wdown : Matrix ℝ) : Vector ℝ → Vector ℝ :=
  fun x =>
    linearProject modelDim Wdown
      (vectorHadamard
        ((linearProject hiddenDim Wgate x).map silu)
        (linearProject hiddenDim Wup x))

def modernNormalize (p : ModernDecoderLayerParameters) (x : Vector ℝ) :
    Vector ℝ := rmsNorm p.normEpsilon p.attentionGain x

def modernKeyAt (p : ModernDecoderLayerParameters) (kvHead position : Nat)
    (x : Vector ℝ) : Vector ℝ :=
  p.rope position
    (linearProject p.headDim (tensorMatrixAt p.keyWeights kvHead)
      (modernNormalize p x))

def modernValueAt (p : ModernDecoderLayerParameters) (kvHead : Nat)
    (x : Vector ℝ) : Vector ℝ :=
  linearProject p.headDim (tensorMatrixAt p.valueWeights kvHead)
    (modernNormalize p x)

def modernQueryAt (p : ModernDecoderLayerParameters)
    (queryHead position : Nat) (x : Vector ℝ) : Vector ℝ :=
  p.rope position
    (linearProject p.headDim (tensorMatrixAt p.queryWeights queryHead)
      (modernNormalize p x))

def modernGroupedAttentionAtPrefix (p : ModernDecoderLayerParameters)
    (ix : Nat × Vector ℝ) (pref : List (Nat × Vector ℝ)) : Vector ℝ :=
  linearProject p.modelDim p.outputWeights
    ((List.range p.queryHeadCount).map (fun h =>
      let g := groupedQueryHeadIndex p.queryHeadCount p.kvHeadCount h
      exactAttention p.headDim p.headDim
        (modernQueryAt p h ix.1 ix.2)
        (pref.map (fun jx => modernKeyAt p g jx.1 jx.2))
        (pref.map (fun jx => modernValueAt p g jx.2)))).flatten

def modernDecoderAtIndexedPrefix (p : ModernDecoderLayerParameters)
    (ix : Nat × Vector ℝ) (pref : List (Nat × Vector ℝ)) : Vector ℝ :=
  let attention := modernGroupedAttentionAtPrefix p ix pref
  let attentionResidual := vectorAdd ix.2 attention
  let mlpInput := rmsNorm p.normEpsilon p.mlpGain attentionResidual
  let mlp := swiglu p.modelDim p.hiddenDim p.gateWeights p.upWeights
    p.downWeights mlpInput
  vectorAdd attentionResidual mlp

def fullModernDecoderLayer (p : ModernDecoderLayerParameters) (start : Nat)
    (X : Matrix ℝ) : Matrix ℝ :=
  causalAttention id id id
    (fun ix pref _ => modernDecoderAtIndexedPrefix p ix pref)
    (indexedSequence start X)

def fullModernDecoderStack : List ModernDecoderLayerParameters → Nat →
    Matrix ℝ → Matrix ℝ
  | [], _, X => X
  | p :: ps, start, X =>
      fullModernDecoderStack ps start (fullModernDecoderLayer p start X)

def validModernDecoderLayer (p : ModernDecoderLayerParameters) : Prop :=
  0 < p.queryHeadCount ∧
  0 < p.kvHeadCount ∧
  0 < p.modelDim ∧
  0 < p.headDim ∧
  0 < p.hiddenDim ∧
  p.modelDim = p.queryHeadCount * p.headDim ∧
  p.kvHeadCount ∣ p.queryHeadCount ∧
  0 < p.normEpsilon ∧
  vectorShape p.modelDim p.attentionGain ∧
  vectorShape p.modelDim p.mlpGain ∧
  tensor3Shape p.queryHeadCount p.modelDim p.headDim p.queryWeights ∧
  tensor3Shape p.kvHeadCount p.modelDim p.headDim p.keyWeights ∧
  tensor3Shape p.kvHeadCount p.modelDim p.headDim p.valueWeights ∧
  matrixShape (p.queryHeadCount * p.headDim) p.modelDim p.outputWeights ∧
  matrixShape p.modelDim p.hiddenDim p.gateWeights ∧
  matrixShape p.modelDim p.hiddenDim p.upWeights ∧
  matrixShape p.hiddenDim p.modelDim p.downWeights ∧
  (∀ position x, vectorShape p.headDim x →
    vectorShape p.headDim (p.rope position x))

def validModernStack (layers : List ModernDecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validModernDecoderLayer p

def modernStackCompatible (modelDim : Nat)
    (layers : List ModernDecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validModernDecoderLayer p ∧ p.modelDim = modelDim

def palomarModernStackWellFormed (modelDim : Nat)
    (layers : List ModernDecoderLayerParameters) : Prop :=
  layers ≠ [] ∧ validModernStack layers ∧
    modernStackCompatible modelDim layers

def emptyCache : KVCache (Vector ℝ) (Vector ℝ) := ⟨[], []⟩

def cacheOf (K : α → Vector ℝ) (V : α → Vector ℝ) (xs : List α) :
    KVCache (Vector ℝ) (Vector ℝ) :=
  ⟨xs.map K, xs.map V⟩

def modernLayerCacheOf (p : ModernDecoderLayerParameters) (start : Nat)
    (pref : Matrix ℝ) : ModernLayerCache :=
  (List.range p.kvHeadCount).map (fun g =>
    cacheOf (fun ix : Nat × Vector ℝ => modernKeyAt p g ix.1 ix.2)
      (fun ix : Nat × Vector ℝ => modernValueAt p g ix.2)
      (indexedSequence start pref))

def modernLayerCacheMatches (p : ModernDecoderLayerParameters) (start : Nat)
    (pref : Matrix ℝ) (cache : ModernLayerCache) : Prop :=
  cache = modernLayerCacheOf p start pref

def modernExtendHeadCache (p : ModernDecoderLayerParameters) (g position : Nat)
    (x : Vector ℝ) (cache : KVCache (Vector ℝ) (Vector ℝ)) :
    KVCache (Vector ℝ) (Vector ℝ) :=
  ⟨cache.keys ++ [modernKeyAt p g position x],
   cache.values ++ [modernValueAt p g x]⟩

def modernExtendLayerCache (p : ModernDecoderLayerParameters) (position : Nat)
    (x : Vector ℝ) (cache : ModernLayerCache) : ModernLayerCache :=
  (List.range p.kvHeadCount).map (fun g =>
    modernExtendHeadCache p g position x (cache.getD g emptyCache))

def cachedModernGroupedAttention (p : ModernDecoderLayerParameters)
    (position : Nat) (x : Vector ℝ) (cache : ModernLayerCache) : Vector ℝ :=
  linearProject p.modelDim p.outputWeights
    ((List.range p.queryHeadCount).map (fun h =>
      let g := groupedQueryHeadIndex p.queryHeadCount p.kvHeadCount h
      let entry := cache.getD g emptyCache
      exactAttention p.headDim p.headDim
        (modernQueryAt p h position x) entry.keys entry.values)).flatten

def cachedModernDecoderLayerStep (p : ModernDecoderLayerParameters)
    (position : Nat) (x : Vector ℝ) (cache : ModernLayerCache) :
    Vector ℝ × ModernLayerCache :=
  let cache' := modernExtendLayerCache p position x cache
  let attention := cachedModernGroupedAttention p position x cache'
  let residual := vectorAdd x attention
  let mlpInput := rmsNorm p.normEpsilon p.mlpGain residual
  let mlp := swiglu p.modelDim p.hiddenDim p.gateWeights p.upWeights
    p.downWeights mlpInput
  (vectorAdd residual mlp, cache')

/- The cache relation is a layer-by-layer invariant over the transformed
   prefix, so the next layer sees the output of the preceding full layer. -/
def modernTransformerCacheMatches
    (layers : List ModernDecoderLayerParameters) (start : Nat)
    (pref : Matrix ℝ) (caches : ModernTransformerCache) : Prop :=
  match layers, caches with
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | p :: ps, cache :: rest =>
      modernLayerCacheMatches p start pref cache ∧
        modernTransformerCacheMatches ps start
          (fullModernDecoderLayer p start pref) rest

def cachedModernDecoderStackStep :
    List ModernDecoderLayerParameters → Nat → Vector ℝ →
      ModernTransformerCache → Vector ℝ × ModernTransformerCache
  | [], _, x, _ => (x, [])
  | _ :: _, _, x, [] => (x, [])
  | p :: ps, position, x, cache :: rest =>
      let layerStep := cachedModernDecoderLayerStep p position x cache
      let stackStep := cachedModernDecoderStackStep ps position layerStep.1 rest
      (stackStep.1, layerStep.2 :: stackStep.2)

def modernGenerationCacheMatches (embedding : Nat → Vector ℝ)
    (layers : List ModernDecoderLayerParameters) (start : Nat)
    (tokens : List Nat) (caches : ModernTransformerCache) : Prop :=
  tokens ≠ [] ∧ validModernStack layers ∧
    modernTransformerCacheMatches layers start
      (tokens.dropLast.map embedding) caches

def nextTokenLogits (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  linearProject vocabularySize vocabularyWeights hidden

def nextTokenDistribution (vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  listSoftmax (nextTokenLogits vocabularySize vocabularyWeights hidden)

def firstArgmax : Vector ℝ → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: ys =>
      let i := firstArgmax (y :: ys)
      if x ≥ (y :: ys).getD i 0 then 0 else i + 1

def deterministicNextToken (select : Vector ℝ → Nat) (distribution : Vector ℝ) :
    Nat := select distribution

def lastNat (tokens : List Nat) : Nat := tokens.getLast?.getD 0

def cachedModernGenerationEvaluate
    (layers : List ModernDecoderLayerParameters) (embedding : Nat → Vector ℝ)
    (start vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (tokens : List Nat) (caches : ModernTransformerCache) :
    Vector ℝ × ModernTransformerCache :=
  if tokens = [] then ([], caches)
  else
    let pref := tokens.dropLast.map embedding
    let step := cachedModernDecoderStackStep layers
      (start + pref.length) (embedding (lastNat tokens)) caches
    (nextTokenDistribution vocabularySize vocabularyWeights step.1, step.2)

def modernGenerationTransition (select : Vector ℝ → Nat)
    (layers : List ModernDecoderLayerParameters) (embedding : Nat → Vector ℝ)
    (start vocabularySize : Nat) (vocabularyWeights : Matrix ℝ)
    (state : ModernGenerationState) : ModernGenerationState :=
  let evaluation := cachedModernGenerationEvaluate layers embedding start
    vocabularySize vocabularyWeights state.1 state.2
  let next := deterministicNextToken select evaluation.1
  (state.1 ++ [next], evaluation.2)

def modernGenerateSteps : Nat → (Vector ℝ → Nat) →
    List ModernDecoderLayerParameters → (Nat → Vector ℝ) → Nat → Nat →
    Matrix ℝ → ModernGenerationState → ModernGenerationState
  | 0, _, _, _, _, _, _, state => state
  | n + 1, select, layers, embedding, start, vocabularySize,
      vocabularyWeights, state =>
      modernGenerateSteps n select layers embedding start vocabularySize
        vocabularyWeights
        (modernGenerationTransition select layers embedding start vocabularySize
          vocabularyWeights state)

def modernFullNextToken (layers : List ModernDecoderLayerParameters)
    (embedding : Nat → Vector ℝ) (start vocabularySize : Nat)
    (vocabularyWeights : Matrix ℝ) (tokens : List Nat) : Nat :=
  firstArgmax (nextTokenDistribution vocabularySize vocabularyWeights
    ((fullModernDecoderStack layers start
      (tokens.map embedding)).getLast?.getD ([] : Vector ℝ)))

def modernFullGenerateSteps : Nat → List ModernDecoderLayerParameters →
    (Nat → Vector ℝ) → Nat → Nat → Matrix ℝ → List Nat → List Nat
  | 0, _, _, _, _, _, tokens => tokens
  | n + 1, layers, embedding, start, vocabularySize, vocabularyWeights, tokens =>
      modernFullGenerateSteps n layers embedding start vocabularySize
        vocabularyWeights
        (tokens ++ [modernFullNextToken layers embedding start vocabularySize
          vocabularyWeights tokens])

def dyadicScale (p : Nat) : ℝ := (2 : ℝ) ^ p

def dyadicUnitRoundoff (p : Nat) : ℝ :=
  (2 * dyadicScale p)⁻¹

def dyadicRound (p : Nat) (x : ℝ) : ℝ :=
  (round (x * dyadicScale p) : ℝ) / dyadicScale p

def dyadicFmaDot (p : Nat) : Vector ℝ → Vector ℝ → ℝ
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, w :: ws =>
      dyadicRound p (x * w + dyadicFmaDot p xs ws)

def dyadicLinearProject (p outDim : Nat) (W : Matrix ℝ) (x : Vector ℝ) :
    Vector ℝ :=
  (matrixColumns outDim W).map (dyadicFmaDot p x)

def dyadicNextTokenLogits (p vocabularySize : Nat) (W : Matrix ℝ)
    (hidden : Vector ℝ) : Vector ℝ :=
  dyadicLinearProject p vocabularySize W hidden

def vectorErrorBound (epsilon : ℝ) (xs ys : Vector ℝ) : Prop :=
  xs.length = ys.length ∧
    ∀ i, i < xs.length →
      |xs.getD i 0 - ys.getD i 0| ≤ epsilon

/- The three advertised contracts are strengthened wrappers around the
   concrete equalities: common dimension is explicit in every wrapper, and
   generation/logit wrappers exclude the empty-vocabulary default branch. -/
theorem palomarIncrementalModernDecoderRefinesFull
    {modelDim : Nat} {layers : List ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {caches : ModernTransformerCache} {x : Vector ℝ}
    (hwellformed : palomarModernStackWellFormed modelDim layers)
    (hmatch : modernTransformerCacheMatches layers start pref caches) :
    (cachedModernDecoderStackStep layers (start + pref.length) x caches).1 =
      (fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD
        ([] : Vector ℝ) := by
  sorry

theorem palomarModernGreedyGenerateStepsRefinesFull {modelDim n : Nat}
    {layers : List ModernDecoderLayerParameters}
    {embedding : Nat → Vector ℝ} {start vocabularySize : Nat}
    {vocabularyWeights : Matrix ℝ} {state : ModernGenerationState}
    (hwellformed : palomarModernStackWellFormed modelDim layers)
    (hvocabulary : 0 < vocabularySize)
    (hmatch : modernGenerationCacheMatches embedding layers start
      state.1 state.2) :
    (modernGenerateSteps n firstArgmax layers embedding start vocabularySize
      vocabularyWeights state).1 =
      modernFullGenerateSteps n layers embedding start vocabularySize
        vocabularyWeights state.1 := by
  sorry

theorem palomarCachedModernDyadicNextTokenLogitError
    {modelDim vocabularySize p start : Nat}
    {layers : List ModernDecoderLayerParameters}
    {pref : Matrix ℝ} {x : Vector ℝ}
    {caches : ModernTransformerCache} {W : Matrix ℝ}
    (hwellformed : palomarModernStackWellFormed modelDim layers)
    (hvocabulary : 0 < vocabularySize)
    (hcache : modernTransformerCacheMatches layers start pref caches)
    (hmatrix : matrixShape modelDim vocabularySize W) :
    vectorErrorBound (modelDim * dyadicUnitRoundoff p)
      (nextTokenLogits vocabularySize W
        ((fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD
          ([] : Vector ℝ)))
      (dyadicNextTokenLogits p vocabularySize W
        (cachedModernDecoderStackStep layers (start + pref.length) x caches).1) := by
  sorry

end
end DecoderTransformer
