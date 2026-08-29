import DecoderTransformer.Decoding
import DecoderTransformer.Incremental
import Mathlib.Data.List.GetD
import Mathlib.Tactic

namespace DecoderTransformer

noncomputable section

/-!
# Modern grouped-query decoder and incremental caches

This is the modern branch: grouped-query attention, rotary positions, SwiGLU,
and a cache indexed by KV heads.  The cache relation is represented as
equality with the projected indexed prefix and makes the refinement proofs
executable in Lean's totalized list API.
-/

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
  let x := ix.2
  let attention := modernGroupedAttentionAtPrefix p ix pref
  let attentionResidual := vectorAdd x attention
  let mlpInput := rmsNorm p.normEpsilon p.mlpGain attentionResidual
  let mlp := swiglu p.modelDim p.hiddenDim p.gateWeights p.upWeights
    p.downWeights mlpInput
  vectorAdd attentionResidual mlp

def fullModernDecoderLayer (p : ModernDecoderLayerParameters) (start : Nat)
    (X : Matrix ℝ) : Matrix ℝ :=
  causalAttention id id id
    (fun ix pref _ => modernDecoderAtIndexedPrefix p ix pref)
    (indexedSequence start X)

@[simp] theorem length_fullModernDecoderLayer
    (p : ModernDecoderLayerParameters) (start : Nat) (X : Matrix ℝ) :
    (fullModernDecoderLayer p start X).length = X.length := by
  simp [fullModernDecoderLayer, length_causalAttention,
    indexedSequence]

theorem fullModernDecoderLayer_append (p : ModernDecoderLayerParameters)
    (start : Nat) (pref : Matrix ℝ) (x : Vector ℝ) :
    fullModernDecoderLayer p start (pref ++ [x]) =
      fullModernDecoderLayer p start pref ++
        [modernDecoderAtIndexedPrefix p (start + pref.length, x)
          (indexedSequence start (pref ++ [x]))] := by
  have hindexed := indexedSequence_append_singleton start pref x
  have happ := causalAttention_append id id id
    (fun ix pref _ => modernDecoderAtIndexedPrefix p ix pref)
    (indexedSequence start pref) [(start + pref.length, x)]
  simp [fullModernDecoderLayer, hindexed, happ, causalAttentionFrom]

def modernGroupedParametersShape (p : ModernDecoderLayerParameters) : Prop :=
  groupedQueryParametersShape p.queryHeadCount p.kvHeadCount p.modelDim
    p.headDim p.queryWeights p.keyWeights p.valueWeights p.outputWeights

theorem validModernAttentionShape {p : ModernDecoderLayerParameters}
    (hvalid : validModernDecoderLayer p) (ix : Nat × Vector ℝ)
    (pref : List (Nat × Vector ℝ)) :
    vectorShape p.modelDim (modernGroupedAttentionAtPrefix p ix pref) := by
  have hparams : modernGroupedParametersShape p := by
    rcases hvalid with ⟨hq, hkv, hmodel, hhead, hhidden, hdim, hdiv,
      heps, hgain, hmlp, hqW, hkW, hvW, hOW, hgate, hup, hdown, hrope⟩
    exact ⟨hq, hkv, hdiv, hqW, hkW, hvW, hOW⟩
  unfold modernGroupedAttentionAtPrefix
  have hWO : matrixShape (p.queryHeadCount * p.headDim)
      p.modelDim p.outputWeights := hparams.2.2.2.2.2.2
  apply linearProject_shape hWO
  have hrows : ∀ row ∈ (List.range p.queryHeadCount).map (fun h =>
      let g := groupedQueryHeadIndex p.queryHeadCount p.kvHeadCount h
      exactAttention p.headDim p.headDim
        (modernQueryAt p h ix.1 ix.2)
        (pref.map (fun jx => modernKeyAt p g jx.1 jx.2))
        (pref.map (fun jx => modernValueAt p g jx.2))),
      row.length = p.headDim := by
    intro row hrow
    rcases List.mem_map.1 hrow with ⟨h, hh, rfl⟩
    exact vectorShape_length (exactAttention_shape _ _ _ _ _)
  simpa [vectorShape] using (concat_rows_length hrows)

theorem validModernDecoderAtPrefixShape
    {p : ModernDecoderLayerParameters} (hvalid : validModernDecoderLayer p)
    {ix : Nat × Vector ℝ} {pref : List (Nat × Vector ℝ)}
    (hinput : vectorShape p.modelDim ix.2) :
    vectorShape p.modelDim
      (modernDecoderAtIndexedPrefix p ix pref) := by
  have hatt := validModernAttentionShape hvalid ix pref
  have hres := vectorAdd_shape hinput hatt
  rcases hvalid with ⟨hq, hkv, hmodel, hhead, hhidden, hdim, hdiv,
    heps, hgain, hmlpgain, hqW, hkW, hvW, hOW, hgate, hup, hdown, hrope⟩
  have hnorm := rmsNorm_shape (epsilon := p.normEpsilon) hmlpgain hres
  have hmlp := swiglu_shape hnorm hgate hup hdown
  simpa [modernDecoderAtIndexedPrefix] using vectorAdd_shape hres hmlp

theorem validFullModernDecoderLayerShape
    {p : ModernDecoderLayerParameters} (hvalid : validModernDecoderLayer p)
    {start seqLen : Nat} {X : Matrix ℝ}
    (hinput : matrixShape seqLen p.modelDim X) :
    matrixShape seqLen p.modelDim (fullModernDecoderLayer p start X) := by
  have hrows : ∀ ix ∈ indexedSequence start X,
      vectorShape p.modelDim ix.2 := by
    intro ix hix
    have hsnd : ix.2 ∈ (indexedSequence start X).map Prod.snd :=
      List.mem_map.2 ⟨ix, hix, rfl⟩
    have hsnd' : ix.2 ∈ X := by
      simpa [indexedSequence_snd] using hsnd
    exact hinput.2 _ hsnd'
  have hfrom : ∀ (pref xs : List (Nat × Vector ℝ)),
      (∀ ix ∈ xs, vectorShape p.modelDim ix.2) →
      matrixShape xs.length p.modelDim
        (causalAttentionFrom id id id
          (fun ix pref _ => modernDecoderAtIndexedPrefix p ix pref)
          pref xs) := by
    intro pref xs
    induction xs generalizing pref with
    | nil =>
        intro hrows
        exact ⟨rfl, by intro row hrow; cases hrow⟩
    | cons ix xs ih =>
        intro hrows
        have hhead := validModernDecoderAtPrefixShape (pref := pref ++ [ix]) hvalid
          (hrows ix (by simp))
        have htail := ih (pref := pref ++ [ix]) (by
          intro jx hjx
          exact hrows jx (by simp [hjx]))
        have hlen := length_causalAttentionFrom id id id
          (fun ix pref _ => modernDecoderAtIndexedPrefix p ix pref)
          pref (ix :: xs)
        refine ⟨by simpa using hlen, ?_⟩
        intro row hrow
        simp only [causalAttentionFrom, List.mem_cons] at hrow
        rcases hrow with rfl | hrow
        · simpa using vectorShape_length hhead
        · exact htail.2 row hrow
  have hresult := hfrom [] (indexedSequence start X) hrows
  simpa [fullModernDecoderLayer, causalAttention, hinput.1,
    indexedSequence] using hresult

def fullModernDecoderStack : List ModernDecoderLayerParameters → Nat →
    Matrix ℝ → Matrix ℝ
  | [], start, X => X
  | p :: ps, start, X =>
      fullModernDecoderStack ps start (fullModernDecoderLayer p start X)

def validModernDecoderStack
    (layers : List ModernDecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validModernDecoderLayer p

def modernDecoderStackCompatible (modelDim : Nat)
    (layers : List ModernDecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validModernDecoderLayer p ∧ p.modelDim = modelDim

theorem compatibleFullModernDecoderStackShape
    {modelDim seqLen start : Nat} {layers : List ModernDecoderLayerParameters}
    {X : Matrix ℝ} (hcompatible : modernDecoderStackCompatible modelDim layers)
    (hinput : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim (fullModernDecoderStack layers start X) := by
  induction layers generalizing X with
  | nil => simpa [fullModernDecoderStack] using hinput
  | cons p ps ih =>
      have hp := hcompatible p (by simp)
      have hps : modernDecoderStackCompatible modelDim ps := by
        intro q hq
        exact hcompatible q (by simp [hq])
      have hinput' : matrixShape seqLen p.modelDim X := by
        simpa [hp.2] using hinput
      have hlayer := validFullModernDecoderLayerShape hp.1
        (start := start) hinput'
      have hlayer' : matrixShape seqLen modelDim
          (fullModernDecoderLayer p start X) := by
        simpa [hp.2] using hlayer
      exact ih hps hlayer'

abbrev ModernLayerCache := List (KVCache (Vector ℝ) (Vector ℝ))
abbrev ModernTransformerCache := List ModernLayerCache

def modernLayerCacheOf (p : ModernDecoderLayerParameters) (start : Nat)
    (pref : Matrix ℝ) : ModernLayerCache :=
  (List.range p.kvHeadCount).map (fun g =>
    cacheOf (fun ix : Nat × Vector ℝ => modernKeyAt p g ix.1 ix.2)
      (fun ix : Nat × Vector ℝ => modernValueAt p g ix.2)
      (indexedSequence start pref))

def modernLayerCacheMatches (p : ModernDecoderLayerParameters) (start : Nat)
    (pref : Matrix ℝ) (cache : ModernLayerCache) : Prop :=
  cache = modernLayerCacheOf p start pref

def emptyModernLayerCache (p : ModernDecoderLayerParameters) : ModernLayerCache :=
  List.replicate p.kvHeadCount emptyCache

theorem emptyModernLayerCache_matches (p : ModernDecoderLayerParameters)
    (start : Nat) : modernLayerCacheMatches p start []
      (emptyModernLayerCache p) := by
  unfold modernLayerCacheMatches emptyModernLayerCache modernLayerCacheOf
  have hconst : ∀ n : Nat,
      (List.range n).map (fun _ => (emptyCache : KVCache (Vector ℝ) (Vector ℝ))) =
        List.replicate n emptyCache := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp [ih]
  rw [← hconst p.kvHeadCount]
  apply List.map_congr_left
  intro g hg
  simp [cacheOf, indexedSequence, emptyCache]

def modernExtendHeadCache (p : ModernDecoderLayerParameters) (g position : Nat)
    (x : Vector ℝ) (cache : KVCache (Vector ℝ) (Vector ℝ)) :
    KVCache (Vector ℝ) (Vector ℝ) :=
  ⟨cache.keys ++ [modernKeyAt p g position x],
   cache.values ++ [modernValueAt p g x]⟩

def modernExtendLayerCache (p : ModernDecoderLayerParameters) (position : Nat)
    (x : Vector ℝ) (cache : ModernLayerCache) : ModernLayerCache :=
  (List.range p.kvHeadCount).map (fun g =>
    modernExtendHeadCache p g position x (cache.getD g emptyCache))

theorem modernGetDMapRange {β : Type*} (f : Nat → β) (d : β)
    {n i : Nat} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD, List.getElem?_map]
  have hget : (List.range n)[i]? = some i := by
    rw [List.getElem?_eq_getElem (by simp [hi]), List.getElem_range]
  rw [hget]
  rfl

theorem modernExtendLayerCache_nth
    {p : ModernDecoderLayerParameters} {position : Nat}
    {x : Vector ℝ} {cache : ModernLayerCache} {g : Nat}
    (hg : g < p.kvHeadCount) :
    (modernExtendLayerCache p position x cache).getD g emptyCache =
      modernExtendHeadCache p g position x (cache.getD g emptyCache) := by
  unfold modernExtendLayerCache
  rw [List.getD, List.getElem?_map]
  have hget : (List.range p.kvHeadCount)[g]? = some g := by
    rw [List.getElem?_eq_getElem (by simp [hg]), List.getElem_range]
  rw [hget]
  rfl

theorem modernExtendLayerCache_matches
    {p : ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {cache : ModernLayerCache} {x : Vector ℝ}
    (hcache : modernLayerCacheMatches p start pref cache) :
    modernLayerCacheMatches p start (pref ++ [x])
      (modernExtendLayerCache p (start + pref.length) x cache) := by
  subst cache
  unfold modernLayerCacheMatches modernExtendLayerCache modernLayerCacheOf
  apply List.map_congr_left
  intro g hg
  have hlt : g < p.kvHeadCount := List.mem_range.1 hg
  have hcacheg := modernGetDMapRange
    (fun k => cacheOf (fun ix : Nat × Vector ℝ => modernKeyAt p k ix.1 ix.2)
      (fun ix : Nat × Vector ℝ => modernValueAt p k ix.2)
      (indexedSequence start pref)) emptyCache hlt
  rw [hcacheg]
  simp [modernExtendHeadCache, indexedSequence_append_singleton,
    cacheOf, List.map_append, modernKeyAt, modernValueAt]

def cachedModernGroupedAttention (p : ModernDecoderLayerParameters)
    (position : Nat) (x : Vector ℝ) (cache : ModernLayerCache) : Vector ℝ :=
  linearProject p.modelDim p.outputWeights
    ((List.range p.queryHeadCount).map (fun h =>
      let g := groupedQueryHeadIndex p.queryHeadCount p.kvHeadCount h
      let entry := cache.getD g emptyCache
      exactAttention p.headDim p.headDim
        (modernQueryAt p h position x) entry.keys entry.values)).flatten

theorem cachedModernGroupedAttention_correct
    {p : ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {cache : ModernLayerCache} {x : Vector ℝ}
    (hvalid : validModernDecoderLayer p)
    (hcache : modernLayerCacheMatches p start pref cache) :
    cachedModernGroupedAttention p (start + pref.length) x
        (modernExtendLayerCache p (start + pref.length) x cache) =
      modernGroupedAttentionAtPrefix p (start + pref.length, x)
        (indexedSequence start (pref ++ [x])) := by
  subst cache
  have hq : 0 < p.queryHeadCount := hvalid.1
  have hkv : 0 < p.kvHeadCount := hvalid.2.1
  rcases hvalid with ⟨hq, hkv, hmodel, hhead, hhidden, hdim, hdiv,
    heps, hgain, hmlp, hqW, hkW, hvW, hOW, hgate, hup, hdown, hrope⟩
  unfold cachedModernGroupedAttention modernGroupedAttentionAtPrefix
  apply congrArg (linearProject p.modelDim p.outputWeights)
  apply congrArg List.flatten
  apply List.map_congr_left
  intro h hh
  have hhead : h < p.queryHeadCount := List.mem_range.1 hh
  let g := groupedQueryHeadIndex p.queryHeadCount p.kvHeadCount h
  have hg : g < p.kvHeadCount := groupedQueryHeadIndex_bound hq hkv hdiv hhead
  have hnew :
      (modernExtendLayerCache p (start + pref.length) x
        (modernLayerCacheOf p start pref)).getD g emptyCache =
        modernExtendHeadCache p g (start + pref.length) x
          (cacheOf (fun ix : Nat × Vector ℝ => modernKeyAt p g ix.1 ix.2)
            (fun ix : Nat × Vector ℝ => modernValueAt p g ix.2)
            (indexedSequence start pref)) := by
    rw [modernExtendLayerCache_nth hg]
    unfold modernLayerCacheOf
    rw [modernGetDMapRange _ _ hg]
  change exactAttention p.headDim p.headDim (modernQueryAt p h
      (start + pref.length) x)
      ((modernExtendLayerCache p (start + pref.length) x
        (modernLayerCacheOf p start pref)).getD g emptyCache).keys
      ((modernExtendLayerCache p (start + pref.length) x
        (modernLayerCacheOf p start pref)).getD g emptyCache).values =
    exactAttention p.headDim p.headDim (modernQueryAt p h
      (start + pref.length) x)
      ((indexedSequence start (pref ++ [x])).map
        (fun jx => modernKeyAt p g jx.1 jx.2))
      ((indexedSequence start (pref ++ [x])).map
        (fun jx => modernValueAt p g jx.2))
  rw [hnew]
  simp [modernExtendHeadCache, cacheOf,
    indexedSequence_append_singleton, modernKeyAt, modernValueAt]

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

theorem cachedModernDecoderLayerStep_correct
    {p : ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {cache : ModernLayerCache} {x : Vector ℝ}
    (hvalid : validModernDecoderLayer p)
    (hcache : modernLayerCacheMatches p start pref cache) :
    (cachedModernDecoderLayerStep p (start + pref.length) x cache).1 =
        modernDecoderAtIndexedPrefix p (start + pref.length, x)
          (indexedSequence start (pref ++ [x])) ∧
      modernLayerCacheMatches p start (pref ++ [x])
        (cachedModernDecoderLayerStep p (start + pref.length) x cache).2 := by
  have hatt := cachedModernGroupedAttention_correct (p := p) (start := start)
    (pref := pref) (cache := cache) (x := x) hvalid hcache
  have hext := modernExtendLayerCache_matches
    (p := p) (start := start) (pref := pref) (cache := cache) (x := x) hcache
  constructor
  · simpa [cachedModernDecoderLayerStep, modernDecoderAtIndexedPrefix]
      using congrArg (fun a =>
        vectorAdd (vectorAdd x a)
          (swiglu p.modelDim p.hiddenDim p.gateWeights p.upWeights
            p.downWeights
            (rmsNorm p.normEpsilon p.mlpGain (vectorAdd x a)))) hatt
  · simpa [cachedModernDecoderLayerStep] using hext

theorem cachedModernDecoderLayerStep_full
    {p : ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {cache : ModernLayerCache} {x : Vector ℝ}
    (hvalid : validModernDecoderLayer p)
    (hcache : modernLayerCacheMatches p start pref cache) :
    fullModernDecoderLayer p start (pref ++ [x]) =
      fullModernDecoderLayer p start pref ++
        [(cachedModernDecoderLayerStep p (start + pref.length) x cache).1] := by
  rw [fullModernDecoderLayer_append]
  rw [(cachedModernDecoderLayerStep_correct hvalid hcache).1]

def validModernStack (layers : List ModernDecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validModernDecoderLayer p

def modernStackCompatible (modelDim : Nat)
    (layers : List ModernDecoderLayerParameters) : Prop :=
  ∀ p ∈ layers, validModernDecoderLayer p ∧ p.modelDim = modelDim

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

theorem compatibleFullModernStackShape
    {modelDim seqLen start : Nat}
    {layers : List ModernDecoderLayerParameters} {X : Matrix ℝ}
    (hcompatible : modernStackCompatible modelDim layers)
    (hinput : matrixShape seqLen modelDim X) :
    matrixShape seqLen modelDim (fullModernDecoderStack layers start X) := by
  induction layers generalizing X with
  | nil => simpa [fullModernDecoderStack] using hinput
  | cons p ps ih =>
      have hp := hcompatible p (by simp)
      have hps : modernStackCompatible modelDim ps := by
        intro q hq
        exact hcompatible q (by simp [hq])
      have hx : matrixShape seqLen p.modelDim X := by
        simpa [hp.2] using hinput
      have hl := validFullModernDecoderLayerShape (start := start) hp.1 hx
      have hl' : matrixShape seqLen modelDim
          (fullModernDecoderLayer p start X) := by
        simpa [hp.2] using hl
      exact ih hps hl'

theorem cachedModernDecoderStackStep_correct
    {layers : List ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {caches : ModernTransformerCache} {x : Vector ℝ}
    (hvalid : validModernStack layers)
    (hmatch : modernTransformerCacheMatches layers start pref caches) :
    fullModernDecoderStack layers start (pref ++ [x]) =
        fullModernDecoderStack layers start pref ++
          [(cachedModernDecoderStackStep layers (start + pref.length)
            x caches).1] ∧
      modernTransformerCacheMatches layers start (pref ++ [x])
        (cachedModernDecoderStackStep layers (start + pref.length)
          x caches).2 := by
  induction layers generalizing pref caches x with
  | nil =>
      cases caches with
      | nil =>
          constructor
          · rfl
          · simp [modernTransformerCacheMatches, cachedModernDecoderStackStep]
      | cons cache rest => simp [modernTransformerCacheMatches] at hmatch
  | cons p ps ih =>
      cases caches with
      | nil => simp [modernTransformerCacheMatches] at hmatch
      | cons cache rest =>
          have hp : validModernDecoderLayer p := hvalid p (by simp)
          have hps : validModernStack ps := by
            intro q hq
            exact hvalid q (by simp [hq])
          have hpcache := hmatch.1
          have hrest := hmatch.2
          let position := start + pref.length
          let layerStep := cachedModernDecoderLayerStep p position x cache
          have hlayer := cachedModernDecoderLayerStep_correct
            (p := p) (start := start) (pref := pref) (cache := cache)
            (x := x) hp hpcache
          have hstack := ih (pref := fullModernDecoderLayer p start pref)
            (caches := rest) (x := layerStep.1) hps hrest
          have hout : layerStep.1 =
              modernDecoderAtIndexedPrefix p (position, x)
                (indexedSequence start (pref ++ [x])) := hlayer.1
          have hfull := fullModernDecoderLayer_append p start pref x
          have hstackOut :
              fullModernDecoderStack ps start
                (fullModernDecoderLayer p start pref ++ [layerStep.1]) =
                fullModernDecoderStack ps start
                  (fullModernDecoderLayer p start pref) ++
                  [(cachedModernDecoderStackStep ps position
                    layerStep.1 rest).1] := by
            simpa [position, length_fullModernDecoderLayer] using hstack.1
          have hstackCache :
              modernTransformerCacheMatches ps start
                (fullModernDecoderLayer p start pref ++ [layerStep.1])
                (cachedModernDecoderStackStep ps position
                  layerStep.1 rest).2 := by
            simpa [position, length_fullModernDecoderLayer] using hstack.2
          constructor
          · change fullModernDecoderStack ps start
                (fullModernDecoderLayer p start (pref ++ [x])) =
              fullModernDecoderStack ps start
                (fullModernDecoderLayer p start pref) ++
                [(cachedModernDecoderStackStep ps position layerStep.1 rest).1]
            rw [hfull, ← hout]
            exact hstackOut
          · change modernLayerCacheMatches p start (pref ++ [x]) layerStep.2 ∧
              modernTransformerCacheMatches ps start
                (fullModernDecoderLayer p start (pref ++ [x]))
                (cachedModernDecoderStackStep ps position layerStep.1 rest).2
            constructor
            · exact hlayer.2
            · rw [hfull, ← hout]
              exact hstackCache

theorem incremental_modern_decoder_equals_full
    {layers : List ModernDecoderLayerParameters} {start : Nat}
    {pref : Matrix ℝ} {caches : ModernTransformerCache} {x : Vector ℝ}
    (hvalid : validModernStack layers)
    (hmatch : modernTransformerCacheMatches layers start pref caches) :
    (cachedModernDecoderStackStep layers (start + pref.length) x caches).1 =
      (fullModernDecoderStack layers start (pref ++ [x])).getLast?.getD
        ([] : Vector ℝ) := by
  have h := (cachedModernDecoderStackStep_correct
    (layers := layers) (start := start) (pref := pref) (caches := caches)
    (x := x) hvalid hmatch).1
  have hlast := congrArg
    (fun z : Matrix ℝ => z.getLast?.getD ([] : Vector ℝ)) h
  simpa using hlast.symm

def emptyModernTransformerCache
    (layers : List ModernDecoderLayerParameters) : ModernTransformerCache :=
  layers.map emptyModernLayerCache

@[simp] theorem fullModernDecoderLayer_empty
    (p : ModernDecoderLayerParameters) (start : Nat) :
    fullModernDecoderLayer p start [] = [] := by
  have h := length_causalAttention id id id
    (fun ix pref _ => modernDecoderAtIndexedPrefix p ix pref)
    (indexedSequence start ([] : Matrix ℝ))
  simpa [fullModernDecoderLayer, indexedSequence] using h

@[simp] theorem fullModernDecoderStack_empty
    (layers : List ModernDecoderLayerParameters) (start : Nat) :
    fullModernDecoderStack layers start [] = [] := by
  induction layers with
  | nil => simp [fullModernDecoderStack]
  | cons p ps ih => simp [fullModernDecoderStack, ih]

theorem emptyModernTransformerCache_matches
    (layers : List ModernDecoderLayerParameters) (start : Nat) :
    modernTransformerCacheMatches layers start []
      (emptyModernTransformerCache layers) := by
  induction layers with
  | nil => simp [emptyModernTransformerCache, modernTransformerCacheMatches]
  | cons p ps ih =>
      change modernLayerCacheMatches p start [] (emptyModernLayerCache p) ∧
        modernTransformerCacheMatches ps start (fullModernDecoderLayer p start [])
          (emptyModernTransformerCache ps)
      constructor
      · exact emptyModernLayerCache_matches p start
      · simpa using ih

def cachedModernDecoderStackRun (layers : List ModernDecoderLayerParameters)
    (position : Nat) (caches : ModernTransformerCache) (xs : Matrix ℝ) :
    Matrix ℝ × ModernTransformerCache :=
  match xs with
  | [] => ([], caches)
  | x :: rest =>
      let step := cachedModernDecoderStackStep layers position x caches
      let tail := cachedModernDecoderStackRun layers (position + 1) step.2 rest
      (step.1 :: tail.1, tail.2)

theorem cachedModernDecoderStackRun_correct
    {layers : List ModernDecoderLayerParameters} {start position : Nat}
    {pref : Matrix ℝ} {caches : ModernTransformerCache} {xs : Matrix ℝ}
    (hvalid : validModernStack layers)
    (hmatch : modernTransformerCacheMatches layers start pref caches)
    (hposition : position = start + pref.length) :
    fullModernDecoderStack layers start (pref ++ xs) =
        fullModernDecoderStack layers start pref ++
          (cachedModernDecoderStackRun layers position caches xs).1 ∧
      modernTransformerCacheMatches layers start (pref ++ xs)
        (cachedModernDecoderStackRun layers position caches xs).2 := by
  induction xs generalizing pref position caches with
  | nil =>
      constructor
      · simp [cachedModernDecoderStackRun]
      · simpa [cachedModernDecoderStackRun] using hmatch
  | cons x xs ih =>
      have hone0 := cachedModernDecoderStackStep_correct (layers := layers)
        (start := start) (pref := pref) (caches := caches) (x := x)
        hvalid hmatch
      have hone :
          fullModernDecoderStack layers start (pref ++ [x]) =
              fullModernDecoderStack layers start pref ++
                [(cachedModernDecoderStackStep layers position x caches).1] ∧
            modernTransformerCacheMatches layers start (pref ++ [x])
              (cachedModernDecoderStackStep layers position x caches).2 := by
        simpa [hposition] using hone0
      have hnext : position + 1 = start + (pref ++ [x]).length := by
        calc
          position + 1 = start + pref.length + 1 := by rw [hposition]
          _ = start + (pref.length + 1) := by omega
          _ = start + (pref ++ [x]).length := by simp
      have htail := ih (pref := pref ++ [x]) (position := position + 1)
        (caches := (cachedModernDecoderStackStep layers position x caches).2)
        hone.2 hnext
      simp only [cachedModernDecoderStackRun]
      constructor
      · rw [show pref ++ x :: xs = (pref ++ [x]) ++ xs by simp,
          htail.1, hone.1]
        simp [List.append_assoc]
      · simpa [List.append_assoc] using htail.2

theorem initializedModernCachedRun_equalsFull
    {layers : List ModernDecoderLayerParameters} (hvalid : validModernStack layers)
    (start : Nat) (xs : Matrix ℝ) :
    (cachedModernDecoderStackRun layers start
      (emptyModernTransformerCache layers) xs).1 =
      fullModernDecoderStack layers start xs := by
  have h := cachedModernDecoderStackRun_correct (layers := layers)
    (start := start) (position := start) (pref := [])
    (caches := emptyModernTransformerCache layers) (xs := xs) hvalid
    (emptyModernTransformerCache_matches layers start) (by simp)
  simpa [fullModernDecoderStack_empty] using h.1.symm

theorem initializedModernCachedRun_cacheInvariant
    {layers : List ModernDecoderLayerParameters} (hvalid : validModernStack layers)
    (start : Nat) (xs : Matrix ℝ) :
    modernTransformerCacheMatches layers start xs
      (cachedModernDecoderStackRun layers start
        (emptyModernTransformerCache layers) xs).2 := by
  have h := cachedModernDecoderStackRun_correct (layers := layers)
    (start := start) (position := start) (pref := [])
    (caches := emptyModernTransformerCache layers) (xs := xs) hvalid
    (emptyModernTransformerCache_matches layers start) (by simp)
  simpa using h.2

end
end DecoderTransformer
