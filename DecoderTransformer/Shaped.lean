import DecoderTransformer.Cache
import Mathlib.Tactic

namespace DecoderTransformer

/-!
# Finite shape-safe tensors

Vectors, matrices, and rank-three tensors are represented by nested lists plus
explicit shape predicates.  The predicates, rather than the host language's
partial indexing notation, carry the dimensions needed by the later attention
and decoder proofs.
-/

abbrev Vector (α : Type*) := List α
abbrev Matrix (α : Type*) := List (List α)
abbrev Tensor3 (α : Type*) := List (List (List α))

def vectorShape (n : Nat) (xs : Vector α) : Prop :=
  xs.length = n

def matrixShape (rows cols : Nat) (M : Matrix α) : Prop :=
  M.length = rows ∧ ∀ row ∈ M, row.length = cols

def tensor3Shape (d₁ d₂ d₃ : Nat) (T : Tensor3 α) : Prop :=
  T.length = d₁ ∧ ∀ M ∈ T, matrixShape d₂ d₃ M

theorem vectorShape_length {n : Nat} {xs : Vector α}
    (h : vectorShape n xs) : xs.length = n := h

theorem matrixShape_length {rows cols : Nat} {M : Matrix α}
    (h : matrixShape rows cols M) : M.length = rows := h.1

theorem matrixShape_row {rows cols : Nat} {M : Matrix α} {row : List α}
    (h : matrixShape rows cols M) (hrow : row ∈ M) : row.length = cols :=
  h.2 row hrow

theorem matrixShape_nth {rows cols : Nat} {M : Matrix α} {i : Nat}
    (h : matrixShape rows cols M) (hi : i < rows) :
    (M[i]'(by simpa [h.1] using hi)).length = cols := by
  apply matrixShape_row h
  exact List.getElem_mem (by simpa [h.1] using hi)

def vectorAdd [Add α] (xs ys : Vector α) : Vector α :=
  List.zipWith (· + ·) xs ys

theorem vectorAdd_shape [Add α] {n : Nat} {xs ys : Vector α}
    (hx : vectorShape n xs) (hy : vectorShape n ys) :
    vectorShape n (vectorAdd xs ys) := by
  change (List.zipWith (· + ·) xs ys).length = n
  rw [List.length_zipWith, hx, hy]
  simp

def matrixAdd [Add α] (A B : Matrix α) : Matrix α :=
  List.zipWith vectorAdd A B

theorem matrixAdd_shape [Add α] {rows cols : Nat} {A B : Matrix α}
    (hA : matrixShape rows cols A) (hB : matrixShape rows cols B) :
    matrixShape rows cols (matrixAdd A B) := by
  have hlenA : A.length = rows := hA.1
  have hlenB : B.length = rows := hB.1
  subst rows
  induction A generalizing B with
  | nil => cases B <;> simp_all [matrixAdd, matrixShape]
  | cons a A ih =>
      cases B with
      | nil => simp_all [matrixAdd, matrixShape]
      | cons b B =>
          have ha : a.length = cols := hA.2 a (by simp)
          have hb : b.length = cols := hB.2 b (by simp)
          have hAt : matrixShape A.length cols A := by
            refine ⟨rfl, ?_⟩
            intro row hrow
            exact hA.2 row (by simp [hrow])
          have hBt : matrixShape B.length cols B := by
            refine ⟨rfl, ?_⟩
            intro row hrow
            exact hB.2 row (by simp [hrow])
          simp only [matrixAdd, List.zipWith]
          refine ⟨?_, ?_⟩
          · have hlenBt : B.length = A.length := by simpa using hlenB
            simp only [List.length_cons]
            rw [List.length_zipWith]
            rw [hlenBt]
            simp
          intro row hrow
          simp only [List.mem_cons] at hrow
          rcases hrow with rfl | hrow
          · exact vectorAdd_shape (n := cols)
              (by simpa [vectorShape] using ha)
              (by simpa [vectorShape] using hb)
          · have hlenBt : B.length = A.length := by simpa using hlenB
            have hBt' : matrixShape A.length cols B := by
              simpa [hlenBt] using hBt
            exact (ih hAt hBt' hlenBt).2 row hrow

def nthOrZero [Zero α] : List α → Nat → α
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nthOrZero xs n

def dotProduct [Mul α] [AddMonoid α] (xs ys : Vector α) : α :=
  (List.zipWith (· * ·) xs ys).sum

def matrixColumns [Zero α] (cols : Nat) (M : Matrix α) : Matrix α :=
  (List.range cols).map (fun j => M.map (fun row => nthOrZero row j))

theorem matrixColumns_shape [Zero α] {rows cols : Nat} {M : Matrix α}
    (h : matrixShape rows cols M) :
    matrixShape cols rows (matrixColumns cols M) := by
  refine ⟨by simp [matrixColumns], ?_⟩
  intro column hcolumn
  simp only [matrixColumns, List.mem_map, List.mem_range] at hcolumn
  obtain ⟨j, hj, rfl⟩ := hcolumn
  simp [h.1]

def matrixMultiply [Mul α] [AddMonoid α]
    (outCols : Nat) (A B : Matrix α) : Matrix α :=
  A.map (fun row => (matrixColumns outCols B).map (dotProduct row))

theorem matrixMultiply_shape [Mul α] [AddMonoid α]
    {rows inner cols : Nat} {A B : Matrix α}
    (hA : matrixShape rows inner A) (hB : matrixShape inner cols B) :
    matrixShape rows cols (matrixMultiply cols A B) := by
  have hcols := matrixColumns_shape hB
  refine ⟨by simp [matrixMultiply, hA.1], ?_⟩
  intro row hrow
  simp only [matrixMultiply, List.mem_map] at hrow
  obtain ⟨source, hsource, rfl⟩ := hrow
  simp [hcols.1]

def linearProject [Mul α] [AddMonoid α]
    (outDim : Nat) (W : Matrix α) (x : Vector α) : Vector α :=
  (matrixColumns outDim W).map (dotProduct x)

theorem linearProject_shape [Mul α] [AddMonoid α]
    {inDim outDim : Nat} {W : Matrix α} {x : Vector α}
    (hW : matrixShape inDim outDim W) (hx : vectorShape inDim x) :
    vectorShape outDim (linearProject outDim W x) := by
  simp [linearProject, vectorShape, (matrixColumns_shape hW).1]

def projectSequence [Mul α] [AddMonoid α]
    (outDim : Nat) (W : Matrix α) (X : Matrix α) : Matrix α :=
  X.map (linearProject outDim W)

theorem projectSequence_shape [Mul α] [AddMonoid α]
    {seqLen inDim outDim : Nat} {W X : Matrix α}
    (hX : matrixShape seqLen inDim X) (hW : matrixShape inDim outDim W) :
    matrixShape seqLen outDim (projectSequence outDim W X) := by
  refine ⟨by simp [projectSequence, hX.1], ?_⟩
  intro row hrow
  simp only [projectSequence, List.mem_map] at hrow
  obtain ⟨source, hsource, rfl⟩ := hrow
  apply linearProject_shape hW
  exact hX.2 source hsource

def splitVector : Nat → Nat → Vector α → Matrix α
  | 0, _, _ => []
  | heads + 1, headDim, xs =>
      xs.take headDim :: splitVector heads headDim (xs.drop headDim)

theorem splitVector_shape {heads headDim : Nat} {xs : Vector α}
    (hxs : xs.length = heads * headDim) :
    matrixShape heads headDim (splitVector heads headDim xs) := by
  induction heads generalizing xs with
  | zero => simp [splitVector, matrixShape]
  | succ heads ih =>
      have hlen : xs.length = heads * headDim + headDim := by
        simpa [Nat.succ_mul, Nat.add_comm] using hxs
      have hhead : headDim ≤ xs.length := by
        rw [hlen]
        omega
      have hdrop : (xs.drop headDim).length = heads * headDim := by
        rw [List.length_drop, hlen]
        omega
      have htail := ih hdrop
      refine ⟨by simp [splitVector, htail.1], ?_⟩
      intro row hrow
      simp only [splitVector, List.mem_cons] at hrow
      rcases hrow with rfl | hrow
      · simp [List.length_take, min_eq_left hhead]
      · exact htail.2 row hrow

theorem concat_splitVector {heads headDim : Nat} {xs : Vector α}
    (hxs : xs.length = heads * headDim) :
    (splitVector heads headDim xs).flatten = xs := by
  induction heads generalizing xs with
  | zero => simpa [splitVector] using hxs
  | succ heads ih =>
      have hlen : xs.length = heads * headDim + headDim := by
        simpa [Nat.succ_mul, Nat.add_comm] using hxs
      have hdrop : (xs.drop headDim).length = heads * headDim := by
        rw [List.length_drop, hlen]
        omega
      have htail := ih hdrop
      simp [splitVector, htail, List.take_append_drop]

theorem concat_rows_length {cols : Nat} {M : Matrix α}
    (hrows : ∀ row ∈ M, row.length = cols) :
    M.flatten.length = M.length * cols := by
  induction M with
  | nil => simp
  | cons row M ih =>
      have hrow := hrows row (by simp)
      have htail : ∀ r ∈ M, r.length = cols := by
        intro r hr
        exact hrows r (by simp [hr])
      simp [ih htail, hrow, Nat.succ_mul, Nat.add_comm]

theorem matrixShape_concat_length {rows cols : Nat} {M : Matrix α}
    (h : matrixShape rows cols M) :
    M.flatten.length = rows * cols :=
  concat_rows_length h.2 |>.trans (by rw [h.1])

def splitSequenceHeads (heads headDim : Nat) (X : Matrix α) : Tensor3 α :=
  X.map (splitVector heads headDim)

theorem tensor3Shape_splitSequenceHeads {seqLen heads headDim : Nat} {X : Matrix α}
    (hX : matrixShape seqLen (heads * headDim) X) :
    tensor3Shape seqLen heads headDim (splitSequenceHeads heads headDim X) := by
  refine ⟨by simp [splitSequenceHeads, hX.1], ?_⟩
  intro M hM
  simp only [splitSequenceHeads, List.mem_map] at hM
  obtain ⟨row, hrow, rfl⟩ := hM
  exact splitVector_shape (hX.2 row hrow)

def concatSequenceHeads (T : Tensor3 α) : Matrix α :=
  T.map List.flatten

theorem concatSequenceHeads_shape {seqLen heads headDim : Nat} {T : Tensor3 α}
    (hT : tensor3Shape seqLen heads headDim T) :
    matrixShape seqLen (heads * headDim) (concatSequenceHeads T) := by
  refine ⟨by simp [concatSequenceHeads, hT.1], ?_⟩
  intro row hrow
  simp only [concatSequenceHeads, List.mem_map] at hrow
  obtain ⟨M, hM, rfl⟩ := hrow
  have hshape := hT.2 M hM
  exact matrixShape_concat_length hshape

theorem concat_splitSequenceHeads {seqLen heads headDim : Nat} {X : Matrix α}
    (hX : matrixShape seqLen (heads * headDim) X) :
    concatSequenceHeads (splitSequenceHeads heads headDim X) = X := by
  induction X generalizing seqLen with
  | nil => simp [concatSequenceHeads, splitSequenceHeads]
  | cons row X ih =>
      have hrow : row.length = heads * headDim := hX.2 row (by simp)
      have htail : matrixShape X.length (heads * headDim) X := by
        refine ⟨rfl, ?_⟩
        intro r hr
        exact hX.2 r (by simp [hr])
      have htail_eq :
          (X.map (splitVector heads headDim)).map List.flatten = X :=
        ih htail
      change
        (splitVector heads headDim row).flatten ::
            (X.map (splitVector heads headDim)).map List.flatten = row :: X
      rw [concat_splitVector hrow, htail_eq]

end DecoderTransformer
