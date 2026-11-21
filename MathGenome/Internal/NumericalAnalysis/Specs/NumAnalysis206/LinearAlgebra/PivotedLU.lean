import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact row-pivoted Gaussian elimination. Cursors are zero based. A skip
advances only the column cursor. Pivots are not normalized. The recursive
multiplier factor permutes each stored multiplier vector by all subsequent
row exchanges; this is the backward assembly of the usual forward update
`L ↦ S L S⁻¹`, including the previously stored columns. -/
noncomputable section
namespace NumAnalysis206.PivotedLU
open NumAnalysis206.MatrixDefinitions
universe u
variable {K : Type u} [Field K] {m n : ℕ}

/-- Permuting rows, with row i selecting old row p i. -/
def permuteRows (p : Equiv.Perm (Fin m)) (A : Mat K m n) : Mat K m n :=
  fun i j => A (p i) j

/-- The actual permutation matrix for this row-selection convention. -/
def permutationMatrix (p : Equiv.Perm (Fin m)) : Mat K m m :=
  fun i j => if j = p i then 1 else 0

/-- The elimination multipliers vanish through the pivot row. -/
def multipliers (A : Mat K m n) (r q : Fin m) (d : Fin n) : Fin m → K :=
  fun i => if r < i then A (Equiv.swap r q i) d / A q d else 0

/-- I + ell e_r^T: the inverse of a simultaneous elimination shear. -/
def store (r : Fin m) (ell : Fin m → K) : Mat K m m :=
  1 + (Matrix.of fun i j => if j = r then ell i else 0)

/-- Swap the chosen row into the pivot row and clear below it. -/
def eliminate (A : Mat K m n) (r q : Fin m) (d : Fin n) : Mat K m n :=
  fun i j => A (Equiv.swap r q i) j - multipliers A r q d i * A q j

/-- The unprocessed rows vanish in the columns before the cursor. -/
def LowerZero (A : Mat K m n) (r c : ℕ) : Prop :=
  ∀ i j, r ≤ i.val → j.val < c → A i j = 0

/-- A finite, actual elimination run. No factorization or echelon conclusion
is assumed. In the pivot constructor the subsequent permutation `p` acts on
the stored multiplier vector, thus also moving old multipliers at later swaps. -/
inductive Run : ℕ → ℕ → Mat K m n → Equiv.Perm (Fin m) → Mat K m m →
    Mat K m n → List (Fin n) → Prop where
  | stop {r c A} (hz : ∀ i : Fin m, r ≤ i.val → ∀ j, A i j = 0) :
      Run r c A (Equiv.refl _) 1 A []
  | skip {r c A p L U ps} (hc : c < n)
      (hz : ∀ i : Fin m, r ≤ i.val → A i ⟨c, hc⟩ = 0)
      (tail : Run r (c + 1) A p L U ps) : Run r c A p L U ps
  | pivot {r c A p L U ps} (hr : r < m) (hc : c < n) (q : Fin m)
      (hq : r ≤ q.val) (hp : A q ⟨c, hc⟩ ≠ 0)
      (tail : Run (r + 1) (c + 1) (eliminate A ⟨r, hr⟩ q ⟨c, hc⟩) p L U ps) :
      Run r c A (p.trans (Equiv.swap ⟨r, hr⟩ q))
        (store ⟨r, hr⟩ (fun i => multipliers A ⟨r, hr⟩ q ⟨c, hc⟩ (p i)) * L)
        U (⟨c, hc⟩ :: ps)
end NumAnalysis206.PivotedLU

namespace Specs.NumAnalysis206.PivotedLU
open _root_.NumAnalysis206.MatrixDefinitions _root_.NumAnalysis206.PivotedLU
universe u
/-- W20, including an actual skipped-column elimination run and the empty case. -/
def exact_pivoted_lu : Prop :=
  ∀ {K : Type u} [Field K] {n : ℕ} (A : Mat K n n),
    ∃ (p : Equiv.Perm (Fin n)) (L U : Mat K n n) (ps : List (Fin n)),
      Run 0 0 A p L U ps ∧
      IsPermutation (permutationMatrix (K := K) p) ∧
      IsUnitLowerTriangular L ∧ IsRowEchelon U ∧ IsUpperTriangular U ∧
      permutationMatrix p * A = L * U
end Specs.NumAnalysis206.PivotedLU
