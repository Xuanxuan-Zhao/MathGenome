import MathGenome.Internal.Specs.D05.M08.CayleyHamilton
import MathGenome.Internal.D05.M05.Adjugate
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M08.Minpoly
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-! Cayley–Hamilton over an arbitrary field, including the zero space.
The library theorem transports the matrix adjugate proof through an algebra
isomorphism. Its matrix proof uses the telescoping identity for evaluation
at noncommuting coefficients, not multiplicativity of arbitrary evaluation.
-/

noncomputable section
namespace D05.M08.CayleyHamilton
open scoped BigOperators

theorem annihilates : Specs.D05.M08.CayleyHamilton.annihilates := by
  intro K V _ _ _ _ T
  exact LinearMap.aeval_self_charpoly T

theorem minpoly_divides_charpoly :
    Specs.D05.M08.CayleyHamilton.minpoly_divides_charpoly := by
  intro K V _ _ _ _ T
  apply (Minpoly.divides_iff_annihilates T _).mpr
  exact (Annihilating.mem_annihilator T _).mpr (annihilates T)

theorem cayley_hamilton : Specs.D05.M08.CayleyHamilton.cayley_hamilton := by
  intro K V _ _ _ _ T
  exact ⟨annihilates T, minpoly_divides_charpoly T⟩

theorem coefficient_sum : Specs.D05.M08.CayleyHamilton.coefficient_sum := by
  intro K V _ _ _ _ T
  rw [← Evaluation.coefficient_sum_of_bound T _ _ (le_of_eq (Charpoly.natDegree T))]
  exact annihilates T

theorem zero_dimension : Specs.D05.M08.CayleyHamilton.zero_dimension := by
  intro K V _ _ _ _ T h
  exact ⟨Charpoly.zero_dimensional T h,
    (Annihilating.zero_dimension T h).1, annihilates T⟩

theorem adjugate_recurrence : Specs.D05.M08.CayleyHamilton.adjugate_recurrence := by
  intro K _ n A j
  let Q := D05.M05.adjugate (Matrix.charmatrix A)
  have h := D05.M05.Adjugate.mul_adjugate (Matrix.charmatrix A)
  rw [D05.M05.DetDefinition.matrix_det_bridge] at h
  have hp := congrArg matPolyEquiv h
  rw [map_mul, Matrix.matPolyEquiv_charmatrix, matPolyEquiv_smul_one] at hp
  have hc := congrArg (fun p => p.coeff j) hp
  dsimp only
  simp only [← matPolyEquiv_coeff_apply]
  change (if j = 0 then 0 else (matPolyEquiv Q).coeff (j - 1)) -
      A * (matPolyEquiv Q).coeff j =
      (Matrix.charpoly A).coeff j • (1 : Matrix (Fin n) (Fin n) K)
  cases j with
  | zero =>
    simpa only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul_zero,
      Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Algebra.algebraMap_eq_smul_one, Q, Matrix.charpoly, ite_true] using hc
  | succ j =>
    simpa only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Algebra.algebraMap_eq_smul_one, Nat.add_sub_cancel, Nat.succ_ne_zero,
      ite_false, Q, Matrix.charpoly] using hc

open Polynomial Matrix in
private theorem adjugate_entry_natDegree_le {K : Type*} [Field K] {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) K)
  (i j : Fin (m+1)) :
  (D05.M05.adjugate (Matrix.charmatrix A) i j).natDegree ≤ m := by
  rw [D05.M05.Adjugate.matrix_adjugate_bridge,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have hm : (Matrix.charmatrix A).submatrix j.succAbove i.succAbove =
      (X : Polynomial K) • ((1 : Matrix (Fin (m+1)) (Fin (m+1)) K).submatrix
        j.succAbove i.succAbove).map C +
      ((-A).submatrix j.succAbove i.succAbove).map C := by
    ext a b
    simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal,
      Matrix.submatrix, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg]
  rw [hm]
  calc
    _ ≤ ((-1 : Polynomial K) ^ (j + i : ℕ)).natDegree +
        (det ((X : Polynomial K) •
          ((1 : Matrix (Fin (m+1)) (Fin (m+1)) K).submatrix
            j.succAbove i.succAbove).map C +
          ((-A).submatrix j.succAbove i.succAbove).map C)).natDegree := natDegree_mul_le
    _ ≤ 0 + m := Nat.add_le_add (by simp)
        (by simpa using (natDegree_det_X_add_C_le
          ((1 : Matrix (Fin (m+1)) (Fin (m+1)) K).submatrix j.succAbove i.succAbove)
          ((-A).submatrix j.succAbove i.succAbove)))
    _ = m := Nat.zero_add m

theorem adjugate_coeff_vanish : Specs.D05.M08.CayleyHamilton.adjugate_coeff_vanish := by
  intro K _ n A j hj
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    ext i l
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((adjugate_entry_natDegree_le A i l).trans_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hj))

theorem adjugate_expansion : Specs.D05.M08.CayleyHamilton.adjugate_expansion := by
  intro K _ n A
  dsimp only
  ext i l k
  simp only [Finset.sum_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k < n
  · simp [hk]
  · have hz := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i l)
      (adjugate_coeff_vanish A k (Nat.le_of_not_gt hk))
    simpa [hk] using hz

end D05.M08.CayleyHamilton
