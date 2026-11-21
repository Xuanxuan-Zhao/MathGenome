import MathGenome.Internal.Specs.D05.M08.Coefficients.DeterminantDerivative
import MathGenome.Internal.D05.M05.Adjugate
import MathGenome.Internal.D05.Foundations.DifferentiationTaylor

/-! Formal differentiation of the determinant, independent of characteristic
coefficient recurrences, Newton identities, and exterior powers. -/

noncomputable section

namespace D05.M08.Coefficients.DeterminantDerivative

open scoped BigOperators
open Polynomial

/-- Row-indexed version of the Leibniz expansion. -/
private lemma det_rows {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) :
    M.det = ∑ σ : Equiv.Perm ι,
      (↑(↑(Equiv.Perm.sign σ) : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose M, Matrix.det_apply']
  rfl

/-- Differentiate each row in turn in the Leibniz expansion.
This is a formal identity over an arbitrary commutative ring. -/
lemma derivative_det {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) :
    derivative M.det =
      ∑ i, (M.updateRow i (fun j => derivative (M i j))).det := by
  rw [det_rows, map_sum]
  simp_rw [derivative_mul, derivative_intCast, zero_mul, zero_add,
    derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [det_rows]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [Matrix.updateRow_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj)]

/-- The formal derivative of `det (XI+A)` is the trace of its actual
cofactor adjugate. This includes size one and fields of positive characteristic. -/
theorem determinant_derivative :
    Specs.D05.M08.Coefficients.DeterminantDerivative.determinant_derivative := by
  intro K _ n _hn A
  rw [D05.M05.DetDefinition.matrix_det_bridge,
    D05.M05.Adjugate.matrix_adjugate_bridge, derivative_det]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, Matrix.adjugate_apply]
  have hrow : (fun j => derivative
      ((Matrix.scalar (Fin n) (X : K[X]) + A.map C) i j)) = Pi.single i 1 := by
    funext j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar, Matrix.diagonal]
    · simp [Matrix.scalar, Matrix.diagonal, hij, Ne.symm hij]
  rw [hrow]

end D05.M08.Coefficients.DeterminantDerivative
