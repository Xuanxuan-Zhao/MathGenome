import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.MatrixInversion
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseStability
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C02.BilinearRules
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set Filter Topology
open scoped ContDiff BigOperators Matrix.Norms.Frobenius
namespace D04

/-- Smoothness in the Euclidean matrix norm is equivalent to smoothness of
each entry. The reverse direction uses the actual finite matrix expansion. -/
theorem contDiff_matrix_iff_entries {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {m n : ℕ} {r : ℕ∞ω} {f : X → Matrix (Fin m) (Fin n) ℝ} :
    ContDiff ℝ r f ↔ ∀ i j, ContDiff ℝ r (fun x => f x i j) := by
  classical
  constructor
  · intro hf i j
    exact (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp hf
  · intro hf
    have he : f = fun x => ∑ i : Fin m, ∑ j : Fin n,
        f x i j • Matrix.single i j (1 : ℝ) := by
      funext x
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
        Matrix.matrix_eq_sum_single (f x)
    rw [he]
    exact ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hf i j).smul contDiff_const

/-- The determinant is a finite polynomial in the matrix entries. This proof
uses no regularity theorem for matrix inversion. -/
theorem contDiff_matrix_determinant {n : ℕ} (r : ℕ∞ω) :
    ContDiff ℝ r (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := by
  classical
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  exact contDiff_matrix_iff_entries.mp contDiff_id _ _

/-- Every adjugate entry is a determinant with one row replaced by constants.
This gives smoothness also for the empty matrix, without a size restriction. -/
theorem contDiff_matrix_adjugate {n : ℕ} (r : ℕ∞ω) :
    ContDiff ℝ r (fun A : Matrix (Fin n) (Fin n) ℝ => A.adjugate) := by
  classical
  apply contDiff_matrix_iff_entries.mpr
  intro i j
  simp only [Matrix.adjugate_apply]
  apply (contDiff_matrix_determinant r).comp
  apply contDiff_matrix_iff_entries.mpr
  intro k l
  by_cases hk : k = j
  · subst k
    simpa using (contDiff_const : ContDiff ℝ r
      (fun _ : Matrix (Fin n) (Fin n) ℝ => (Pi.single i 1 : Fin n → ℝ) l))
  · simpa only [Matrix.updateRow_ne hk, id_eq] using
      (contDiff_matrix_iff_entries.mp (contDiff_id : ContDiff ℝ r
        (fun A : Matrix (Fin n) (Fin n) ℝ => A)) k l)

theorem matrix_inversion_mapsTo :
    Specs.D04.C04.MatrixInversion.matrix_inversion_mapsToType := by
  intro n A hA
  obtain ⟨u, rfl⟩ := hA
  change IsUnit ((↑u : Matrix (Fin n) (Fin n) ℝ)⁻¹)
  simpa only [Matrix.coe_units_inv] using u⁻¹.isUnit

/-- The algebraic adjugate formula and scalar quotient calculus prove C^∞.
No differentiability of an inverse operation is assumed. -/
theorem matrix_inversion_smooth :
    Specs.D04.C04.MatrixInversion.matrix_inversion_smoothType := by
  intro n
  apply (smoothOn_iff_contDiffOn _ _ (general_linear_open n)).mpr
  have hd : ContDiffOn ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ => A.det⁻¹)
      {A | IsUnit A} := by
    apply (contDiff_matrix_determinant ∞).contDiffOn.inv
    intro A hA
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hi := hd.smul (contDiff_matrix_adjugate ∞).contDiffOn
  change ContDiffOn ℝ ∞ (fun A : Matrix (Fin n) (Fin n) ℝ => A.det⁻¹ • A.adjugate) _ at hi
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv'] using hi

/-- Differentiate the product with its inverse, which is locally constant.
The ensuing algebra solves for the unknown derivative without commuting any
factors. Invertibility of an increment H is never required. -/
theorem matrix_inversion_hasTotalDerivative :
    Specs.D04.C04.MatrixInversion.matrix_inversion_hasTotalDerivativeType := by
  intro n A hA
  let U : Set (Matrix (Fin n) (Fin n) ℝ) := {B | IsUnit B}
  have hU : IsOpen U := general_linear_open n
  obtain ⟨L, hL⟩ := (matrix_inversion_smooth n 1).1 A hA
  have hid : HasTotalDerivative U (fun B => B) (ContinuousLinearMap.id ℝ _) A :=
    (hasTotalDerivative_iff_hasFDerivAt U _ _ A hU hA).mpr (hasFDerivAt_id A)
  obtain ⟨K, hK, hKH⟩ := bilinear_hasTotalDerivative
    (LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℝ)) U (fun B => B) (fun B => B⁻¹)
    (ContinuousLinearMap.id ℝ _) L A hid hL
  have he : (fun B : Matrix (Fin n) (Fin n) ℝ => B * B⁻¹) =ᶠ[𝓝 A] (fun _ => 1) := by
    filter_upwards [hU.mem_nhds hA] with B hB
    exact Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  have hKzero : K = 0 :=
    ((hasTotalDerivative_iff_hasFDerivAt U _ _ A hU hA).mp hK).unique
      ((hasFDerivAt_const (1 : Matrix (Fin n) (Fin n) ℝ) A).congr_of_eventuallyEq he)
  refine ⟨L, hL, ?_⟩
  intro H
  have hsum : H * A⁻¹ + A * L H = 0 := by
    simpa only [hKzero, zero_apply, ContinuousLinearMap.id_apply,
      LinearMap.mul_apply'] using (hKH H).symm
  have hmul := congrArg (fun B => A⁻¹ * B) hsum
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  simp only [mul_add, ← mul_assoc, Matrix.nonsing_inv_mul A hdet,
    one_mul, mul_zero] at hmul
  exact eq_neg_of_add_eq_zero_right hmul

theorem matrix_inversion_column_derivative :
    Specs.D04.C04.MatrixInversion.matrix_inversion_column_derivativeType := by
  intro n A H hA
  obtain ⟨L, hL, hLH⟩ := matrix_inversion_hasTotalDerivative A hA
  have hD : totalDerivative (fun B : Matrix (Fin n) (Fin n) ℝ => B⁻¹) A H =
      -(A⁻¹ * H * A⁻¹) := by
    exact (congrArg (fun K : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ => K H)
      (totalDerivative_eq _ _ _ _ hL)).trans (hLH H)
  calc
    _ = matrixLinearEquiv n n (-(A⁻¹ * H * A⁻¹)) :=
      congrArg (matrixLinearEquiv n n) hD
    _ = _ := by
      change matrixLinearEquiv n n (-(A⁻¹ * H * A⁻¹)) =
        -((matrixLinearEquiv n n A⁻¹).comp (matrixLinearEquiv n n H)).comp
          (matrixLinearEquiv n n A⁻¹)
      simp only [map_neg, matrix_composition]

end D04
