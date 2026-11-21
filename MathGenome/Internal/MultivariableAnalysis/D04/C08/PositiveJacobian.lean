import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix

/-! Jacobi's formula and the derivative of the positive volume Jacobian.
The determinant is a continuous multilinear function of its rows. Its total
derivative is the sum of single-row replacements. For invertible A, expanding
each replacement row in the rows of A identifies that sum with
`det A * trace (H * A⁻¹)`; cyclicity of trace gives the stated order.
The scalar absolute-value derivative then applies at each nonzero determinant.
-/
noncomputable section
open Set Filter Topology
open scoped BigOperators Matrix.Norms.Elementwise
namespace D04
namespace PositiveJacobian

private def determinantMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := continuous_id.matrix_det }

private theorem determinantLinearDeriv_apply {n : ℕ}
    (A H : Matrix (Fin n) (Fin n) ℝ) :
    (determinantMultilinear n).linearDeriv A H =
      ∑ i, (A.updateRow i (H i)).det := by
  dsimp only [Matrix] at A H ⊢
  simp only [ContinuousMultilinearMap.linearDeriv_apply]
  rfl

theorem determinant_differentiable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    DifferentiableAt ℝ Matrix.det A :=
  ((determinantMultilinear n).hasFDerivAt A).differentiableAt

private theorem determinant_updateRow {n : ℕ}
    (A H : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (i : Fin n) :
    (A.updateRow i (H i)).det = (H * A⁻¹) i i * A.det := by
  have he : H i = ∑ k, ((H * A⁻¹) i k) • A k := by
    funext j
    have h := congr_fun (congr_fun
      (Matrix.nonsing_inv_mul_cancel_right A H (isUnit_iff_ne_zero.mpr hA)) i) j
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  rw [he, Matrix.det_updateRow_sum]
  rfl

theorem determinant_derivative {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.det ≠ 0) (H : Matrix (Fin n) (Fin n) ℝ) :
    fderiv ℝ Matrix.det A H = A.det * (A⁻¹ * H).trace := by
  calc
    fderiv ℝ Matrix.det A H = (determinantMultilinear n).linearDeriv A H :=
      congrArg (fun L : (Fin n → Fin n → ℝ) →L[ℝ] ℝ => L H)
        ((determinantMultilinear n).hasFDerivAt A).fderiv
    _ = ∑ i, (A.updateRow i (H i)).det := determinantLinearDeriv_apply A H
    _ = A.det * (A⁻¹ * H).trace := by
      simp_rw [determinant_updateRow A H hA]
      rw [← Finset.sum_mul]
      change (H * A⁻¹).trace * A.det = A.det * (A⁻¹ * H).trace
      rw [Matrix.trace_mul_comm, mul_comm]

section Parameters
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A pointwise theorem needs invertibility only at the basepoint. -/
theorem positive_jacobian_derivative_at {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) (p : X)
    (hA : DifferentiableAt ℝ A p) (hInv : (A p).det ≠ 0) :
    DifferentiableAt ℝ (fun q => |(A q).det|) p ∧
      ∀ h : X, fderiv ℝ (fun q => |(A q).det|) p h =
        |(A p).det| * ((A p)⁻¹ * (fderiv ℝ A p h)).trace := by
  have hd : HasFDerivAt (fun q => (A q).det)
      ((fderiv ℝ Matrix.det (A p)).comp (fderiv ℝ A p)) p :=
    (determinant_differentiable (A p)).hasFDerivAt.comp p hA.hasFDerivAt
  have ha := hd.abs hInv
  refine ⟨ha.differentiableAt, fun h => ?_⟩
  rw [ha.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [determinant_derivative (A p) hInv, ← mul_assoc, sign_mul_self]

/-- The sign is chosen locally at p; disconnected domains require no common sign. -/
theorem determinant_local_sign {n : ℕ}
    (A : X → Matrix (Fin n) (Fin n) ℝ) (p : X)
    (hA : DifferentiableAt ℝ A p) (hInv : (A p).det ≠ 0) :
    ∀ᶠ q in 𝓝 p, (A q).det ≠ 0 ∧
      |(A q).det| = (SignType.sign ((A p).det) : ℝ) * (A q).det := by
  have hc := ((determinant_differentiable (A p)).hasFDerivAt.comp p
    hA.hasFDerivAt).continuousAt
  rcases lt_or_gt_of_ne hInv with hn | hp
  · filter_upwards [hc.eventually (Iio_mem_nhds hn)] with q hq
    change (A q).det < 0 at hq
    exact ⟨ne_of_lt hq, by simp [sign_neg hn, abs_of_neg hq]⟩
  · filter_upwards [hc.eventually (Ioi_mem_nhds hp)] with q hq
    change 0 < (A q).det at hq
    exact ⟨ne_of_gt hq, by simp [sign_pos hp, abs_of_pos hq]⟩

end Parameters

/-- The source's open finite-dimensional parameter domain, with the shared
remainder definition of total differentiability. All m,n range over ℕ. -/
theorem positive_jacobian {m n : ℕ} (P : Set (E m)) (hP : IsOpen P)
    (A : E m → Matrix (Fin n) (Fin n) ℝ)
    (hA : TotalDifferentiableOn P A) (hInv : ∀ p ∈ P, (A p).det ≠ 0) :
    TotalDifferentiableOn P (fun p => |(A p).det|) ∧
      ∀ p ∈ P, ∀ h : E m,
        totalDerivative (fun q => |(A q).det|) p h =
          |(A p).det| * ((A p)⁻¹ * (totalDerivative A p h)).trace := by
  have hdiff : ∀ p ∈ P, DifferentiableAt ℝ A p := by
    intro p hp
    obtain ⟨L, hL⟩ := hA p hp
    exact ((hasTotalDerivative_iff_hasFDerivAt P A L p hP hp).mp hL).differentiableAt
  have hj := fun p hp => positive_jacobian_derivative_at A p (hdiff p hp) (hInv p hp)
  constructor
  · intro p hp
    exact ⟨_, (hasTotalDerivative_iff_hasFDerivAt P _ _ p hP hp).mpr
      (hj p hp).1.hasFDerivAt⟩
  · intro p hp h
    exact (hj p hp).2 h

/-- The empty determinant is one, its trace term is zero, and its parameter
Jacobian is the constant one with zero total derivative. -/
theorem positive_jacobian_dimension_zero {m : ℕ}
    (A : E m → Matrix (Fin 0) (Fin 0) ℝ) (p h : E m) :
    (A p).det = 1 ∧ ((A p)⁻¹ * (totalDerivative A p h)).trace = 0 ∧
      |(A p).det| = 1 ∧ totalDerivative (fun q => |(A q).det|) p = 0 := by
  simp [Matrix.det_isEmpty, Matrix.trace, totalDerivative,
    Specs.D04.C02.DerivativeInterfaces.totalDerivativeValue,
    Specs.D04.C02.DerivativeInterfaces.Model.totalDerivative]

end PositiveJacobian
end D04
