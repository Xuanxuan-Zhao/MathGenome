import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.TikhonovMinimizer
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.LaxMilgramSolvability

/-!
Coercivity of αI + A*A gives a bounded inverse on all of H. The normal
equation cancels the cross terms in the objective. The sharp regularizer
estimate follows directly from Cauchy–Schwarz and completing a square,
so this argument does not require compactness or a spectral decomposition.
-/

noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.PartV.TikhonovMinimizer
universe u v w

section Helpers
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- The real part of the normal operator's pairing, in the source convention. -/
theorem re_inner_normal (A : H →L[𝕜] G) (α : ℝ) (x y : H) :
    RCLike.re ⟪x, Spec.normalOperator A α y⟫_𝕜 =
      α * RCLike.re ⟪x, y⟫_𝕜 + RCLike.re ⟪A x, A y⟫_𝕜 := by
  simp only [Spec.normalOperator, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, inner_add_right, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, map_add, RCLike.re_ofReal_mul]

/-- Positive regularization makes the normal operator coercive on all of H. -/
theorem normal_coercive (A : H →L[𝕜] G) (α : ℝ) (x : H) :
    α * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, Spec.normalOperator A α x⟫_𝕜 := by
  rw [re_inner_normal, inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖A x‖]

end Helpers

theorem normal_invertible : Spec.Invertibility.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα
  have hb := ExpandedFA.Hilbert.LaxMilgramSolvability.operator_bijective
    (Spec.normalOperator A α) hα (normal_coercive A α)
  refine ⟨ContinuousLinearEquiv.ofBijective (Spec.normalOperator A α) ?_ ?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mpr hb.1
  · exact LinearMap.range_eq_top.mpr hb.2
  · exact ContinuousLinearEquiv.coe_ofBijective _ _ _

theorem inverse_identities : Spec.InverseIdentities.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα
  have hi := normal_invertible 𝕜 H G A α hα
  exact ⟨hi.self_comp_inverse, hi.inverse_comp_self⟩

theorem normal_equation : Spec.NormalEquation.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα f
  exact (normal_invertible 𝕜 H G A α hα).self_apply_inverse (A.adjoint f)

section MoreHelpers
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- The normal equation tested against any vector. -/
theorem normal_pairing (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α)
    (f : G) (v : H) :
    α * RCLike.re ⟪v, Spec.regularizer A α f⟫_𝕜 +
      RCLike.re ⟪A v, A (Spec.regularizer A α f)⟫_𝕜 =
        RCLike.re ⟪A v, f⟫_𝕜 := by
  rw [← re_inner_normal, normal_equation 𝕜 H G A α hα f,
    ContinuousLinearMap.adjoint_inner_right]

end MoreHelpers

theorem difference_identity : Spec.DifferenceIdentity.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα f x
  have hx := normal_pairing A α hα f x
  have hu := normal_pairing A α hα f (Spec.regularizer A α f)
  simp only [inner_self_eq_norm_sq] at hu
  simp only [Spec.objective, map_sub, norm_sub_sq (𝕜 := 𝕜)]
  nlinarith

theorem unique_minimizer : Spec.UniqueMinimizer.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα f
  constructor
  · intro x
    have hd := difference_identity 𝕜 H G A α hα f x
    have hp := mul_nonneg hα.le (sq_nonneg ‖x - Spec.regularizer A α f‖)
    nlinarith [sq_nonneg ‖A (x - Spec.regularizer A α f)‖]
  · intro y hy
    have hd := difference_identity 𝕜 H G A α hα f y
    have hm := hy (Spec.regularizer A α f)
    have hz : ‖y - Spec.regularizer A α f‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖A (y - Spec.regularizer A α f)‖,
        sq_nonneg ‖y - Spec.regularizer A α f‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The scalar completing-square estimate used for the sharp norm constant. -/
theorem scalar_bound {α s t r : ℝ} (hα : 0 < α) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (h : α * s ^ 2 + t ^ 2 ≤ t * r) : s ≤ r / (2 * Real.sqrt α) := by
  have hsq : 4 * α * s ^ 2 ≤ r ^ 2 := by
    nlinarith only [h, sq_nonneg (2 * t - r)]
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  apply (le_div_iff₀ (mul_pos (by norm_num) hsqrt)).mpr
  have hb : (2 * Real.sqrt α * s) ^ 2 ≤ r ^ 2 := by
    calc
      _ = 4 * α * s ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hα.le]
        ring
      _ ≤ _ := hsq
  have hle := (sq_le_sq₀ (mul_nonneg (mul_nonneg (by norm_num) hsqrt.le) hs) hr).mp hb
  simpa only [mul_comm s] using hle

theorem regularizer_norm : Spec.RegularizerNorm.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  refine (Spec.regularizer A α).opNorm_le_bound
    (le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) hs))) ?_
  intro f
  have he := normal_pairing A α hα f (Spec.regularizer A α f)
  simp only [inner_self_eq_norm_sq] at he
  have hc := re_inner_le_norm (𝕜 := 𝕜) (A (Spec.regularizer A α f)) f
  have hb := scalar_bound hα (norm_nonneg (Spec.regularizer A α f)) (norm_nonneg f)
    (he.le.trans hc)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hb

end ExpandedFA.PartV.TikhonovMinimizer
