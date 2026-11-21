import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Green
import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.Dichotomy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction Matrix.Norms.Operator
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch20.Green
open D13Unified.Ch07
open Specs.D13Unified.Ch20.Dichotomy
open Specs.D13Unified.Ch07.MatrixExponential

/-- The complete space and its exact supremum-norm interface. -/
theorem bounded_continuous_function_space : Specs.D13Unified.Ch20.Green.functionSpaceExpected := by
  intro E _ _ _
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  refine ⟨inferInstance, fun g C => BoundedContinuousFunction.norm_le_of_nonempty, ?_⟩
  intro g hg hbound
  obtain ⟨C, hC⟩ := hbound
  exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup g hg C hC, fun _ => rfl⟩

/-- The Green formula uses the original half-line kernels. -/
def green : Specs.D13Unified.Ch20.Green.greenType := @greenValue

variable {n E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The exponential in the same operator realization as the chapter norms. -/
def evolution (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (t : ℝ) : E →L[ℝ] E :=
  matrixOperatorEquiv b (matrixExp A t)

def projection (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (stable : Bool) : E →L[ℝ] E :=
  matrixOperatorEquiv b (projectionMatrix A stable)

lemma evolution_hasDerivAt (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (evolution b A) (matrixOperatorEquiv b A * evolution b A t) t := by
  let L := (matrixOperatorEquiv b).toLinearMap.toContinuousLinearMap
  have hd := L.hasFDerivAt.comp_hasDerivAt t (matrixExp_hasDerivAt_left A t)
  change HasDerivAt (evolution b A) (matrixOperatorEquiv b (A * matrixExp A t)) t at hd
  simpa only [map_mul, evolution] using hd

lemma evolution_continuous (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) :
    Continuous (evolution b A) :=
  continuous_iff_continuousAt.mpr (fun t => (evolution_hasDerivAt b A t).continuousAt)

lemma kernel_eq (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (stable : Bool)
    (g : ℝ → E) (t s : ℝ) :
    kernel b A stable g t s = evolution b A (t - s) (projection b A stable (g s)) := by
  simp only [kernel, evolution, projection, map_mul, mul_apply_eq_comp]
  rfl

lemma kernel_continuous (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (stable : Bool) (g : ℝ →ᵇ E) (t : ℝ) :
    Continuous (kernel b A stable g t) := by
  have heq : kernel b A stable g t =
      fun s => evolution b A (t-s) (projection b A stable (g s)) :=
    funext (fun s => kernel_eq b A stable g t s)
  rw [heq]
  exact ((evolution_continuous b A).comp (continuous_const.sub continuous_id)).clm_apply
    ((projection b A stable).continuous.comp g.continuous)

lemma stable_kernel_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t s : ℝ) (hst : s ≤ t) :
    ‖kernel b A true g t s‖ ≤ K * ‖g‖ * Real.exp (-α * (t - s)) := by
  have hK : 0 ≤ K := le_trans zero_le_one h.1
  calc
    ‖kernel b A true g t s‖ ≤
        matrixOperatorNorm b (exponentialValue A (t-s) * projectionMatrix A true) * ‖g s‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (K * Real.exp (-α * (t-s))) * ‖g‖ :=
      mul_le_mul (h.2.2 (t-s) (sub_nonneg.mpr hst)).1 (g.norm_coe_le_norm s)
        (norm_nonneg _) (mul_nonneg hK (Real.exp_pos _).le)
    _ = _ := by ring

lemma unstable_kernel_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t s : ℝ) (hst : t ≤ s) :
    ‖kernel b A false g t s‖ ≤ K * ‖g‖ * Real.exp (-α * (s - t)) := by
  have hK : 0 ≤ K := le_trans zero_le_one h.1
  have he := (h.2.2 (s-t) (sub_nonneg.mpr hst)).2
  rw [neg_sub] at he
  calc
    ‖kernel b A false g t s‖ ≤
        matrixOperatorNorm b (exponentialValue A (t-s) * projectionMatrix A false) * ‖g s‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (K * Real.exp (-α * (s-t))) * ‖g‖ :=
      mul_le_mul he (g.norm_coe_le_norm s) (norm_nonneg _) (mul_nonneg hK (Real.exp_pos _).le)
    _ = _ := by ring

lemma stable_majorant_eq (K α M t s : ℝ) :
    K * M * Real.exp (-α * (t-s)) =
      (K * M * Real.exp (-α*t)) * Real.exp (α*s) := by
  rw [mul_assoc (K * M), ← Real.exp_add]
  congr 2
  ring

lemma unstable_majorant_eq (K α M t s : ℝ) :
    K * M * Real.exp (-α * (s-t)) =
      (K * M * Real.exp (α*t)) * Real.exp (-α*s) := by
  rw [mul_assoc (K * M), ← Real.exp_add]
  congr 2
  ring

lemma stable_kernel_integrable (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    IntegrableOn (kernel b A true g t) (Iic t) := by
  have hmaj := (integrableOn_exp_mul_Iic h.2.1 t).const_mul
    (K * ‖g‖ * Real.exp (-α*t))
  apply hmaj.mono' (kernel_continuous b A true g t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  rw [← stable_majorant_eq]
  exact stable_kernel_bound b A h g t s hs

lemma unstable_kernel_integrable (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    IntegrableOn (kernel b A false g t) (Ioi t) := by
  have hmaj := (integrableOn_exp_mul_Ioi (neg_neg_of_pos h.2.1) t).const_mul
    (K * ‖g‖ * Real.exp (α*t))
  apply hmaj.mono' (kernel_continuous b A false g t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [← unstable_majorant_eq]
  exact unstable_kernel_bound b A h g t s (le_of_lt hs)

/-- Both integrals converge absolutely, with the asserted improper limits. -/
theorem green_convergence : Specs.D13Unified.Ch20.Green.convergenceExpected := by
  intro n E _ _ _ _ _ b A K α h g t
  have hs := stable_kernel_integrable b A h g t
  have hu := unstable_kernel_integrable b A h g t
  exact ⟨hs, hu, intervalIntegral_tendsto_integral_Iic t hs tendsto_id,
    intervalIntegral_tendsto_integral_Ioi t hu tendsto_id⟩

lemma stable_majorant_integral {α : ℝ} (hα : 0 < α) (K M t : ℝ) :
    (∫ s in Iic t, (K * M * Real.exp (-α*t)) * Real.exp (α*s)) = K / α * M := by
  rw [integral_const_mul, integral_exp_mul_Iic hα]
  calc
    (K * M * Real.exp (-α*t)) * (Real.exp (α*t) / α) =
        (K / α * M) * (Real.exp (-α*t) * Real.exp (α*t)) := by ring
    _ = K / α * M := by
      rw [← Real.exp_add]
      simp

lemma unstable_majorant_integral {α : ℝ} (hα : 0 < α) (K M t : ℝ) :
    (∫ s in Ioi t, (K * M * Real.exp (α*t)) * Real.exp (-α*s)) = K / α * M := by
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hα)]
  calc
    (K * M * Real.exp (α*t)) * (-Real.exp (-α*t) / -α) =
        (K / α * M) * (Real.exp (α*t) * Real.exp (-α*t)) := by ring
    _ = K / α * M := by
      rw [← Real.exp_add]
      simp

lemma stable_integral_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    ‖∫ s in Iic t, kernel b A true g t s‖ ≤ K / α * ‖g‖ := by
  rw [← stable_majorant_integral h.2.1 K ‖g‖ t]
  apply norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Iic h.2.1 t).const_mul (K * ‖g‖ * Real.exp (-α*t)))
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  rw [← stable_majorant_eq]
  exact stable_kernel_bound b A h g t s hs

lemma unstable_integral_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    ‖∫ s in Ioi t, kernel b A false g t s‖ ≤ K / α * ‖g‖ := by
  rw [← unstable_majorant_integral h.2.1 K ‖g‖ t]
  apply norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr h.2.1) t).const_mul
      (K * ‖g‖ * Real.exp (α*t)))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [← unstable_majorant_eq]
  exact unstable_kernel_bound b A h g t s (le_of_lt hs)

lemma green_pointwise_bound (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    ‖greenValue b A g t‖ ≤ (2 * K / α) * ‖g‖ := by
  apply (norm_sub_le _ _).trans
  have hs := stable_integral_bound b A h g t
  have hu := unstable_integral_bound b A h g t
  calc
    _ ≤ K / α * ‖g‖ + K / α * ‖g‖ := add_le_add hs hu
    _ = _ := by ring

lemma evolution_add (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (r t : ℝ) :
    evolution b A (r+t) = evolution b A r * evolution b A t := by
  simp only [evolution, matrixExp_add_time, map_mul]

@[simp] lemma evolution_zero (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) :
    evolution b A 0 = 1 := by simp [evolution]

lemma kernel_transport (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (stable : Bool)
    (g : ℝ → E) (r t s : ℝ) :
    evolution b A r (kernel b A stable g t s) = kernel b A stable g (r+t) s := by
  rw [kernel_eq, kernel_eq]
  change (evolution b A r * evolution b A (t-s)) _ = _
  rw [← evolution_add]
  congr 2
  ring

lemma reference_kernel_integrable (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    IntegrableOn (kernel b A true g 0) (Iic t) ∧
      IntegrableOn (kernel b A false g 0) (Ioi t) := by
  have heq (stable : Bool) : (fun s => evolution b A (-t) (kernel b A stable g t s)) =
      kernel b A stable g 0 := by
    funext s
    rw [kernel_transport, neg_add_cancel]
  constructor
  · simpa only [IntegrableOn, Function.comp_def, heq] using
      (evolution b A (-t)).integrable_comp (stable_kernel_integrable b A h g t)
  · simpa only [IntegrableOn, Function.comp_def, heq] using
      (evolution b A (-t)).integrable_comp (unstable_kernel_integrable b A h g t)

lemma green_factored (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    greenValue b A g t = evolution b A t
      ((∫ s in Iic t, kernel b A true g 0 s) -
        ∫ s in Ioi t, kernel b A false g 0 s) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heq (stable : Bool) : kernel b A stable g t =
      fun s => evolution b A t (kernel b A stable g 0 s) := by
    funext s
    rw [kernel_transport, add_zero]
  rw [greenValue, heq true, heq false,
    (evolution b A t).integral_comp_comm (reference_kernel_integrable b A h g t).1,
    (evolution b A t).integral_comp_comm (reference_kernel_integrable b A h g t).2,
    map_sub]

/-- FTC for a left improper primitive. Convergence is used to reduce it to
an ordinary continuous integral, so no derivative of the forcing is needed. -/
lemma hasDerivAt_left_primitive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : ℝ → F) (hf : Continuous f)
    (hi : ∀ t : ℝ, IntegrableOn f (Iic t)) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in Iic t, f s) (f t) t := by
  have hd := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have heq : (fun t => ∫ s in Iic t, f s) =
      fun t => (∫ s in 0..t, f s) + ∫ s in Iic 0, f s := by
    funext t
    exact eq_add_of_sub_eq (intervalIntegral.integral_Iic_sub_Iic (hi 0) (hi t))
  rw [heq]
  exact hd.add_const _

/-- FTC for a right improper primitive; the lower endpoint contributes a
minus sign. This is the sign used in the Green inverse. -/
lemma hasDerivAt_right_primitive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (f : ℝ → F) (hf : Continuous f)
    (hi : ∀ t : ℝ, IntegrableOn f (Ioi t)) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in Ioi t, f s) (-f t) t := by
  have hd := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have heq : (fun t => ∫ s in Ioi t, f s) =
      fun t => (∫ s in Ioi 0, f s) - ∫ s in 0..t, f s := by
    funext t
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (hi 0) (hi t)
    calc
      (∫ s in Ioi t, f s) = (∫ s in Ioi 0, f s) -
          ((∫ s in Ioi 0, f s) - ∫ s in Ioi t, f s) := by abel
      _ = _ := by rw [h]
  rw [heq]
  exact hd.const_sub _

lemma projection_add (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : IsHyperbolic A) :
    projection b A true + projection b A false = 1 := by
  have h := (spectral_projection_laws A hA).1
  have hmat : projectionMatrix A true + projectionMatrix A false = 1 := by
    simpa only [projectionMatrix, map_add, map_one] using
      congrArg Matrix.toLinAlgEquiv'.symm h
  simpa only [projection, map_add, map_one] using congrArg (matrixOperatorEquiv b) hmat

lemma kernel_diagonal (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (stable : Bool)
    (g : ℝ → E) (t : ℝ) : kernel b A stable g t t = projection b A stable (g t) := by
  rw [kernel_eq, sub_self, evolution_zero]
  rfl

/-- Differentiation of the absolutely convergent Green formula. -/
lemma green_hasDerivAt (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (t : ℝ) :
    HasDerivAt (greenValue b A g) (matrixOperatorEquiv b A (greenValue b A g t) + g t) t := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let B : ℝ → E := fun t => (∫ s in Iic t, kernel b A true g 0 s) -
    ∫ s in Ioi t, kernel b A false g 0 s
  have hB : HasDerivAt B (kernel b A true g 0 t + kernel b A false g 0 t) t := by
    have hs := hasDerivAt_left_primitive _ (kernel_continuous b A true g 0)
      (fun t => (reference_kernel_integrable b A h g t).1) t
    have hu := hasDerivAt_right_primitive _ (kernel_continuous b A false g 0)
      (fun t => (reference_kernel_integrable b A h g t).2) t
    have hd := hs.sub hu
    change HasDerivAt B (kernel b A true g 0 t - -kernel b A false g 0 t) t at hd
    simpa only [sub_neg_eq_add] using hd
  have hd := (evolution_hasDerivAt b A t).clm_apply hB
  have hend : evolution b A t (kernel b A true g 0 t + kernel b A false g 0 t) = g t := by
    rw [map_add, kernel_transport, kernel_transport, add_zero, kernel_diagonal, kernel_diagonal]
    have hp := congrArg (fun L : E →L[ℝ] E => L (g t)) (projection_add b A hA)
    exact hp
  have hval : (matrixOperatorEquiv b A * evolution b A t) (B t) +
        evolution b A t (kernel b A true g 0 t + kernel b A false g 0 t) =
      matrixOperatorEquiv b A (greenValue b A g t) + g t := by
    rw [hend, green_factored b A h g t]
    rfl
  rw [hval] at hd
  have heq : (fun t => evolution b A t (B t)) = greenValue b A g :=
    funext (fun t => (green_factored b A h g t).symm)
  rwa [heq] at hd

lemma green_continuous (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) :
    Continuous (greenValue b A g) :=
  continuous_iff_continuousAt.mpr (fun t => (green_hasDerivAt b A hA h g t).continuousAt)

lemma green_contDiff (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) :
    ContDiff ℝ 1 (greenValue b A g) := by
  have hd := green_hasDerivAt b A hA h g
  have heq : deriv (greenValue b A g) = fun t => matrixOperatorEquiv b A (greenValue b A g t) + g t :=
    funext (fun t => (hd t).deriv)
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  rw [heq]
  exact ((matrixOperatorEquiv b A).continuous.comp (green_continuous b A hA h g)).add g.continuous

/-- The homogeneous difference argument gives uniqueness among all bounded
whole-line differentiable solutions, without any extra smoothness assumption. -/
lemma green_unique (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) (hA : IsHyperbolic A)
    {K α : ℝ} (h : DichotomyBounds b A K α) (g : ℝ →ᵇ E) (z : ℝ → E)
    (hz : ∀ t, HasDerivAt z (matrixOperatorEquiv b A (z t) + g t) t)
    (hbound : ∃ M : ℝ, ∀ t, ‖z t‖ ≤ M) : ∀ t, z t = greenValue b A g t := by
  let w : ℝ → E := fun t => z t - greenValue b A g t
  have hwd : ∀ t, HasDerivAt w (matrixOperatorEquiv b A (w t)) t := by
    intro t
    have hd := (hz t).sub (green_hasDerivAt b A hA h g t)
    have heq : (matrixOperatorEquiv b A (z t) + g t) -
        (matrixOperatorEquiv b A (greenValue b A g t) + g t) =
        matrixOperatorEquiv b A (w t) := by
      dsimp [w]
      rw [map_sub]
      abel
    exact heq ▸ hd
  have hwb : ∃ M : ℝ, ∀ t, ‖w t‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbound
    refine ⟨M + (2*K/α)*‖g‖, fun t => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hM t) (green_pointwise_bound b A h g t))
  intro t
  exact sub_eq_zero.mp (bounded_homogeneous_solution_zero b A hA w hwd hwb t)

/-- The bounded Green inverse with the exact constant 2K/α. -/
theorem green_inverse : Specs.D13Unified.Ch20.Green.inverseExpected := by
  intro n E _ _ _ _ _ b A hA K α h g
  let G : ℝ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup
    (greenValue b A g) (green_continuous b A hA h g) ((2*K/α)*‖g‖)
    (green_pointwise_bound b A h g)
  refine ⟨G, fun _ => rfl, green_contDiff b A hA h g,
    green_hasDerivAt b A hA h g, ?_, ?_⟩
  · exact BoundedContinuousFunction.norm_le_of_nonempty.mpr (green_pointwise_bound b A h g)
  · intro z hz hb t
    exact green_unique b A hA h g z hz hb t

end D13Unified.Ch20.Green
