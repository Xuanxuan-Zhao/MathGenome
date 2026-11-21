import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaRegular
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDerivativeBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Smoothness of the Gamma integral on the positive real axis.
We use dominated differentiation for the measure integrals, with the two
explicit endpoint majorants from GammaDerivativeBounds. The established
continuous-integrable/Darboux bridge separately identifies both endpoints;
no total measure integral is treated as evidence of improper convergence. -/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Riemann Riemann.Improper
namespace GRSpec
export Specs.SingleVariableAnalysis.Ch18.GammaRegular
  (derivativeIntegralValue orderZero independentLimits integralDerivative integralContinuous
    iteratedDerivativeFormula derivativeHasIntegral smooth absoluteConvergence
    uniformConvergence uniformlySmallTails)
end GRSpec

def gammaDerivativeIntegral : ℕ → ℝ → ℝ := GRSpec.derivativeIntegralValue

theorem gamma_derivative_integral_zero : GRSpec.orderZero := by
  intro s hs
  simp [GRSpec.derivativeIntegralValue, GBSpec.kernelValue,
    Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaIntegralValue]

namespace GammaRegular

theorem kernel_parameter_derivative (k : ℕ) (s t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x => gammaLogKernel k x t) (gammaLogKernel (k + 1) s t) s := by
  have h := (((hasDerivAt_id s).sub_const 1).const_rpow ht).mul_const (Real.exp (-t))
  convert h.mul_const ((Real.log t) ^ k) using 1
  · rfl
  · dsimp [gammaLogKernel, GBSpec.kernelValue,
      Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaKernelValue]
    rw [pow_succ]
    ring

theorem integrable_positive_of_parts {f : ℝ → ℝ}
    (hl : IntegrableOn f (Ioc 0 1)) (hr : IntegrableOn f (Ioi 1)) :
    IntegrableOn f (Ioi 0) := by
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact zero_lt_one.trans h
    · intro h
      exact (le_total x 1).elim (fun hx => Or.inl ⟨h, hx⟩)
        (fun hx => if he : x = 1 then Or.inl ⟨h, he.le⟩ else Or.inr (lt_of_le_of_ne hx (Ne.symm he)))
  rw [← hu]
  exact hl.union hr

def majorant (α C : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  if t ≤ 1 then gammaZeroMajorant α k t else GBSpec.infinityMajorant C t

theorem majorant_integrable (α C : ℝ) (k : ℕ) (hα : 0 < α) :
    IntegrableOn (majorant α C k) (Ioi 0) := by
  apply integrable_positive_of_parts
  · apply (GammaBounds.zero_integrable α k hα).congr_fun _ measurableSet_Ioc
    intro t ht
    simp [majorant, ht.2]
  · apply (GammaBounds.infinity_integrable C).congr_fun _ measurableSet_Ioi
    intro t ht
    simp [majorant, not_le.mpr (show 1 < t from ht)]

theorem kernel_measurable (k : ℕ) (s : ℝ) :
    AEStronglyMeasurable (gammaLogKernel k s) (volume.restrict (Ioi 0)) :=
  (show ContinuousOn (gammaLogKernel k s) (Ioi 0) from
    fun t ht => (GammaBounds.kernel_continuous k s t ht).continuousWithinAt).aestronglyMeasurable
      measurableSet_Ioi

theorem kernel_le_majorant (k : ℕ) {α β C : ℝ}
    (hC : ∀ s t : ℝ, s ≤ β → 1 ≤ t →
      |gammaLogKernel k s t| ≤ GBSpec.infinityMajorant C t)
    {s t : ℝ} (hs : s ∈ Icc α β) (ht : 0 < t) :
    ‖gammaLogKernel k s t‖ ≤ majorant α C k t := by
  dsimp [majorant]
  split_ifs with ht1
  · exact gamma_log_zero_bound k α s t hs.1 ht ht1
  · exact hC s t hs.2 (not_le.mp ht1).le

theorem kernel_integrable (k : ℕ) (s : ℝ) (hs : 0 < s) :
    IntegrableOn (gammaLogKernel k s) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := gamma_log_infinity_bound k s
  apply (majorant_integrable s C k hs).mono' (kernel_measurable k s)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact kernel_le_majorant k hC ⟨le_rfl, le_rfl⟩ ht

theorem integral_eq (k : ℕ) (s : ℝ) (hs : 0 < s) :
    gammaDerivativeIntegral k s = ∫ t in Ioi (0 : ℝ), gammaLogKernel k s t := by
  exact intervalIntegral.integral_interval_add_Ioi (kernel_integrable k s hs)
    ((kernel_integrable k s hs).mono_set (Ioi_subset_Ioi zero_le_one))

end GammaRegular

theorem gamma_derivative_independent_limits : GRSpec.independentLimits := by
  intro k s hs
  exact positive_integrable_independent (GammaBounds.kernel_continuous k s)
    (GammaRegular.kernel_integrable k s hs)

theorem gamma_derivative_integral_hasDerivAt : GRSpec.integralDerivative := by
  intro k s hs
  change HasDerivAt (gammaDerivativeIntegral k) (gammaDerivativeIntegral (k + 1) s) s
  obtain ⟨C, _, hC⟩ := gamma_log_infinity_bound (k + 1) (s + 1)
  have hC' : ∀ x t : ℝ, x ≤ s + 1 → 1 ≤ t →
      |gammaLogKernel (k + 1) x t| ≤ GBSpec.infinityMajorant C t := hC
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun x t => gammaLogKernel k x t)
    (F' := fun x t => gammaLogKernel (k + 1) x t)
    (bound := GammaRegular.majorant (s / 2) C (k + 1))
    (Icc_mem_nhds (by linarith : s / 2 < s) (by linarith : s < s + 1))
    (Eventually.of_forall (GammaRegular.kernel_measurable k))
    (GammaRegular.kernel_integrable k s hs)
    (GammaRegular.kernel_measurable (k + 1) s)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x hx
      exact GammaRegular.kernel_le_majorant (k + 1) hC' hx ht)
    (GammaRegular.majorant_integrable (s / 2) C (k + 1) (by linarith))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro x _
      exact GammaRegular.kernel_parameter_derivative k x t ht)).2
  rw [GammaRegular.integral_eq (k + 1) s hs]
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
  exact GammaRegular.integral_eq k x hx

theorem gamma_derivative_integral_continuous : GRSpec.integralContinuous := by
  intro k s hs
  exact (gamma_derivative_integral_hasDerivAt k s hs).continuousAt.continuousWithinAt

theorem gamma_iterated_derivative_formula : GRSpec.iteratedDerivativeFormula := by
  intro k
  induction k with
  | zero =>
    intro s hs
    change Real.Gamma s = GRSpec.derivativeIntegralValue 0 s
    rw [gamma_derivative_integral_zero s hs]
    exact (gamma_eq_realGamma s hs).symm
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k Real.Gamma =ᶠ[𝓝 s] GRSpec.derivativeIntegralValue k := by
      filter_upwards [isOpen_Ioi.mem_nhds hs] with x hx
      exact ih x hx
    exact he.deriv_eq.trans (gamma_derivative_integral_hasDerivAt k s hs).deriv

theorem gamma_derivative_hasIntegral : GRSpec.derivativeHasIntegral := by
  intro k s hs
  refine ⟨?_, ⟨1, WithBot.coe_lt_coe.mpr zero_lt_one, WithTop.coe_lt_top _⟩, ?_⟩
  · intro u v hu huv _
    exact (positive_continuous_darboux (GammaBounds.kernel_continuous k s)
      (WithBot.coe_lt_coe.mp hu) huv).choose
  · obtain ⟨hl, hr⟩ := gamma_derivative_independent_limits k s hs
    exact ⟨_, _, hl, hr, gamma_iterated_derivative_formula k s hs⟩

namespace GammaRegular

theorem integral_contDiffOn (n k : ℕ) :
    ContDiffOn ℝ n (GRSpec.derivativeIntegralValue k) (Ioi 0) := by
  induction n generalizing k with
  | zero => exact contDiffOn_zero.mpr (gamma_derivative_integral_continuous k)
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun s hs => (gamma_derivative_integral_hasDerivAt k s hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (ih (k + 1)).congr
    intro s hs
    exact (gamma_derivative_integral_hasDerivAt k s hs).deriv

end GammaRegular

theorem gamma_smooth_positive : GRSpec.smooth := by
  apply contDiffOn_infty.mpr
  intro n
  apply (GammaRegular.integral_contDiffOn n 0).congr
  intro s hs
  exact gamma_iterated_derivative_formula 0 s hs

theorem gamma_derivative_absolute_convergence : GRSpec.absoluteConvergence :=
  gamma_log_absolute_convergence

theorem gamma_derivative_uniform_convergence : GRSpec.uniformConvergence :=
  gamma_log_uniform_convergence

theorem gamma_derivative_uniformly_small_tails : GRSpec.uniformlySmallTails :=
  gamma_log_uniformly_small_tails

end SingleVariableAnalysis
