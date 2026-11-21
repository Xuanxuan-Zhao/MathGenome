import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.FourierFailures
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.DirichletKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TorusFourierBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08BoundedInverse
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology ZeroAtInfty
namespace ExpandedFA.PartIV.FourierFailures
open DirichletKernelSpec FourierFailuresSpec
abbrev Circle := DirichletKernelSpec.Circle

/-- Contrapositive uniform boundedness, with the quantifiers needed for a
single function whose images are unbounded. -/
theorem exists_unbounded_images {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
    (T : ℕ → E →L[𝕜] F)
    (h : ∀ C : ℝ, ∃ N : ℕ, C < ‖T N‖) :
    ∃ f : E, ∀ B : ℝ, ∃ N : ℕ, B < ‖T N f‖ := by
  by_contra! hn
  obtain ⟨C, _, hC⟩ := ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness
    𝕜 E F ℕ T hn
  obtain ⟨N, hN⟩ := h C
  exact (hC N).not_gt hN

theorem continuous_divergence : ContinuousDivergence := by
  intro x
  obtain ⟨f, hf⟩ := exists_unbounded_images (fun N => DirichletKernel.evaluation N x)
    (fun C => by
      obtain ⟨N, hN⟩ := eventually_atTop.1
        ((tendsto_atTop.1 DirichletKernel.kernel_norm_divergence) (C + 1))
      exact ⟨N, by rw [DirichletKernel.evaluation_norm]; linarith [hN N le_rfl]⟩)
  exact ⟨f, by simpa only [DirichletKernel.evaluation_apply] using hf⟩

theorem real_continuous_divergence : RealContinuousDivergence := by
  intro x
  obtain ⟨f, hf⟩ := exists_unbounded_images (fun N => DirichletKernel.realEvaluation N x)
    (fun C => by
      obtain ⟨N, hN⟩ := eventually_atTop.1
        ((tendsto_atTop.1 DirichletKernel.kernel_norm_divergence) (C + 1))
      exact ⟨N, by rw [DirichletKernel.realEvaluation_norm]; linarith [hN N le_rfl]⟩)
  refine ⟨f, fun B => ?_⟩
  obtain ⟨N, hN⟩ := hf B
  refine ⟨N, hN.trans_le ?_⟩
  rw [DirichletKernel.realEvaluation_apply]
  exact Complex.abs_re_le_norm _

theorem l1_divergence : L1Divergence := by
  choose S hS hnorm using DirichletKernel.l1_convolution_norm
  obtain ⟨f, hf⟩ := exists_unbounded_images S (fun C => by
    obtain ⟨N, hN⟩ := eventually_atTop.1
        ((tendsto_atTop.1 DirichletKernel.kernel_norm_divergence) (C + 1))
    exact ⟨N, by rw [hnorm]; linarith [hN N le_rfl]⟩)
  have hu : ∀ B : ℝ, ∃ N : ℕ, B < ‖partialSumL1 N f‖ := by
    simpa only [hS] using hf
  refine ⟨f, hu, ?_⟩
  rintro ⟨g, hg⟩
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range
  obtain ⟨N, hN⟩ := hu C
  exact (hC (Set.mem_range_self N)).not_gt hN

theorem real_l1_divergence : RealL1Divergence := by
  choose S hS hnorm using DirichletKernel.real_l1_convolution_norm
  obtain ⟨f, hf⟩ := exists_unbounded_images S (fun C => by
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((tendsto_atTop.1 DirichletKernel.kernel_norm_divergence) (C + 1))
    exact ⟨N, by rw [hnorm]; linarith [hN N le_rfl]⟩)
  refine ⟨f, fun N => S N f, ?_, hf, ?_⟩
  · intro N
    filter_upwards [hS N f] with x hx
    rw [hx]
    exact DirichletKernel.real_fourier_convolution N f (L1.integrable_coeFn f) x
  · rintro ⟨g, hg⟩
    obtain ⟨C, hC⟩ := hg.norm.bddAbove_range
    obtain ⟨N, hN⟩ := hf C
    exact (hC (Set.mem_range_self N)).not_gt hN

/-- The L¹ coefficient estimate uses normalized Haar measure. -/
theorem coefficient_norm_le (f : DirichletKernelSpec.L1) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ ‖f‖ := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ ≤ ∫ t, ‖fourier (-n) t • f t‖ ∂haar := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

theorem coefficient_add (f g : DirichletKernelSpec.L1) (n : ℤ) :
    fourierCoeff (f + g) n = fourierCoeff f n + fourierCoeff g n := by
  rw [fourierCoeff_congr_ae (Lp.coeFn_add f g)]
  exact congrFun (fourierCoeff.add (L1.integrable_coeFn f) (L1.integrable_coeFn g)) n

theorem coefficient_smul (c : ℂ) (f : DirichletKernelSpec.L1) (n : ℤ) :
    fourierCoeff (c • f) n = c • fourierCoeff f n := by
  rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f)]
  exact fourierCoeff.const_smul f c n

theorem coefficient_sub (f g : DirichletKernelSpec.L1) (n : ℤ) :
    fourierCoeff (f - g) n = fourierCoeff f n - fourierCoeff g n := by
  rw [fourierCoeff_congr_ae (Lp.coeFn_sub f g)]
  simp only [fourierCoeff, Pi.sub_apply, smul_sub]
  exact integral_sub ((L1.integrable_coeFn f).fourier_smul _)
    ((L1.integrable_coeFn g).fourier_smul _)

theorem continuous_coefficient_decay (g : C(Circle, ℂ)) :
    Tendsto (fourierCoeff g) cofinite (𝓝 0) := by
  have hs : Summable (fun n : ℤ => ‖fourierCoeff g n‖ ^ 2) := by
    simpa only [fourierCoeff_toLp] using
      (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 haar ℂ g)).summable
  apply NormedAddGroup.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [hs.tendsto_cofinite_zero.eventually_lt_const (sq_pos_of_pos hε)] with n hn
  nlinarith [norm_nonneg (fourierCoeff g n)]

theorem coefficient_decay : CoefficientDecay := by
  intro f
  apply NormedAddGroup.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := (ContinuousMap.toLp_denseRange ℂ haar ℂ (p := 1) (by simp)).exists_dist_lt
    f (half_pos hε)
  have hgcoeff (n : ℤ) : fourierCoeff (ContinuousMap.toLp 1 haar ℂ g) n =
      fourierCoeff g n :=
    congrFun (fourierCoeff_congr_ae (ContinuousMap.coeFn_toAEEqFun haar g)) n
  filter_upwards [(NormedAddGroup.tendsto_nhds_zero.mp
    (continuous_coefficient_decay g)) (ε / 2) (half_pos hε)] with n hn
  have hnorm := coefficient_norm_le (f - ContinuousMap.toLp 1 haar ℂ g) n
  rw [coefficient_sub, hgcoeff] at hnorm
  have hdist : ‖f - ContinuousMap.toLp 1 haar ℂ g‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hg
  calc
    ‖fourierCoeff f n‖ ≤ ‖fourierCoeff f n - fourierCoeff g n‖ + ‖fourierCoeff g n‖ :=
      norm_le_norm_sub_add _ _
    _ < ε := by linarith

/-- The canonical integral coefficient sequence, bundled in c₀(ℤ). -/
def coefficientSequence (f : DirichletKernelSpec.L1) : CoefficientSpace where
  toFun := fourierCoeff f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa only [cocompact_eq_cofinite] using coefficient_decay f

def coefficientMap : DirichletKernelSpec.L1 →L[ℂ] CoefficientSpace := by
  let F : DirichletKernelSpec.L1 →ₗ[ℂ] CoefficientSpace :=
    { toFun := coefficientSequence
      map_add' := fun f g => by ext n; exact coefficient_add f g n
      map_smul' := fun c f => by ext n; exact coefficient_smul c f n }
  refine F.mkContinuous 1 fun f => ?_
  change ‖(coefficientSequence f).toBCF‖ ≤ 1 * ‖f‖
  rw [one_mul]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 (coefficient_norm_le f)

@[simp] theorem coefficientMap_apply (f : DirichletKernelSpec.L1) (n : ℤ) :
    coefficientMap f n = fourierCoeff f n := rfl

theorem coefficientMap_norm_le : ‖coefficientMap‖ ≤ 1 := by
  apply coefficientMap.opNorm_le_bound zero_le_one
  intro f
  change ‖(coefficientSequence f).toBCF‖ ≤ 1 * ‖f‖
  rw [one_mul]
  exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 (coefficient_norm_le f)

theorem coefficientMap_injective : Function.Injective coefficientMap := by
  intro f g h
  apply Lp.ext
  apply ExpandedFA.Fourier.TorusFourierBasis.l1_unique (2 * π) f g
    (L1.integrable_coeFn f) (L1.integrable_coeFn g)
  intro n
  exact congrArg (fun a : CoefficientSpace => a n) h

/-- The Dirichlet polynomial regarded as an element of the original L¹ space. -/
def kernelL1 (N : ℕ) : DirichletKernelSpec.L1 := ContinuousMap.toLp 1 haar ℂ (kernel N)

theorem kernelL1_coefficient (N : ℕ) (n : ℤ) :
    fourierCoeff (kernelL1 N) n = if n ∈ frequencies N then 1 else 0 := by
  calc
    _ = fourierCoeff (kernel N) n :=
      congrFun (fourierCoeff_congr_ae (ContinuousMap.coeFn_toAEEqFun haar (kernel N))) n
    _ = _ := DirichletKernel.kernel_fourierCoeff N n

theorem kernelL1_norm (N : ℕ) : ‖kernelL1 N‖ = lebesgueConstant N := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae ((ContinuousMap.coeFn_toAEEqFun haar (kernel N)).fun_comp norm)

theorem kernelL1_coefficient_norm_le (N : ℕ) : ‖coefficientMap (kernelL1 N)‖ ≤ 1 := by
  change ‖(coefficientMap (kernelL1 N)).toBCF‖ ≤ 1
  apply (BoundedContinuousFunction.norm_le zero_le_one).2
  intro n
  change ‖fourierCoeff (kernelL1 N) n‖ ≤ 1
  rw [kernelL1_coefficient]
  split_ifs <;> simp

theorem coefficientMap_not_surjective : ¬ Function.Surjective coefficientMap := by
  intro hsurj
  obtain ⟨S, hS, _, _⟩ := ExpandedFA.P1.C08BoundedInverse.bounded_inverse
    ℂ DirichletKernelSpec.L1 CoefficientSpace coefficientMap
    ⟨coefficientMap_injective, hsurj⟩
  have hbound (N : ℕ) : lebesgueConstant N ≤ ‖S‖ := by
    rw [← kernelL1_norm N, ← hS (kernelL1 N)]
    exact (S.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg S)
      (kernelL1_coefficient_norm_le N))
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((tendsto_atTop.1 DirichletKernel.kernel_norm_divergence) (‖S‖ + 1))
  linarith [hbound N, hN N le_rfl]

theorem coefficient_map_failure : CoefficientMapFailure :=
  ⟨coefficientMap, coefficientMap_apply, coefficientMap_norm_le,
    coefficientMap_injective, coefficientMap_not_surjective⟩

end ExpandedFA.PartIV.FourierFailures
