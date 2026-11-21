import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HeatFundamental
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ProperSupportConvolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ContDiff Distributions Pointwise

namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

@[simp] theorem heatKernel_of_nonpos {d : ℕ} {z : Domain (d+1)} (hz : z 0 ≤ 0) :
    heatKernel d z = 0 := by simp [heatKernel, not_lt.mpr hz]

@[simp] theorem heatKernel_cons {d : ℕ} {t : ℝ} (ht : 0 < t) (x : Domain d) :
    heatKernel d (Fin.cons t x) = gaussianSlice d t x := by simp [heatKernel, ht]

@[simp] theorem delta_apply (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (φ : SpaceTimeTests 𝕜 d) :
    delta 𝕜 d φ = φ 0 := rfl

/-- Tensor-product form of the Gaussian: one normalized factor per spatial coordinate. -/
theorem gaussianSlice_eq_prod (d : ℕ) {t : ℝ} (ht : 0 < t) (x : Domain d) :
    gaussianSlice d t x =
      ∏ i : Fin d, (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x i)^2 / (4*t)) := by
  have hA : 0 < 4 * Real.pi * t := by positivity
  have hpow : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) =
      (Real.sqrt (4 * Real.pi * t))⁻¹ ^ d := by
    rw [show -(d : ℝ) / 2 = -(1 / 2 : ℝ) * (d : ℝ) by ring,
      Real.rpow_mul_natCast hA.le, Real.rpow_neg hA.le, Real.sqrt_eq_rpow]
  rw [gaussianSlice, hpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin,
    ← Real.exp_sum]
  congr 1
  simp only [spatialSquare, neg_div, Finset.sum_div, Finset.sum_neg_distrib]

/-- The normalization of a single coordinate. -/
theorem integral_gaussian_factor {t : ℝ} (ht : 0 < t) :
    (∫ y : ℝ, (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-y^2 / (4*t))) = 1 := by
  have hA : 0 < 4 * Real.pi * t := by positivity
  have heq : (fun y : ℝ => Real.exp (-y^2 / (4*t))) =
      (fun y => Real.exp (-(1 / (4*t)) * y^2)) := by funext y; congr 1; ring
  rw [integral_const_mul, heq, integral_gaussian]
  have hp : Real.pi / (1 / (4*t)) = 4 * Real.pi * t := by field_simp
  rw [hp, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hA))]

/-- Mass one and absolute integrability in every spatial dimension. -/
theorem slice_mass : Specs.ExpandedFA.PartIV.HeatFundamental.sliceMassType := by
  intro d t ht
  have heq := funext (gaussianSlice_eq_prod d ht)
  have hf : Integrable (fun y : ℝ =>
      (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-y^2 / (4*t))) := by
    convert (integrable_exp_neg_mul_sq (by positivity : 0 < 1/(4*t))).const_mul
      (Real.sqrt (4 * Real.pi * t))⁻¹ using 1
    funext y
    congr 2
    ring
  constructor
  · rw [heq]
    exact Integrable.fintype_prod (fun _ => hf)
  · rw [heq]
    change (∫ x : Fin d → ℝ, ∏ i : Fin d,
      (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(x i)^2 / (4*t))) = 1
    rw [integral_fintype_prod_volume_eq_prod
      (fun (_ : Fin d) (y : ℝ) =>
        (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-y^2 / (4*t)))]
    simp [integral_gaussian_factor ht]

theorem gaussianSlice_nonneg (d : ℕ) {t : ℝ} (ht : 0 < t) (x : Domain d) :
    0 ≤ gaussianSlice d t x := by
  unfold gaussianSlice
  positivity

theorem heatKernel_nonneg (d : ℕ) (z : Domain (d+1)) : 0 ≤ heatKernel d z := by
  unfold heatKernel
  split_ifs with ht
  · exact gaussianSlice_nonneg d ht _
  · exact le_rfl

theorem heatKernel_measurable (d : ℕ) : Measurable (heatKernel d) := by
  have heq : heatKernel d = fun z : Domain (d+1) =>
      if 0 < z 0 then
        Real.exp (Real.log (4 * Real.pi * z 0) * (-(d : ℝ) / 2)) *
          Real.exp (-spatialSquare (Fin.tail z) / (4 * z 0)) else 0 := by
    funext z
    by_cases ht : 0 < z 0
    · simp [heatKernel, ht, gaussianSlice, Real.rpow_def_of_pos (by positivity : 0 < 4 * Real.pi * z 0)]
    · simp [heatKernel, ht]
  rw [heq]
  apply Measurable.ite ((isOpen_lt continuous_const (continuous_apply 0)).measurableSet)
  · unfold spatialSquare Fin.tail
    fun_prop
  · exact measurable_const

/-- Integrability over an arbitrary bounded time slab; space is not truncated. -/
theorem heatKernel_integrable_slab (d : ℕ) (a b : ℝ) :
    IntegrableOn (heatKernel d) {z : Domain (d+1) | z 0 ∈ Icc a b} := by
  classical
  let g : ℝ × Domain d → ℝ := fun p =>
    if p.1 ∈ Icc a b then heatKernel d (Fin.cons p.1 p.2) else 0
  have hgmeas : Measurable g := by
    change Measurable (fun p : ℝ × Domain d =>
      if p.1 ∈ Icc a b then heatKernel d (Fin.cons p.1 p.2) else 0)
    apply Measurable.ite
    · exact measurable_fst measurableSet_Icc
    · apply (heatKernel_measurable d).comp
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using measurable_fst
      · simpa only [Fin.cons_succ, Function.comp_def] using
          (((continuous_apply j).comp continuous_snd).measurable :
            Measurable (fun p : ℝ × Domain d => p.2 j))
    · exact measurable_const
  have hgint : Integrable g := by
    apply (integrable_prod_iff hgmeas.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t => by
        by_cases ht : t ∈ Icc a b ∧ 0 < t
        · simpa only [g, ite_eq_left ht.1, heatKernel_cons ht.2] using (slice_mass d t ht.2).1
        · have hzero : (fun y : Domain d => g (t,y)) = 0 := by
            funext y
            simp only [g, heatKernel, Fin.cons_zero, Fin.tail_cons]
            split_ifs <;> simp_all
          rw [hzero]
          exact integrable_zero _ _ _
    · have hbound : Integrable ((Icc a b).indicator (fun _ : ℝ => (1 : ℝ))) :=
        (integrableOn_const (isCompact_Icc.measure_ne_top) :
          IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a b)).integrable_indicator
          measurableSet_Icc
      apply hbound.mono' hgmeas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun t => by
        by_cases ht : t ∈ Icc a b ∧ 0 < t
        · have hmass : (∫ y : Domain d, ‖g (t,y)‖) = 1 := by
            simp only [g, ite_eq_left ht.1, heatKernel_cons ht.2,
              Real.norm_eq_abs, abs_of_nonneg (gaussianSlice_nonneg d ht.2 _)]
            exact (slice_mass d t ht.2).2
          rw [hmass]
          simp [ht.1]
        · have hzero : (fun y : Domain d => ‖g (t,y)‖) = 0 := by
            funext y
            simp only [g, heatKernel, Fin.cons_zero, Fin.tail_cons]
            split_ifs <;> simp_all
          rw [hzero]
          simpa using Set.indicator_nonneg (fun (_ : ℝ) _ => (zero_le_one : (0 : ℝ) ≤ 1)) t
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  have hc := he.integrable_comp_of_integrable hgint
  have heq : (fun z => g (e z)) =
      {z : Domain (d+1) | z 0 ∈ Icc a b}.indicator (heatKernel d) := by
    funext z
    simp [g, e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Set.indicator_apply]
  change Integrable (fun z => g (e z)) at hc
  rw [heq] at hc
  exact (integrable_indicator_iff ((measurable_pi_apply 0) measurableSet_Icc)).1 hc

/-- The slice mass bound controls the space-time singularity at time zero. -/
theorem heatKernel_locallyIntegrable_real (d : ℕ) : LocallyIntegrable (heatKernel d) := by
  apply locallyIntegrable_iff.2
  intro K hK
  obtain ⟨a, ha⟩ := (hK.image (continuous_apply 0)).bddBelow
  obtain ⟨b, hb⟩ := (hK.image (continuous_apply 0)).bddAbove
  apply (heatKernel_integrable_slab d a b).mono_set
  intro z hz
  exact ⟨ha ⟨z, hz, rfl⟩, hb ⟨z, hz, rfl⟩⟩

/-- Scalar extension preserves local integrability, including over ℂ. -/
theorem local_integrability : Specs.ExpandedFA.PartIV.HeatFundamental.localIntegrabilityType := by
  intro 𝕜 _ d
  have hf := (RCLike.ofRealCLM (K := 𝕜)).locallyIntegrableOn_comp
    (locallyIntegrableOn_univ.mpr (heatKernel_locallyIntegrable_real d))
  exact locallyIntegrableOn_univ.mp hf

/-- The spatial dilation used at the initial boundary, with its exact Jacobian. -/
theorem gaussianSlice_scaling (d : ℕ) {t : ℝ} (ht : 0 < t) (y : Domain d) :
    gaussianSlice d t (Real.sqrt t • y) =
      ((Real.sqrt t) ^ d)⁻¹ * gaussianSlice d 1 y := by
  rw [gaussianSlice_eq_prod d ht]
  have hs : Real.sqrt (4 * Real.pi * t) = Real.sqrt (4 * Real.pi) * Real.sqrt t :=
    Real.sqrt_mul (by positivity) t
  calc
    _ = ∏ i : Fin d, (Real.sqrt t)⁻¹ *
        ((Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-(y i)^2 / 4)) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Pi.smul_apply, smul_eq_mul]
      have he : -(Real.sqrt t * y i)^2 / (4*t) = -(y i)^2 / 4 := by
        rw [mul_pow, Real.sq_sqrt ht.le]
        field_simp
      rw [he, hs, mul_inv]
      ring
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, inv_pow]
      congr 1
      symm
      simpa only [mul_one] using gaussianSlice_eq_prod d zero_lt_one y

/-- Exact rescaling of the initial test pairing. -/
theorem initial_pairing_rescaling {𝕜 : Type} [RCLike 𝕜] (d : ℕ)
    (φ : SpaceTimeTests 𝕜 d) {t : ℝ} (ht : 0 < t) :
    (∫ x : Domain d, gaussianSlice d t x • φ (Fin.cons t x)) =
      ∫ y : Domain d, gaussianSlice d 1 y • φ (Fin.cons t (Real.sqrt t • y)) := by
  have hdim : Module.finrank ℝ (Domain d) = d := by simp [Domain]
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure (Domain d))
    (fun x : Domain d => gaussianSlice d t x • φ (Fin.cons t x))
    (Real.sqrt t) (hR := Real.sqrt_nonneg t)
  rw [hdim] at hc
  have hl : (∫ y : Domain d,
      gaussianSlice d t (Real.sqrt t • y) • φ (Fin.cons t (Real.sqrt t • y))) =
      ((Real.sqrt t)^d)⁻¹ •
        ∫ y : Domain d, gaussianSlice d 1 y • φ (Fin.cons t (Real.sqrt t • y)) := by
    simp_rw [gaussianSlice_scaling d ht, mul_smul]
    exact integral_smul _ _
  rw [hl] at hc
  exact (smul_right_injective 𝕜 (inv_ne_zero (pow_ne_zero d
    (Real.sqrt_pos.2 ht).ne')) hc).symm

/-- After the Gaussian change of variables, dominated convergence supplies
the initial boundary contribution. This statement also allows the test's time
coordinate to tend to zero simultaneously with its spatial coordinate. -/
theorem scaled_initial_limit {𝕜 : Type} [RCLike 𝕜] (d : ℕ) (φ : SpaceTimeTests 𝕜 d) :
    Tendsto (fun t : ℝ => ∫ y : Domain d,
      gaussianSlice d 1 y • φ (Fin.cons t (Real.sqrt t • y)))
      (𝓝 0) (𝓝 (φ 0)) := by
  let B : ℝ := ‖TestFunction.toBoundedContinuousFunctionCLM 𝕜 φ‖
  have hg : Measurable (gaussianSlice d 1) := by
    unfold gaussianSlice spatialSquare
    fun_prop
  have hlim : ∀ y : Domain d,
      Tendsto (fun t : ℝ => φ (Fin.cons t (Real.sqrt t • y))) (𝓝 0) (𝓝 (φ 0)) := by
    intro y
    have hc : Continuous (fun t : ℝ => (Fin.cons t (Real.sqrt t • y) : Domain (d+1))) := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        fun_prop
      · simpa only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul] using
          Real.continuous_sqrt.mul_const (y j)
    have hz : (Fin.cons 0 (0 : Domain d) : Domain (d+1)) = 0 := by
      ext i
      exact Fin.cases (by simp) (fun j => by simp) i
    simpa only [Function.comp_def, Real.sqrt_zero, zero_smul, hz] using
      (φ.continuous.comp hc).tendsto 0
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun y : Domain d => gaussianSlice d 1 y * B)
    (F := fun t y => gaussianSlice d 1 y • φ (Fin.cons t (Real.sqrt t • y)))
    (f := fun y => gaussianSlice d 1 y • φ 0)
    (Filter.Eventually.of_forall fun t => by
      apply Measurable.aestronglyMeasurable
      apply hg.smul
      apply φ.continuous.measurable.comp
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
        fun_prop)
    (Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (gaussianSlice_nonneg d zero_lt_one y)]
      exact mul_le_mul_of_nonneg_left
        ((TestFunction.toBoundedContinuousFunctionCLM 𝕜 φ).norm_coe_le_norm _)
        (gaussianSlice_nonneg d zero_lt_one y))
    ((slice_mass d 1 zero_lt_one).1.mul_const B)
    (Filter.Eventually.of_forall fun y => tendsto_const_nhds.smul (hlim y))
  simpa only [integral_smul_const, (slice_mass d 1 zero_lt_one).2, one_smul] using h

/-- The Gaussian slices converge to the point source, with a moving time test. -/
theorem initial_boundary_limit {𝕜 : Type} [RCLike 𝕜] (d : ℕ) (φ : SpaceTimeTests 𝕜 d) :
    Tendsto (fun t : ℝ => ∫ x : Domain d,
      gaussianSlice d t x • φ (Fin.cons t x))
      (𝓝[>] 0) (𝓝 (φ 0)) := by
  apply ((scaled_initial_limit d φ).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (initial_pairing_rescaling d φ ht).symm

/-- The transpose signs of the heat operator, on the actual test space. -/
theorem heatOperator_transpose {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E : SpaceTimeDistribution 𝕜 d) (φ : SpaceTimeTests 𝕜 d) :
    heatOperator E φ = E (-testPartialCLM [0] φ -
      ∑ i : Fin d, testPartialCLM [i.succ, i.succ] φ) := by
  simp [heatOperator, Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue]

/-- The delta equation is equivalent to the full analytic weak identity. -/
theorem heatOperator_eq_delta_iff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E : SpaceTimeDistribution 𝕜 d) (hE : HasHeatKernelPairing E) :
    heatOperator E = delta 𝕜 d ↔ ∀ φ : SpaceTimeTests 𝕜 d,
      (∫ z : Domain (d+1), (heatKernel d z : 𝕜) *
        (-(testPartialCLM [0] φ) z -
          ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z)) = φ 0 := by
  have hpair (φ : SpaceTimeTests 𝕜 d) :
      heatOperator E φ = ∫ z : Domain (d+1), (heatKernel d z : 𝕜) *
        (-(testPartialCLM [0] φ) z -
          ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z) := by
    rw [heatOperator_transpose, hE]
    congr 1
    funext z
    simp
  constructor
  · intro he φ
    rw [← hpair φ, he, delta_apply]
  · intro he
    ext φ
    rw [hpair φ, he φ, delta_apply]

/-- Causality propagates under support addition with no spatial restriction. -/
theorem future_add_subset (d : ℕ) (a : ℝ) :
    future d 0 + future d a ⊆ future d a := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  change a ≤ x 0 + y 0
  exact le_add_of_nonneg_left hx |>.trans' hy

/-- Once a kernel distribution with causal support is supplied, the accepted
proper convolution theorem gives a convolution and the causal support bound.
No fundamental-solution identity is assumed or proved by this helper. -/
theorem convolution_exists_causal {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E f : SpaceTimeDistribution 𝕜 d) (hE : distributionSupport E ⊆ future d 0)
    (hf : IsCompact (distributionSupport f)) :
    ∃ u : SpaceTimeDistribution 𝕜 d, IsProperConvolution E f u ∧
      distributionSupport u ⊆ distributionSupport E + distributionSupport f ∧
      ∀ a : ℝ, distributionSupport f ⊆ future d a → distributionSupport u ⊆ future d a := by
  obtain ⟨u, hu, _⟩ := ProperSupportConvolution.convolution_existence 𝕜 (d+1) E f
    (ProperSupportConvolution.compact_distribution_suffices 𝕜 (d+1) E f (Or.inr hf))
  have hs := ProperSupportConvolution.convolution_support 𝕜 (d+1) E f u hu
  refine ⟨u, hu, hs, ?_⟩
  intro a ha
  exact hs.trans ((Set.add_subset_add hE ha).trans (future_add_subset d a))

/-- The explicit density pairing already forces the causal support bound. -/
theorem causal_support : Specs.ExpandedFA.PartIV.HeatFundamental.causalSupportType := by
  intro 𝕜 _ d E hE z hz
  by_contra hn
  have hneg : z 0 < 0 := lt_of_not_ge hn
  have hvan : z ∈ vanishingRegion E := by
    apply Set.mem_sUnion_of_mem
      (show z ∈ {y : Domain (d+1) | y 0 < 0} from hneg)
    refine ⟨isOpen_lt (continuous_apply 0) continuous_const, subset_univ _, ?_⟩
    intro φ hφ
    rw [hE φ]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : y 0 < 0
      · simp [heatKernel_of_nonpos hy.le]
      · have hp : φ y = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hm
          exact hy (hφ hm)
        simp [hp]
  exact hz.2 hvan

/-- The displayed density defines an actual continuous scalar-linear distribution
and has causal distribution support. The heat equation is a further obligation. -/
theorem kernel_distribution_exists :
    Specs.ExpandedFA.PartIV.HeatFundamental.kernelDistributionType := by
  intro 𝕜 _ d
  let E : SpaceTimeDistribution 𝕜 d := regularDistribution volume (fun z => (heatKernel d z : 𝕜))
  have hE : HasHeatKernelPairing E := by
    intro φ
    exact regularDistribution_apply _ _
      (locallyIntegrableOn_univ.mpr (local_integrability 𝕜 d)) φ
  exact ⟨E, hE, causal_support 𝕜 d E hE⟩

/-- Constant-coefficient heat differentiation cannot enlarge support. -/
theorem heatOperator_support {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E : SpaceTimeDistribution 𝕜 d) :
    distributionSupport (heatOperator E) ⊆ distributionSupport E := by
  intro z hz
  refine ⟨Set.mem_univ z, ?_⟩
  rintro ⟨V, ⟨hV, hVU, hEV⟩, hzV⟩
  apply hz.2
  refine ⟨V, ⟨hV, hVU, ?_⟩, hzV⟩
  intro φ hφ
  have he (w : List (Fin (d+1))) : E (testPartialCLM w φ) = 0 :=
    hEV _ ((ProperSupportConvolution.testPartial_tsupport_subset w φ).trans hφ)
  simp [heatOperator, Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue, he]

/-- A cutoff remains admissible after shrinking the first distribution support. -/
theorem admissible_cutoff_mono_left {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {E E' f : ScalarDistribution 𝕜 (⊤ : Opens (Domain n))}
    {φ : Tests 𝕜 (⊤ : Opens (Domain n))} {χ : ProductTests ℝ n}
    (h : AdmissibleConvolutionCutoff E f φ χ)
    (hs : distributionSupport E' ⊆ distributionSupport E) :
    AdmissibleConvolutionCutoff E' f φ χ := by
  obtain ⟨V, hV, hSV, hχ⟩ := h
  exact ⟨V, hV, fun p hp => hSV ⟨⟨hs hp.1.1, hp.1.2⟩, hp.2⟩, hχ⟩

/-- The whole heat operator commutes with proper convolution with compact data.
This includes the finite linear combination, in addition to the upstream
individual coordinate derivative formulas. -/
theorem heatOperator_convolution {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (E f u : SpaceTimeDistribution 𝕜 d) (hf : IsCompact (distributionSupport f))
    (hu : IsProperConvolution E f u) :
    IsProperConvolution (heatOperator E) f (heatOperator u) := by
  classical
  let D := Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue 𝕜 (d+1) ⊤
  have hconv : Convolvable (heatOperator E) f :=
    ProperSupportConvolution.compact_distribution_suffices 𝕜 (d+1) _ f (Or.inr hf)
  refine ⟨hconv, ⟨ProperSupportConvolution.iteratedTensor (heatOperator E) f,
    ProperSupportConvolution.iteratedTensor_isTensorProduct _ _⟩, ?_⟩
  intro T hT φ χ hχ
  obtain ⟨χ₀, hχ₀⟩ := ProperSupportConvolution.cutoff_existence 𝕜 (d+1) E f hu.1 φ
  have hχ₀P := admissible_cutoff_mono_left hχ₀ (heatOperator_support E)
  have hp (w : List (Fin (d+1))) : D w u φ =
      ProperSupportConvolution.iteratedTensor (D w E) f (cutoffAdditionTest χ₀ φ) := by
    have hD := (ProperSupportConvolution.convolution_derivatives
      𝕜 (d+1) E f u w hu).1
    exact hD.2.2 _ (ProperSupportConvolution.iteratedTensor_isTensorProduct _ _)
      φ χ₀ (admissible_cutoff_mono_left hχ₀
        (ProperSupportConvolution.derivative_support 𝕜 (d+1) E w))
  have hP : heatOperator u φ =
      ProperSupportConvolution.iteratedTensor (heatOperator E) f (cutoffAdditionTest χ₀ φ) := by
    simp only [ProperSupportConvolution.iteratedTensor_apply, heatOperator,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply]
    change D [0] u φ - ∑ i : Fin d, D [i.succ, i.succ] u φ = _
    rw [hp [0]]
    simp only [ProperSupportConvolution.iteratedTensor_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hp [i.succ, i.succ]
  rw [hP]
  exact ProperSupportConvolution.cutoff_independence 𝕜 (d+1) (heatOperator E) f
    hconv _ T (ProperSupportConvolution.iteratedTensor_isTensorProduct _ _) hT φ χ₀ χ hχ₀P hχ

/-- The scalar-linear point source has exactly its stated point support. -/
theorem delta_support (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    distributionSupport (delta 𝕜 d) = {0} := by
  have hs : distributionSupport (delta 𝕜 d) ⊆ {0} := by
    intro z hz
    by_contra hn
    apply hz.2
    refine ⟨({0} : Set (Domain (d+1)))ᶜ,
      ⟨isClosed_singleton.isOpen_compl, subset_univ _, ?_⟩, hn⟩
    intro φ hφ
    rw [delta_apply]
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact hφ hm (Set.mem_singleton _)
  have h0 : (0 : Domain (d+1)) ∈ distributionSupport (delta 𝕜 d) := by
    by_contra hn
    have hempty : distributionSupport (delta 𝕜 d) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro z hz
      have hz0 : z = 0 := hs hz
      exact hn (hz0 ▸ hz)
    have hzero := (ProperSupportConvolution.zero_support 𝕜 (d+1) (delta 𝕜 d)).1 hempty
    obtain ⟨χ, V, hV, h0V, hχ⟩ := cutoff_existence (d+1) ⊤ {0}
      isCompact_singleton (subset_univ _)
    let ψ : SpaceTimeTests 𝕜 d := TestFunction.postcompCLM (RCLike.ofRealCLM (K := 𝕜)) χ
    have hone : delta 𝕜 d ψ = 1 := by
      change (χ 0 : 𝕜) = 1
      rw [hχ (h0V (Set.mem_singleton _))]
      simp
    have hnone : delta 𝕜 d ψ = 0 := by rw [hzero]; rfl
    exact one_ne_zero (hone.symm.trans hnone)
  exact Set.Subset.antisymm hs (Set.singleton_subset_iff.2 h0)

/-- Convolution by the point source is the identity for the accepted
proper-support tensor/cutoff construction. -/
theorem convolution_delta_eq {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f w : SpaceTimeDistribution 𝕜 d) (hw : IsProperConvolution (delta 𝕜 d) f w) : w = f := by
  ext φ
  obtain ⟨χ, hχ⟩ := ProperSupportConvolution.cutoff_existence 𝕜 (d+1) (delta 𝕜 d) f hw.1 φ
  rw [hw.2.2 _ (ProperSupportConvolution.iteratedTensor_isTensorProduct _ _) φ χ hχ,
    ProperSupportConvolution.iteratedTensor_apply, delta_apply,
    ProperSupportConvolution.kernelActionTest_apply]
  obtain ⟨V, hV, hSV, hχV⟩ := hχ
  let W : Set (Domain (d+1)) :=
    (fun y => ((0 : Domain (d+1)), y)) ⁻¹' V ∪ (tsupport φ)ᶜ
  have hW : IsOpen W :=
    (hV.preimage (continuous_const.prodMk continuous_id)).union isClosed_closure.isOpen_compl
  have hsW : distributionSupport f ⊆ W := by
    intro y hy
    by_cases hφ : y ∈ tsupport φ
    · apply Or.inl
      apply hSV
      refine ⟨⟨?_, hy⟩, ?_⟩
      · rw [delta_support]
        exact Set.mem_singleton _
      · simpa using hφ
    · exact Or.inr hφ
  apply pairing_locality 𝕜 (d+1) ⊤ f _ φ W hW hsW
  intro y hy
  change χ (0,y) • φ (0+y) = φ y
  rcases hy with hy | hy
  · simp only [hχV hy, Pi.one_apply, one_smul, zero_add]
  · rw [zero_add, image_eq_zero_of_notMem_tsupport hy, smul_zero]

/-- With the weak heat identity established, all original distribution and
compact-data conclusions follow from the existing constructions. The hypothesis
isolates the analytic step from the distribution and convolution construction. -/
theorem fundamental_solution_of_weak_identity
    (hweak : Specs.ExpandedFA.PartIV.HeatFundamental.weakIdentityType) :
    Specs.ExpandedFA.PartIV.HeatFundamental.fundamentalSolutionType := by
  intro 𝕜 _ d
  obtain ⟨E, hE, hS⟩ := kernel_distribution_exists 𝕜 d
  have hP : heatOperator E = delta 𝕜 d :=
    (heatOperator_eq_delta_iff E hE).2 (hweak 𝕜 d)
  refine ⟨E, hE, hP, hS, ?_⟩
  intro f hf
  obtain ⟨u, hu, hSu, hcausal⟩ := convolution_exists_causal E f hS hf
  refine ⟨u, hu, ?_, hSu, hcausal⟩
  have hPu := heatOperator_convolution E f u hf hu
  rw [hP] at hPu
  exact convolution_delta_eq f (heatOperator u) hPu

/-- Truncations tend to the full weak pairing because its integrand is
absolutely integrable, including through the time-zero singularity. -/
theorem truncated_weak_pairing_limit {𝕜 : Type} [RCLike 𝕜] (d : ℕ)
    (φ : SpaceTimeTests 𝕜 d) :
    Tendsto (fun ε : ℝ => ∫ z : Domain (d+1) in {z | ε < z 0}, (heatKernel d z : 𝕜) *
      (-(testPartialCLM [0] φ) z -
        ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z))
      (𝓝[>] 0) (𝓝 (∫ z : Domain (d+1), (heatKernel d z : 𝕜) *
        (-(testPartialCLM [0] φ) z -
          ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z))) := by
  classical
  let ψ : SpaceTimeTests 𝕜 d := -testPartialCLM [0] φ -
    ∑ i : Fin d, testPartialCLM [i.succ, i.succ] φ
  let f : Domain (d+1) → 𝕜 := fun z => (heatKernel d z : 𝕜) * ψ z
  have hf : Integrable f := by
    have h := (local_integrability 𝕜 d).integrable_smul_left_of_hasCompactSupport
      ψ.continuous ψ.hasCompactSupport
    simpa only [smul_eq_mul, mul_comm] using h
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (fun z => ‖f z‖)
    (F := fun ε : ℝ => {z : Domain (d+1) | ε < z 0}.indicator f) (f := f)
    (Filter.Eventually.of_forall fun ε => hf.aestronglyMeasurable.indicator
      ((isOpen_lt continuous_const (continuous_apply 0)).measurableSet))
    (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ {z : Domain (d+1) | ε < z 0}
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, norm_zero]
        exact norm_nonneg _)
    hf.norm
    (Filter.Eventually.of_forall fun z => by
      by_cases hz : 0 < z 0
      · have he : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < z 0 :=
          (eventually_lt_nhds hz).filter_mono nhdsWithin_le_nhds
        apply tendsto_const_nhds.congr'
        filter_upwards [he] with ε hε
        exact (Set.indicator_of_mem (show z ∈ {z : Domain (d+1) | ε < z 0} from hε) f).symm
      · have hzero : f z = 0 := by simp [f, heatKernel, hz]
        have heq : (fun ε : ℝ => {z : Domain (d+1) | ε < z 0}.indicator f z) =
            (fun _ => f z) := by
          funext ε
          by_cases hε : z ∈ {z : Domain (d+1) | ε < z 0} <;> simp [hε, hzero]
        rw [heq]
        exact tendsto_const_nhds)
  have hi (ε : ℝ) : (∫ z : Domain (d+1), {z : Domain (d+1) | ε < z 0}.indicator f z) =
      ∫ z : Domain (d+1) in {z | ε < z 0}, f z :=
    integral_indicator ((isOpen_lt continuous_const (continuous_apply 0)).measurableSet)
  simp_rw [hi] at hlim
  have hfapply (z : Domain (d+1)) : f z = (heatKernel d z : 𝕜) *
      (-(testPartialCLM [0] φ) z -
        ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z) := by simp [f, ψ]
  simpa only [hfapply] using hlim

/-- All original conclusions reduce to the positive-time truncated identity;
the initial limit, integrability, convolution equation, and causality are proved here. -/
theorem fundamental_solution_of_truncated_identity :
    Specs.ExpandedFA.PartIV.HeatFundamental.truncatedAssemblyType := by
  intro htrunc
  apply fundamental_solution_of_weak_identity
  intro 𝕜 _ d φ
  apply tendsto_nhds_unique (truncated_weak_pairing_limit d φ)
  apply (initial_boundary_limit d φ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (htrunc 𝕜 d φ ε hε).symm

end ExpandedFA.PartIV.HeatFundamental


/-! Compact positive-time pairings and Fubini. -/

open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ContDiff Distributions Pointwise
namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

theorem integrableOn_future_of_compactSupport {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f : Domain (d+1) → 𝕜} {ε : ℝ}
    (hc : ContinuousOn f {z | ε ≤ z 0}) (hs : HasCompactSupport f) :
    IntegrableOn f {z | ε < z 0} := by
  let K := tsupport f ∩ {z : Domain (d+1) | ε ≤ z 0}
  have hK : IsCompact K := hs.inter_right (isClosed_le continuous_const (continuous_apply 0))
  have hi : IntegrableOn f K := (hc.mono inter_subset_right).integrableOn_compact hK
  apply hi.of_forall_sdiff_eq_zero (isOpen_lt continuous_const (continuous_apply 0)).measurableSet
  rintro z ⟨hz, hn⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact hn ⟨hmem, (show ε ≤ z 0 from le_of_lt hz)⟩

/-- Fubini with coordinate zero singled out as time. -/
theorem integral_halfspace_eq_integral_slices {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Domain (d+1) → 𝕜) (ε : ℝ)
    (hf : IntegrableOn f {z | ε < z 0}) :
    (∫ z : Domain (d+1) in {z | ε < z 0}, f z) =
      ∫ t : ℝ in Ioi ε, ∫ x : Domain d, f (Fin.cons t x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  let g := {z : Domain (d+1) | ε < z 0}.indicator f
  have hg : Integrable g := hf.integrable_indicator
    (isOpen_lt continuous_const (continuous_apply 0)).measurableSet
  have hi := he.symm.integrable_comp_of_integrable hg
  have heq : (fun p : ℝ × Domain d => g (e.symm p)) =
      fun p : ℝ × Domain d => (Ioi ε).indicator (fun t => f (Fin.cons t p.2)) p.1 := by
    funext p
    simp [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Set.indicator_apply]
  change Integrable (fun p => g (e.symm p)) at hi
  rw [heq, Measure.volume_eq_prod] at hi
  rw [← integral_indicator (isOpen_lt continuous_const (continuous_apply 0)).measurableSet]
  change (∫ z, g z) = _
  rw [← he.symm.integral_comp' g, heq, Measure.volume_eq_prod]
  rw [integral_prod _ hi]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases ht : t ∈ Ioi ε <;> simp [ht]

theorem contDiffOn_partialFunction {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {G : Domain (d+1) → 𝕜}
    (hG : ContDiffOn ℝ ∞ G {z | 0 < z 0}) (w : List (Fin (d+1))) :
    ContDiffOn ℝ ∞ (partialFunction w G) {z | 0 < z 0} := by
  induction w with
  | nil => exact hG
  | cons i w ih =>
    exact (ih.fderiv_of_isOpen (isOpen_lt continuous_const (continuous_apply 0)) (by simp)).clm_apply
      contDiffOn_const

theorem integrableOn_positive_coefficient_test {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {G : Domain (d+1) → 𝕜} {ε : ℝ} (hε : 0 < ε)
    (hG : ContinuousOn G {z | 0 < z 0}) (φ : SpaceTimeTests 𝕜 d) :
    IntegrableOn (fun z => G z * φ z) {z | ε < z 0} := by
  apply integrableOn_future_of_compactSupport
  · exact (hG.mono (fun z hz => lt_of_lt_of_le hε hz)).mul φ.continuous.continuousOn
  · exact φ.hasCompactSupport.mul_left

end ExpandedFA.PartIV.HeatFundamental

namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

theorem integrableOn_positive_smul_test {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {G : Domain (d+1) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hG : ContinuousOn G {z | 0 < z 0}) (φ : SpaceTimeTests 𝕜 d) :
    IntegrableOn (fun z => G z • φ z) {z | ε < z 0} := by
  simpa only [RCLike.real_smul_eq_coe_mul, Function.comp_def, RCLike.ofRealCLM_apply] using
    integrableOn_positive_coefficient_test hε
      ((RCLike.ofRealCLM (K := 𝕜)).continuous.comp_continuousOn hG) φ

end ExpandedFA.PartIV.HeatFundamental


/-! Transfer of the spatial derivatives. -/

open Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace HeatGreen

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]
  {μ : Measure E} [IsAddHaarMeasure μ]

lemma compact_integrable_smul {f : E → ℝ} {g : E → 𝕜}
    (hf : Continuous f) (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun x => f x • g x) μ :=
  (hf.smul hg).integrable_of_hasCompactSupport hc.smul_left

lemma integral_smul_fderiv_second_transfer {f : E → ℝ} {g : E → 𝕜}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (v : E) :
    (∫ x, f x • fderiv ℝ (fun y => fderiv ℝ g y v) x v ∂μ) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v • g x ∂μ := by
  let f₁ : E → ℝ := fun x => fderiv ℝ f x v
  let g₁ : E → 𝕜 := fun x => fderiv ℝ g x v
  have hf₁ : ContDiff ℝ ∞ f₁ := (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hg₁ : ContDiff ℝ ∞ g₁ := (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hcg₁ : HasCompactSupport g₁ := hc.fderiv_apply ℝ v
  have A := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := μ) (f := f) (g := g₁) (v := v)
    (compact_integrable_smul (hf.fderiv_right (m := ∞) (by simp) |>.clm_apply contDiff_const).continuous hg₁.continuous hcg₁)
    (compact_integrable_smul hf.continuous
      ((hg₁.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      (hcg₁.fderiv_apply ℝ v))
    (compact_integrable_smul hf.continuous hg₁.continuous hcg₁)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg₁.differentiable (by simp) x)
  have B := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := μ) (f := f₁) (g := g) (v := v)
    (compact_integrable_smul
      ((hf₁.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      hg.continuous hc)
    (compact_integrable_smul hf₁.continuous hg₁.continuous hcg₁)
    (compact_integrable_smul hf₁.continuous hg.continuous hc)
    (fun x _ => hf₁.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)
  change (∫ x, f x • fderiv ℝ g₁ x v ∂μ) = _
  rw [A]
  change -(∫ x, f₁ x • fderiv ℝ g x v ∂μ) = _
  rw [B, neg_neg]

end HeatGreen


namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

lemma contDiff_cons_slice (d : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (fun x : Domain d => (Fin.cons t x : Domain (d+1))) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using (contDiff_const : ContDiff ℝ ∞ (fun _ : Domain d => t))
  · simpa only [Fin.cons_succ] using (contDiff_apply ℝ (fun _ : Fin d => ℝ) j : ContDiff ℝ ∞ (fun x : Domain d => x j))

lemma hasCompactSupport_cons_slice {d : ℕ} {f : Domain (d+1) → 𝕜}
    [Zero 𝕜] (hf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun x : Domain d => f (Fin.cons t x)) := by
  have htail : Continuous (Fin.tail : Domain (d+1) → Domain d) := by
    apply continuous_pi
    intro j
    exact continuous_apply j.succ
  have hK := hf.image htail
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  refine ⟨Fin.cons t x, subset_tsupport f ?_, by simp⟩
  exact hx

lemma fderiv_cons_slice {d : ℕ} {𝕜 : Type*} [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : Domain (d+1) → 𝕜} (t : ℝ) (x v : Domain d)
    (hf : DifferentiableAt ℝ f (Fin.cons t x)) :
    fderiv ℝ (fun y : Domain d => f (Fin.cons t y)) x v =
      fderiv ℝ f (Fin.cons t x) (Fin.cons 0 v) := by
  have h := hf.hasFDerivAt.comp x ((hasFDerivAt_const t x).finCons (hasFDerivAt_id x))
  change (fderiv ℝ (f ∘ Fin.cons t) x) v = _
  rw [h.fderiv]
  rfl

lemma cons_coordinateVector {d : ℕ} (i : Fin d) :
    (Fin.cons 0 (coordinateVector i) : Domain (d+1)) = coordinateVector i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [coordinateVector]
  · simp [coordinateVector, Pi.single_apply, Fin.succ_inj]

lemma testPartial_cons_slice_single {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    (t : ℝ) (x : Domain d) (i : Fin d) :
    fderiv ℝ (fun y : Domain d => φ (Fin.cons t y)) x (coordinateVector i) =
      (testPartialCLM [i.succ] φ) (Fin.cons t x) := by
  rw [fderiv_cons_slice t x _ (φ.contDiff.differentiable (by simp) _),
    cons_coordinateVector, testPartial_single_apply]

lemma testPartial_cons_slice_double {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    (t : ℝ) (x : Domain d) (i : Fin d) :
    fderiv ℝ (fun y : Domain d =>
      fderiv ℝ (fun z : Domain d => φ (Fin.cons t z)) y (coordinateVector i))
      x (coordinateVector i) =
      (testPartialCLM [i.succ, i.succ] φ) (Fin.cons t x) := by
  have hfun : (fun y : Domain d =>
      fderiv ℝ (fun z : Domain d => φ (Fin.cons t z)) y (coordinateVector i)) =
      (fun y => (testPartialCLM [i.succ] φ) (Fin.cons t y)) := by
    funext y
    exact testPartial_cons_slice_single φ t y i
  rw [hfun, testPartial_cons_slice_single]
  rfl


lemma integral_spatial_slice_transfer {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    {f : Domain d → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (i : Fin d) :
    (∫ x : Domain d, f x • (testPartialCLM [i.succ, i.succ] φ) (Fin.cons t x)) =
      ∫ x : Domain d,
        fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector i)) x (coordinateVector i) •
          φ (Fin.cons t x) := by
  have h := HeatGreen.integral_smul_fderiv_second_transfer
    (μ := volume) hf (φ.contDiff.comp (contDiff_cons_slice d t))
    (hasCompactSupport_cons_slice φ.hasCompactSupport t) (coordinateVector i)
  simpa only [Function.comp_def, testPartial_cons_slice_double φ t] using h


lemma fderiv_cons_slice_double {d : ℕ} {𝕜 : Type*}
    [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜]
    {f : Domain (d+1) → 𝕜} (t : ℝ) (x v : Domain d)
    (hf : ∀ y : Domain d, ContDiffAt ℝ ∞ f (Fin.cons t y)) :
    fderiv ℝ (fun y : Domain d =>
      fderiv ℝ (fun z : Domain d => f (Fin.cons t z)) y v) x v =
    fderiv ℝ (fun y : Domain (d+1) => fderiv ℝ f y (Fin.cons 0 v))
      (Fin.cons t x) (Fin.cons 0 v) := by
  have hfun : (fun y : Domain d => fderiv ℝ (fun z : Domain d => f (Fin.cons t z)) y v) =
      (fun y => fderiv ℝ f (Fin.cons t y) (Fin.cons 0 v)) := by
    funext y
    exact fderiv_cons_slice t y v ((hf y).differentiableAt (by simp))
  rw [hfun]
  exact fderiv_cons_slice t x v
    (((hf x).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const |>.differentiableAt (by simp))

lemma integral_spatial_slice_ambient_transfer {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    {G : Domain (d+1) → ℝ} (t : ℝ)
    (hG : ∀ x : Domain d, ContDiffAt ℝ ∞ G (Fin.cons t x)) (i : Fin d) :
    (∫ x : Domain d, G (Fin.cons t x) •
      (testPartialCLM [i.succ, i.succ] φ) (Fin.cons t x)) =
      ∫ x : Domain d, partialFunction [i.succ, i.succ] G (Fin.cons t x) •
          φ (Fin.cons t x) := by
  have hslice : ContDiff ℝ ∞ (fun x : Domain d => G (Fin.cons t x)) := by
    exact contDiff_iff_contDiffAt.mpr fun x =>
      (hG x).comp x (contDiff_cons_slice d t).contDiffAt
  rw [integral_spatial_slice_transfer φ hslice t i]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [fderiv_cons_slice_double t x _ hG, cons_coordinateVector]
    rfl


lemma integrableOn_positive_coefficient_smul_test {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {G : Domain (d+1) → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hG : ContinuousOn G {z | 0 < z 0})
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1)))) :
    IntegrableOn (fun z => G z • φ z) {z | ε < z 0} := by
  apply integrableOn_future_of_compactSupport
  · exact (hG.mono (fun z hz => lt_of_lt_of_le hε hz)).smul φ.continuous.continuousOn
  · exact HasCompactSupport.smul_left (f := G) (f' := (φ : Domain (d+1) → 𝕜)) φ.hasCompactSupport

lemma halfspace_spatial_transfer {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {G : Domain (d+1) → ℝ} (hG : ContDiffOn ℝ ∞ G {z | 0 < z 0})
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    (∫ z : Domain (d+1) in {z | ε < z 0}, G z • (testPartialCLM [i.succ, i.succ] φ) z) =
      ∫ z : Domain (d+1) in {z | ε < z 0}, partialFunction [i.succ, i.succ] G z • φ z := by
  have hleft := integrableOn_positive_coefficient_smul_test hε hG.continuousOn
    (testPartialCLM [i.succ, i.succ] φ)
  have hright := integrableOn_positive_coefficient_smul_test hε
    (contDiffOn_partialFunction hG [i.succ, i.succ]).continuousOn φ
  rw [integral_halfspace_eq_integral_slices _ ε hleft,
    integral_halfspace_eq_integral_slices _ ε hright]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  apply integral_spatial_slice_ambient_transfer φ t
  intro x
  apply (hG (Fin.cons t x) (by simpa using lt_trans hε ht)).contDiffAt
  exact (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds
    (by simpa using lt_trans hε ht)

end ExpandedFA.PartIV.HeatFundamental


/-! The time boundary term. -/

open Set MeasureTheory Filter
open scoped Topology ContDiff Distributions

namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

lemma hasDerivAt_cons_time {d : ℕ} (x : Domain d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Fin.cons s x) (coordinateVector 0) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [coordinateVector] using hasDerivAt_id' t
  · simpa [coordinateVector] using hasDerivAt_const t (x j)

lemma hasDerivAt_test_time {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    (x : Domain d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (Fin.cons s x))
      ((testPartialCLM [0] φ) (Fin.cons t x)) t := by
  rw [testPartial_single_apply]
  exact (φ.contDiff.differentiable (by simp) (Fin.cons t x)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_cons_time x t)

lemma test_time_eventually_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1)))) :
    ∀ᶠ t : ℝ in atTop, ∀ x : Domain d, φ (Fin.cons t x) = 0 := by
  obtain ⟨b, hb⟩ := φ.hasCompactSupport.bddAbove_image
    (continuous_apply (0 : Fin (d+1))).continuousOn
  filter_upwards [eventually_gt_atTop b] with t ht x
  by_contra hx
  have hz : Fin.cons t x ∈ tsupport φ := subset_closure hx
  have hle : t ≤ b := hb ⟨Fin.cons t x, hz, by simp⟩
  exact (not_le_of_gt ht) hle

lemma integral_time_ibp {𝕜 : Type} [RCLike 𝕜] (a : ℝ)
    (G G' φ φ' : ℝ → 𝕜)
    (hG : ∀ t ∈ Ici a, HasDerivAt G (G' t) t)
    (hφ : ∀ t ∈ Ici a, HasDerivAt φ (φ' t) t)
    (hi₁ : IntegrableOn (fun t => G' t * φ t) (Ioi a))
    (hi₂ : IntegrableOn (fun t => G t * φ' t) (Ioi a))
    (hzero : ∀ᶠ t in atTop, φ t = 0) :
    (∫ t in Ioi a, -(G t * φ' t)) =
      G a * φ a + ∫ t in Ioi a, G' t * φ t := by
  have hz : Tendsto (fun t => G t * φ t) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hzero] with t ht
    simp [ht]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => (hG t ht).mul (hφ t ht)) (hi₁.add hi₂) hz
  rw [integral_add hi₁ hi₂, zero_sub] at h
  rw [integral_neg]
  change _ + _ = -(G a * φ a) at h
  linear_combination -h

lemma integral_test_time_ibp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : TopologicalSpace.Opens (Domain (d+1))))
    (G G' : ℝ → 𝕜) (x : Domain d) (a : ℝ)
    (hG : ∀ t ∈ Ici a, HasDerivAt G (G' t) t)
    (hi₁ : IntegrableOn (fun t => G' t * φ (Fin.cons t x)) (Ioi a))
    (hi₂ : IntegrableOn
      (fun t => G t * (testPartialCLM [0] φ) (Fin.cons t x)) (Ioi a)) :
    (∫ t in Ioi a, -(G t * (testPartialCLM [0] φ) (Fin.cons t x))) =
      G a * φ (Fin.cons a x) + ∫ t in Ioi a, G' t * φ (Fin.cons t x) := by
  apply integral_time_ibp a G G' (fun t => φ (Fin.cons t x))
    (fun t => (testPartialCLM [0] φ) (Fin.cons t x)) hG
    (fun t _ => hasDerivAt_test_time φ x t) hi₁ hi₂
  filter_upwards [test_time_eventually_zero φ] with t ht
  exact ht x

theorem halfspace_time_fubini {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Domain (d+1) → 𝕜) (ε : ℝ)
    (hf : IntegrableOn f {z | ε < z 0}) :
    Integrable (fun x : Domain d => ∫ t in Ioi ε, f (Fin.cons t x)) ∧
    (∀ᵐ x : Domain d, IntegrableOn (fun t => f (Fin.cons t x)) (Ioi ε)) ∧
    (∫ z : Domain (d+1) in {z | ε < z 0}, f z) =
      ∫ x : Domain d, ∫ t in Ioi ε, f (Fin.cons t x) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  let g := {z : Domain (d+1) | ε < z 0}.indicator f
  have hg : Integrable g := hf.integrable_indicator
    (isOpen_lt continuous_const (continuous_apply 0)).measurableSet
  have hi := he.symm.integrable_comp_of_integrable hg
  have heq : (fun p : ℝ × Domain d => g (e.symm p)) =
      fun p : ℝ × Domain d => (Ioi ε).indicator (fun t => f (Fin.cons t p.2)) p.1 := by
    funext p
    simp [g, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Set.indicator_apply]
  change Integrable (fun p => g (e.symm p)) at hi
  rw [heq, Measure.volume_eq_prod] at hi
  refine ⟨?_, ?_, ?_⟩
  · simpa only [integral_indicator measurableSet_Ioi] using hi.integral_prod_right
  · filter_upwards [hi.prod_left_ae] with x hx
    exact (integrable_indicator_iff measurableSet_Ioi).mp hx
  · rw [← integral_indicator (isOpen_lt continuous_const (continuous_apply 0)).measurableSet]
    change (∫ z, g z) = _
    rw [← he.symm.integral_comp' g, heq, Measure.volume_eq_prod,
      integral_prod_symm _ hi]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => integral_indicator measurableSet_Ioi

theorem integral_halfspace_time_ibp {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : SpaceTimeTests 𝕜 d) (G G' : Domain (d+1) → 𝕜) (ε : ℝ)
    (hG : ∀ x : Domain d, ∀ t ∈ Ici ε,
      HasDerivAt (fun s => G (Fin.cons s x)) (G' (Fin.cons t x)) t)
    (hi₁ : IntegrableOn (fun z => G' z * φ z) {z | ε < z 0})
    (hi₂ : IntegrableOn (fun z => G z * (testPartialCLM [0] φ) z)
      {z | ε < z 0}) :
    Integrable (fun x : Domain d => G (Fin.cons ε x) * φ (Fin.cons ε x)) ∧
    (∫ z : Domain (d+1) in {z | ε < z 0}, G z * (-(testPartialCLM [0] φ) z)) =
      (∫ x : Domain d, G (Fin.cons ε x) * φ (Fin.cons ε x)) +
        ∫ z : Domain (d+1) in {z | ε < z 0}, G' z * φ z := by
  have h₁ := halfspace_time_fubini (fun z => G' z * φ z) ε hi₁
  have h₂ := halfspace_time_fubini (fun z => G z * (testPartialCLM [0] φ) z) ε hi₂
  have heq : (fun x : Domain d => -(∫ t in Ioi ε,
      G (Fin.cons t x) * (testPartialCLM [0] φ) (Fin.cons t x))) =ᵐ[volume]
      (fun x : Domain d => G (Fin.cons ε x) * φ (Fin.cons ε x) +
        ∫ t in Ioi ε, G' (Fin.cons t x) * φ (Fin.cons t x)) := by
    filter_upwards [h₁.2.1, h₂.2.1] with x hx₁ hx₂
    rw [← integral_neg]
    exact integral_test_time_ibp φ (fun t => G (Fin.cons t x))
      (fun t => G' (Fin.cons t x)) x ε (hG x) hx₁ hx₂
  have hb : Integrable (fun x : Domain d => G (Fin.cons ε x) * φ (Fin.cons ε x)) := by
    apply (h₂.1.neg.sub h₁.1).congr
    filter_upwards [heq] with x hx
    change -(∫ t in Ioi ε, G (Fin.cons t x) * (testPartialCLM [0] φ) (Fin.cons t x)) -
      (∫ t in Ioi ε, G' (Fin.cons t x) * φ (Fin.cons t x)) = _
    linear_combination hx
  refine ⟨hb, ?_⟩
  simp only [mul_neg, integral_neg]
  rw [h₁.2.2, h₂.2.2]
  have h := integral_congr_ae heq
  rw [integral_neg, integral_add hb h₁.1] at h
  exact h


theorem integral_halfspace_time_ibp_real {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : SpaceTimeTests 𝕜 d) (G : Domain (d+1) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hG : ContDiffOn ℝ ∞ G {z | 0 < z 0}) :
    Integrable (fun x : Domain d => G (Fin.cons ε x) • φ (Fin.cons ε x)) ∧
    (∫ z : Domain (d+1) in {z | ε < z 0}, G z • (-(testPartialCLM [0] φ) z)) =
      (∫ x : Domain d, G (Fin.cons ε x) • φ (Fin.cons ε x)) +
        ∫ z : Domain (d+1) in {z | ε < z 0}, partialFunction (𝕜 := ℝ) [0] G z • φ z := by
  have h := integral_halfspace_time_ibp φ (fun z => (G z : 𝕜))
    (fun z => (partialFunction (𝕜 := ℝ) [0] G z : 𝕜)) ε ?_ ?_ ?_
  · simpa only [← RCLike.real_smul_eq_coe_mul] using h
  · intro x t ht
    have hz : 0 < (Fin.cons t x : Domain (d+1)) 0 := by
      simpa only [Fin.cons_zero] using lt_of_lt_of_le hε ht
    have hd : DifferentiableAt ℝ G (Fin.cons t x) :=
      ((hG (Fin.cons t x) hz).contDiffAt
        ((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hz)).differentiableAt (by simp)
    have hreal : HasDerivAt (fun s => G (Fin.cons s x))
        (partialFunction (𝕜 := ℝ) [0] G (Fin.cons t x)) t :=
      hd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_cons_time x t)
    exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t hreal
  · exact integrableOn_positive_coefficient_test hε
      ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_continuousOn
        (contDiffOn_partialFunction hG [0]).continuousOn) φ
  · exact integrableOn_positive_coefficient_test hε
      ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).continuous.comp_continuousOn hG.continuousOn)
      (testPartialCLM [0] φ)

end ExpandedFA.PartIV.HeatFundamental


/-! The classical Gaussian heat equation. -/

open Set Filter
open scoped BigOperators Topology ContDiff
namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

abbrev positiveGaussian (d : ℕ) (z : Domain (d+1)) : ℝ := gaussianSlice d (z 0) (Fin.tail z)

theorem positiveGaussian_contDiffAt (d : ℕ) (z : Domain (d+1)) (hz : 0 < z 0) :
    ContDiffAt ℝ ∞ (positiveGaussian d) z := by
  unfold positiveGaussian gaussianSlice spatialSquare Fin.tail
  apply ContDiffAt.mul
  · apply ContDiffAt.rpow_const_of_ne
    · fun_prop
    · positivity
  · apply ContDiffAt.exp
    apply ContDiffAt.div
    · fun_prop
    · fun_prop
    · positivity

private def sqDeriv {d : ℕ} (z : Domain (d+1)) : Domain (d+1) →L[ℝ] ℝ :=
  ∑ i : Fin d, (2 * z i.succ) • ContinuousLinearMap.proj i.succ

private theorem hasFDerivAt_square {d : ℕ} (z : Domain (d+1)) :
    HasFDerivAt (fun y : Domain (d+1) => spatialSquare (Fin.tail y)) (sqDeriv z) z := by
  unfold spatialSquare Fin.tail sqDeriv
  apply HasFDerivAt.fun_sum
  intro i hi
  convert (hasFDerivAt_apply (𝕜 := ℝ) i.succ z).pow 2 using 1 <;> simp

private theorem hasFDerivAt_gaussian {d : ℕ} (z : Domain (d+1)) (hz : 0 < z 0) :
    ∃ L : Domain (d+1) →L[ℝ] ℝ, HasFDerivAt (positiveGaussian d) L z ∧
      ∀ v, L v = positiveGaussian d z *
        ((-(d:ℝ)/2) / z 0 * v 0 -
          ((sqDeriv z) v * (4*z 0) - spatialSquare (Fin.tail z) * (4*v 0)) /
            (4*z 0)^2) := by
  have hp := ((hasFDerivAt_apply (𝕜 := ℝ) 0 z).const_mul (4*Real.pi)).rpow_const
    (p := -(d:ℝ)/2) (Or.inl (by positivity : 4*Real.pi*z 0 ≠ 0))
  have hi := (hasDerivAt_inv (by positivity : 4*z 0 ≠ 0)).comp_hasFDerivAt z
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 z).const_mul 4)
  have he := ((hasFDerivAt_square z).neg.mul hi).exp
  refine ⟨_, hp.mul he, ?_⟩
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Function.comp_apply, Pi.mul_apply, Pi.neg_apply, ContinuousLinearMap.neg_apply]
  unfold positiveGaussian gaussianSlice
  have hA : 0 < 4*Real.pi*z 0 := by positivity
  rw [Real.rpow_sub hA, Real.rpow_one]
  simp only [← div_eq_mul_inv]
  field_simp
  <;> ring

theorem positiveGaussian_contDiffOn (d : ℕ) :
    ContDiffOn ℝ ∞ (positiveGaussian d) {z | 0 < z 0} := by
  intro z hz
  exact (positiveGaussian_contDiffAt d z hz).contDiffWithinAt

theorem positiveGaussian_time_deriv {d : ℕ} (z : Domain (d+1)) (hz : 0 < z 0) :
    fderiv ℝ (positiveGaussian d) z (coordinateVector 0) =
      positiveGaussian d z * (-(d:ℝ)/(2*z 0) + spatialSquare (Fin.tail z)/(4*(z 0)^2)) := by
  obtain ⟨L, hL, hval⟩ := hasFDerivAt_gaussian z hz
  rw [hL.fderiv, hval]
  simp only [sqDeriv, coordinateVector, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same, Pi.single_eq_of_ne (Fin.succ_ne_zero _), smul_eq_mul,
    mul_zero, Finset.sum_const_zero, zero_mul, zero_sub, mul_one]
  congr 1
  field_simp
  <;> ring

theorem positiveGaussian_space_deriv {d : ℕ} (z : Domain (d+1)) (hz : 0 < z 0)
    (i : Fin d) :
    fderiv ℝ (positiveGaussian d) z (coordinateVector i.succ) =
      positiveGaussian d z * (-z i.succ/(2*z 0)) := by
  obtain ⟨L, hL, hval⟩ := hasFDerivAt_gaussian z hz
  rw [hL.fderiv, hval]
  have hs : sqDeriv z (coordinateVector i.succ) = 2*z i.succ := by
    simp [sqDeriv, coordinateVector, Pi.single_apply, Fin.succ_inj]
  rw [hs]
  simp only [coordinateVector, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
    mul_zero, sub_zero, zero_sub]
  congr 1
  field_simp
  <;> ring

theorem positiveGaussian_space_second_deriv {d : ℕ} (z : Domain (d+1))
    (hz : 0 < z 0) (i : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (positiveGaussian d) y (coordinateVector i.succ))
      z (coordinateVector i.succ) =
      positiveGaussian d z * ((z i.succ)^2/(4*(z 0)^2) - 1/(2*z 0)) := by
  have heq : (fun y => fderiv ℝ (positiveGaussian d) y (coordinateVector i.succ)) =ᶠ[𝓝 z]
      (fun y => positiveGaussian d y * (-y i.succ/(2*y 0))) := by
    filter_upwards [((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hz)] with y hy
    exact positiveGaussian_space_deriv y hy i
  rw [heq.fderiv_eq]
  have hi := (hasDerivAt_inv (by positivity : 2*z 0 ≠ 0)).comp_hasFDerivAt z
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 z).const_mul 2)
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) i.succ z).neg.mul hi
  have hG := (positiveGaussian_contDiffAt d z hz).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hD := hG.hasFDerivAt.mul hc
  change HasFDerivAt (fun y => positiveGaussian d y * (-y i.succ/(2*y 0))) _ z at hD
  rw [hD.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Function.comp_apply,
    Pi.mul_apply, Pi.neg_apply, ContinuousLinearMap.neg_apply, coordinateVector,
    Pi.single_eq_same, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
    mul_zero, zero_mul, neg_zero, zero_add, add_zero]
  rw [show (fderiv ℝ (positiveGaussian d) z) (Pi.single i.succ 1) =
    positiveGaussian d z * (-z i.succ/(2*z 0)) from positiveGaussian_space_deriv z hz i]
  simp only [← div_eq_mul_inv]
  field_simp
  <;> ring

theorem positiveGaussian_heat_equation {d : ℕ} (z : Domain (d+1)) (hz : 0 < z 0) :
    fderiv ℝ (positiveGaussian d) z (coordinateVector 0) =
      ∑ i : Fin d, fderiv ℝ
        (fun y => fderiv ℝ (positiveGaussian d) y (coordinateVector i.succ))
        z (coordinateVector i.succ) := by
  rw [positiveGaussian_time_deriv z hz]
  simp_rw [positiveGaussian_space_second_deriv z hz]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul, spatialSquare, Fin.tail]
  ring

theorem positiveGaussian_heat_partial {d : ℕ} (z : Domain (d+1)) (hz : 0 < z 0) :
    partialFunction [0] (positiveGaussian d) z =
      ∑ i : Fin d, partialFunction [i.succ, i.succ] (positiveGaussian d) z := by
  exact positiveGaussian_heat_equation z hz

end ExpandedFA.PartIV.HeatFundamental


namespace ExpandedFA.PartIV.HeatFundamental
open ExpandedFA.Distributions

/-- Green's identity for any smooth solution of the classical heat equation,
with a test function of compact support and a positive lower time boundary. -/
theorem truncated_identity_of_classical_heat {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {G : Domain (d+1) → ℝ}
    (hG : ContDiffOn ℝ ∞ G {z | 0 < z 0})
    (hPDE : ∀ z : Domain (d+1), 0 < z 0 →
      partialFunction (𝕜 := ℝ) [0] G z =
        ∑ i : Fin d, partialFunction (𝕜 := ℝ) [i.succ, i.succ] G z)
    (φ : SpaceTimeTests 𝕜 d) (ε : ℝ) (hε : 0 < ε) :
    (∫ z : Domain (d+1) in {z | ε < z 0}, G z •
      (-(testPartialCLM [0] φ) z -
        ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z)) =
      ∫ x : Domain d, G (Fin.cons ε x) • φ (Fin.cons ε x) := by
  have htime := (integral_halfspace_time_ibp_real φ G ε hε hG).2
  have hi0 : IntegrableOn (fun z => G z • (-(testPartialCLM [0] φ) z))
      {z | ε < z 0} := by
    simpa using integrableOn_positive_smul_test hε hG.continuousOn (-testPartialCLM [0] φ)
  have hleft (i : Fin d) : IntegrableOn
      (fun z => G z • (testPartialCLM [i.succ, i.succ] φ) z) {z | ε < z 0} :=
    integrableOn_positive_smul_test hε hG.continuousOn (testPartialCLM [i.succ, i.succ] φ)
  have hright (i : Fin d) : IntegrableOn
      (fun z => partialFunction (𝕜 := ℝ) [i.succ, i.succ] G z • φ z) {z | ε < z 0} :=
    integrableOn_positive_smul_test hε
      (contDiffOn_partialFunction hG [i.succ, i.succ]).continuousOn φ
  have hsumleft : IntegrableOn
      (fun z => ∑ i : Fin d, G z • (testPartialCLM [i.succ, i.succ] φ) z)
      {z | ε < z 0} := integrable_finsetSum _ (fun i _ => hleft i)
  simp_rw [smul_sub, Finset.smul_sum]
  rw [integral_sub hi0 hsumleft, htime, integral_finsetSum _ (fun i _ => hleft i)]
  simp_rw [halfspace_spatial_transfer hG φ hε]
  rw [← integral_finsetSum _ (fun i _ => hright i)]
  have hcancel : (∫ z : Domain (d+1) in {z | ε < z 0},
      partialFunction (𝕜 := ℝ) [0] G z • φ z) =
      ∫ z : Domain (d+1) in {z | ε < z 0},
        ∑ i : Fin d, partialFunction (𝕜 := ℝ) [i.succ, i.succ] G z • φ z := by
    apply setIntegral_congr_fun (isOpen_lt continuous_const (continuous_apply 0)).measurableSet
    intro z hz
    dsimp only
    rw [hPDE z (lt_trans hε hz), Finset.sum_smul]
  rw [hcancel]
  exact add_sub_cancel_right _ _

/-- The displayed Gaussian satisfies the truncated heat Green identity. -/
theorem truncated_heat_identity : Specs.ExpandedFA.PartIV.HeatFundamental.truncatedIdentityType := by
  intro 𝕜 _ d φ ε hε
  have h := truncated_identity_of_classical_heat (positiveGaussian_contDiffOn d)
    (fun z hz => positiveGaussian_heat_partial z hz) φ ε hε
  calc
    _ = ∫ z : Domain (d+1) in {z | ε < z 0}, positiveGaussian d z •
        (-(testPartialCLM [0] φ) z -
          ∑ i : Fin d, (testPartialCLM [i.succ, i.succ] φ) z) := by
      apply setIntegral_congr_fun (isOpen_lt continuous_const (continuous_apply 0)).measurableSet
      intro z hz
      simp only [heatKernel, if_pos (lt_trans hε hz), positiveGaussian,
        RCLike.real_smul_eq_coe_mul]
    _ = _ := h
    _ = _ := by simp only [positiveGaussian, Fin.cons_zero, Fin.tail_cons]

end ExpandedFA.PartIV.HeatFundamental


namespace ExpandedFA.PartIV.HeatFundamental

/-- The full weak heat identity, retaining the point source at the initial time. -/
theorem weak_identity : Specs.ExpandedFA.PartIV.HeatFundamental.weakIdentityType := by
  intro 𝕜 _ d φ
  apply tendsto_nhds_unique (truncated_weak_pairing_limit d φ)
  apply (initial_boundary_limit d φ).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (truncated_heat_identity 𝕜 d φ ε hε).symm

/-- The causal Gaussian is a fundamental solution of ∂ₜ−Δₓ. Proper convolution
solves the equation for every compactly supported distribution datum and retains
its lower time support bound. Both scalar fields and dimension zero are included. -/
theorem fundamental_solution :
    Specs.ExpandedFA.PartIV.HeatFundamental.fundamentalSolutionType :=
  fundamental_solution_of_weak_identity weak_identity

end ExpandedFA.PartIV.HeatFundamental
