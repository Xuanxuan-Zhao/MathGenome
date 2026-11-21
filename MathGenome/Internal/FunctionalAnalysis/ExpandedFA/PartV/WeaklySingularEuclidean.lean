import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeaklySingularEuclidean
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.SchurLp
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartV.WeaklySingularEuclidean

lemma cutoffProfile_continuous (δ : ℝ) : Continuous (cutoffProfile δ) := by
  unfold cutoffProfile
  fun_prop

lemma cutoffProfile_nonneg (δ t : ℝ) : 0 ≤ cutoffProfile δ t := le_max_left _ _

lemma cutoffProfile_le_one (δ t : ℝ) : cutoffProfile δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cutoffProfile_eq_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    cutoffProfile δ t = 0 := by
  unfold cutoffProfile
  apply max_eq_left
  apply (min_le_right _ _).trans
  exact sub_nonpos.mpr ((div_le_one hδ).mpr ht)

lemma cutoffProfile_eq_one {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    cutoffProfile δ t = 1 := by
  unfold cutoffProfile
  rw [min_eq_left, max_eq_right zero_le_one]
  have : 2 ≤ t / δ := (le_div_iff₀ hδ).mpr ht
  linarith

lemma cutoffKernel_eq_zero {X 𝕜 : Type*} [PseudoMetricSpace X] [RCLike 𝕜]
    (k : X × X → 𝕜) {δ : ℝ} (hδ : 0 < δ) {z : X × X}
    (hz : dist z.1 z.2 ≤ δ) : cutoffKernel δ k z = 0 := by
  simp [cutoffKernel, cutoffProfile_eq_zero hδ hz]

lemma cutoffKernel_eq_self {X 𝕜 : Type*} [PseudoMetricSpace X] [RCLike 𝕜]
    (k : X × X → 𝕜) {δ : ℝ} (hδ : 0 < δ) {z : X × X}
    (hz : 2 * δ ≤ dist z.1 z.2) : cutoffKernel δ k z = k z := by
  simp [cutoffKernel, cutoffProfile_eq_one hδ hz]

theorem cutoff_continuous : Spec.CutoffContinuity := by
  intro X 𝕜 _ _ k hk δ hδ
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z.1 = z.2
  · have hn : ∀ᶠ w : X × X in 𝓝 z, dist w.1 w.2 < δ := by
      apply (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).mem_nhds
      simpa [hz] using hδ
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hn] with w hw
    exact cutoffKernel_eq_zero k hδ hw.le
  · have ho : IsOpen {z : X × X | z.1 ≠ z.2} := isOpen_ne_fun continuous_fst continuous_snd
    exact ((cutoffProfile_continuous δ).comp
      (continuous_fst.dist continuous_snd)).continuousAt.smul
        (hk.continuousAt (ho.mem_nhds hz))

/-- The norm of the discarded strip is bounded by the original kernel norm. -/
lemma cutoffKernel_error_le {X 𝕜 : Type*} [PseudoMetricSpace X] [RCLike 𝕜]
    (δ : ℝ) (k : X × X → 𝕜) (z : X × X) :
    ‖k z - cutoffKernel δ k z‖ ≤ ‖k z‖ := by
  have he : k z - cutoffKernel δ k z =
      (1 - cutoffProfile δ (dist z.1 z.2)) • k z := by
    simp only [cutoffKernel, sub_smul, one_smul]
  rw [he, norm_smul]
  have hc0 := cutoffProfile_nonneg δ (dist z.1 z.2)
  have hc1 := cutoffProfile_le_one δ (dist z.1 z.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc1)]
  nlinarith [norm_nonneg (k z)]


section FiniteDomains
variable {X 𝕜 : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Finite X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
/-- On a finite discrete domain every Lp class has a continuous representative.
This proves finite dimension without presuming that Lp representatives are
pointwise linear or choosing point evaluations on a quotient. -/
lemma finiteDimensional_lp_of_finite (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FiniteDimensional 𝕜 (Lp 𝕜 p μ) := by
  letI : FiniteDimensional 𝕜 C(X, 𝕜) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap 𝕜)
      DFunLike.coe_injective
  apply FiniteDimensional.of_surjective (ContinuousMap.toLp (E := 𝕜) p μ 𝕜).toLinearMap
  intro f
  refine ⟨⟨f, continuous_of_discreteTopology⟩, ?_⟩
  apply Lp.ext
  exact ContinuousMap.coeFn_toLp (p := p) (𝕜 := 𝕜) μ _

omit [BorelSpace X] [Finite X] [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
/-- A bounded continuous kernel has finite Schur bounds on a finite measure
space. No lower bound on the total measure is required. -/
lemma continuous_kernel_bounds (k : C(X × X, 𝕜)) :
    SchurLp.KernelBounds μ μ k
      (measureUnivNNReal μ * ‖k‖₊) (measureUnivNNReal μ * ‖k‖₊) := by
  constructor
  · apply ae_of_all
    intro x
    calc
      ∫⁻ y, ‖k (x,y)‖ₑ ∂μ ≤ ∫⁻ _ : X, (‖k‖₊ : ℝ≥0∞) ∂μ := by
        apply lintegral_mono
        intro y
        exact ENNReal.coe_le_coe.mpr (show ‖k (x,y)‖₊ ≤ ‖k‖₊ from
          k.norm_coe_le_norm (x,y))
      _ = _ := by simp [measureUnivNNReal, mul_comm]
  · apply ae_of_all
    intro y
    calc
      ∫⁻ x, ‖k (x,y)‖ₑ ∂μ ≤ ∫⁻ _ : X, (‖k‖₊ : ℝ≥0∞) ∂μ := by
        apply lintegral_mono
        intro x
        exact ENNReal.coe_le_coe.mpr (show ‖k (x,y)‖₊ ≤ ‖k‖₊ from
          k.norm_coe_le_norm (x,y))
      _ = _ := by simp [measureUnivNNReal, mul_comm]

/-- All kernels on a finite metric domain give compact integral maps on C
and on every Lp, including both endpoints. -/
theorem finite_domain_compact_integral_maps (k : X × X → 𝕜) :
    CompactIntegralMaps μ k := by
  let kc : C(X × X, 𝕜) := ⟨k, continuous_of_discreteTopology⟩
  constructor
  · refine ⟨ContinuousKernel.kernelOperator μ kc,
      ContinuousKernel.kernelOperator_isCompact μ kc, ?_⟩
    intro f x
    exact ⟨ContinuousKernel.kernel_integrable_section μ kc f x,
      ContinuousKernel.kernelOperator_apply μ kc f x⟩
  · intro p hp
    haveI := finiteDimensional_lp_of_finite (𝕜 := 𝕜) μ p
    letI : ProperSpace (Lp 𝕜 p μ) := FiniteDimensional.proper_rclike 𝕜 _
    obtain ⟨F⟩ := SchurLp.schur_boundedness μ μ k kc.continuous.measurable
      _ _ (continuous_kernel_bounds μ kc)
    refine ⟨F.op p, isCompactOperator_of_locallyCompactSpace_dom (F.op p), ?_⟩
    intro f
    exact ⟨F.integral_exists p f, F.represents p f⟩
end FiniteDomains

/-- Compactness makes the transported Lebesgue measure finite even when G
has empty interior, and does not require a chosen parametrization. -/
lemma domainMeasure_finite {d : ℕ} (G : Set (Euclidean d)) (hG : IsCompact G) :
    IsFiniteMeasure (domainMeasure G) := by
  letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
  letI : IsFiniteMeasureOnCompacts (domainMeasure G) :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hG.measurableSet)
  infer_instance

theorem zero_dimensional_compactness : Spec.ZeroDimensionalCompactness := by
  intro 𝕜 _ _ _ G hG k
  letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
  letI := domainMeasure_finite G hG
  exact finite_domain_compact_integral_maps (domainMeasure G) k


lemma zeroDiagonal_measurable {X 𝕜 : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (k : X × X → 𝕜)
    (hk : ContinuousOn k {z | z.1 ≠ z.2}) : Measurable (zeroDiagonal k) := by
  classical
  have hdiag : MeasurableSet {z : X × X | z.1 = z.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  have h := (continuousOn_const : ContinuousOn (fun _ : X × X => (0 : 𝕜))
    {z | z.1 = z.2}).measurable_piecewise hk hdiag
  have he : zeroDiagonal k = {z : X × X | z.1 = z.2}.piecewise
      (fun _ => (0 : 𝕜)) k := by
    funext z
    simp [zeroDiagonal, Set.piecewise]
  rw [he]
  exact h

lemma domainMeasure_null_singletons {d : ℕ} (hd : 0 < d)
    (G : Set (Euclidean d)) (hG : IsCompact G) :
    NullSingletonClass (domainMeasure G) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  refine ⟨fun x => ?_⟩
  rw [domainMeasure, comap_subtype_coe_apply hG.measurableSet]
  simp

/-- Diagonal removal is a sectionwise a.e. identity; it therefore preserves
integrals against every input, even before imposing any Lp hypothesis. -/
lemma zeroDiagonal_section_ae {X 𝕜 : Type*} [MeasurableSpace X] [Zero 𝕜]
    (μ : Measure X) [NullSingletonClass μ] (k : X × X → 𝕜) (x : X) :
    (fun y => k (x,y)) =ᵐ[μ] fun y => zeroDiagonal k (x,y) := by
  filter_upwards [μ.ae_ne x] with y hy
  simp [zeroDiagonal, Ne.symm hy]

lemma zeroDiagonal_column_ae {X 𝕜 : Type*} [MeasurableSpace X] [Zero 𝕜]
    (μ : Measure X) [NullSingletonClass μ] (k : X × X → 𝕜) (y : X) :
    (fun x => k (x,y)) =ᵐ[μ] fun x => zeroDiagonal k (x,y) := by
  filter_upwards [μ.ae_ne y] with x hx
  simp [zeroDiagonal, hx]

lemma zeroDiagonal_integral_eq {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [NullSingletonClass μ] (k : X × X → 𝕜) (f : X → 𝕜) (x : X) :
    (∫ y, k (x,y) * f y ∂μ) = ∫ y, zeroDiagonal k (x,y) * f y ∂μ := by
  apply integral_congr_ae
  filter_upwards [zeroDiagonal_section_ae μ k x] with y hy
  rw [hy]

theorem diagonal_removal : Spec.DiagonalRemoval := by
  intro d hd 𝕜 _ _ _ G hG k hk
  haveI := domainMeasure_null_singletons hd G hG
  exact ⟨zeroDiagonal_measurable k hk, zeroDiagonal_section_ae _ k,
    zeroDiagonal_column_ae _ k⟩


/-- Sectionwise a.e. equality preserves both versions of the actual integral
map, without assuming a globally measurable original kernel. -/
lemma compactIntegralMaps_of_section_ae {X 𝕜 : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) {k l : X × X → 𝕜}
    (hkl : ∀ x, (fun y => k (x,y)) =ᵐ[μ] fun y => l (x,y))
    (hk : CompactIntegralMaps μ k) : CompactIntegralMaps μ l := by
  have he (f : X → 𝕜) (x : X) :
      (fun y => k (x,y) * f y) =ᵐ[μ] fun y => l (x,y) * f y := by
    filter_upwards [hkl x] with y hy
    rw [hy]
  obtain ⟨⟨T, hT, hrep⟩, hp⟩ := hk
  constructor
  · refine ⟨T, hT, ?_⟩
    intro f x
    exact ⟨(hrep f x).1.congr (he f x),
      (hrep f x).2.trans (integral_congr_ae (he f x))⟩
  · intro p hp'
    obtain ⟨S, hS, hSr⟩ := hp p
    refine ⟨S, hS, ?_⟩
    intro f
    constructor
    · filter_upwards [(hSr f).1] with x hx
      exact hx.congr (he f x)
    · exact (hSr f).2.trans (Eventually.of_forall fun x => integral_congr_ae (he f x))

lemma compactIntegralMaps_zeroDiagonal_iff {X 𝕜 : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [NullSingletonClass μ] (k : X × X → 𝕜) :
    CompactIntegralMaps μ (zeroDiagonal k) ↔ CompactIntegralMaps μ k := by
  constructor
  · exact compactIntegralMaps_of_section_ae μ
      (fun x => (zeroDiagonal_section_ae μ k x).symm)
  · exact compactIntegralMaps_of_section_ae μ (zeroDiagonal_section_ae μ k)


/-- The radial power in the original hypothesis is locally integrable in
positive dimension, for every positive α (including α ≥ d). -/
lemma radial_power_locallyIntegrable {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α) :
    LocallyIntegrable (fun x : Euclidean d => ‖x‖ ^ (α - d)) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (Euclidean d) := by
    simpa only [Euclidean, finrank_euclideanSpace_fin] using (Nat.succ_le_of_lt hd)
  have hexp : (d : ℝ) - α < Module.finrank ℝ (Euclidean d) := by
    simp only [Euclidean, finrank_euclideanSpace_fin]
    linarith
  apply locallyIntegrable_of_norm_le_rpow hdim hexp (C := 1)
  · apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), one_mul]
    have he : -((d : ℝ) - α) = α - d := by ring
    rw [he]
  · exact (measurable_norm.pow_const (α - d)).aestronglyMeasurable

/-- A constant bounded remainder preserves local integrability. -/
lemma radial_majorant_locallyIntegrable {d : ℕ} (hd : 0 < d)
    {α : ℝ} (hα : 0 < α) (C M : ℝ) :
    LocallyIntegrable (fun x : Euclidean d => C * ‖x‖ ^ (α - d) + M) volume := by
  exact ((radial_power_locallyIntegrable hd hα).smul C).add (locallyIntegrable_const M)


theorem radial_majorant_local_integrability : Spec.RadialMajorantLocalIntegrability := by
  intro d hd α hα C M
  exact radial_majorant_locallyIntegrable hd hα C M

/-- The common radial majorant, regarded as a nonnegative measurable function. -/
noncomputable def radialMajorant (d : ℕ) (α : ℝ) (C M : ℝ≥0)
    (z : Euclidean d) : ℝ≥0∞ :=
  ENNReal.ofReal ((C : ℝ) * ‖z‖ ^ (α - d) + M)

lemma radialMajorant_measurable (d : ℕ) (α : ℝ) (C M : ℝ≥0) :
    Measurable (radialMajorant d α C M) := by
  unfold radialMajorant
  fun_prop

/-- Finite radial mass on every bounded ball, without requiring α < d. -/
lemma radialMajorant_ball_ne_top {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α)
    (C M : ℝ≥0) (r : ℝ) :
    (∫⁻ z in Metric.ball (0 : Euclidean d) r, radialMajorant d α C M z) ≠ ∞ := by
  have hi := (radial_majorant_locallyIntegrable hd hα C M).integrableOn_isCompact
    (isCompact_closedBall (0 : Euclidean d) r)
  have hib := hi.mono_set Metric.ball_subset_closedBall
  exact (lintegral_ofReal_ne_top_iff_integrable hib.aestronglyMeasurable
    (Eventually.of_forall fun z => add_nonneg
      (mul_nonneg C.coe_nonneg (Real.rpow_nonneg (norm_nonneg z) _)) M.coe_nonneg)).mpr hib

/-- Shrinking balls have vanishing radial mass.  The argument uses domination
on a fixed compact ball, so it also covers bounded kernels and α ≥ d. -/
lemma radialMajorant_mass_tendsto_zero {d : ℕ} (hd : 0 < d) {α : ℝ} (hα : 0 < α)
    (C M : ℝ≥0) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (hR : ∀ n, r n ≤ 1) :
    Tendsto (fun n => ∫⁻ z in Metric.ball (0 : Euclidean d) (r n),
      radialMajorant d α C M z) atTop (𝓝 0) := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let F (n : ℕ) := (Metric.ball (0 : Euclidean d) (r n)).indicator
    (radialMajorant d α C M)
  let B := (Metric.ball (0 : Euclidean d) 1).indicator (radialMajorant d α C M)
  have hb : (∫⁻ z, B z) ≠ ∞ := by
    rw [show B = _ from rfl, lintegral_indicator measurableSet_ball]
    exact radialMajorant_ball_ne_top hd hα C M 1
  have hlim : ∀ᵐ z : Euclidean d ∂volume,
      Tendsto (fun n => F n z) atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [volume.ae_ne (0 : Euclidean d)] with z hz
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have he : ∀ᶠ n in atTop, F n z = 0 := by
      filter_upwards [hr.eventually (gt_mem_nhds hn)] with n hn'
      apply Set.indicator_of_notMem
      simpa only [Metric.mem_ball, dist_zero_right] using not_lt.mpr hn'.le
    exact tendsto_const_nhds.congr' (EventuallyEq.symm he)
  have ht := tendsto_lintegral_of_dominated_convergence B
    (fun n => (radialMajorant_measurable d α C M).indicator measurableSet_ball)
    (fun n => Eventually.of_forall fun z =>
      Set.indicator_le_indicator_of_subset (Metric.ball_subset_ball (hR n))
        (fun _ => zero_le) z) hb hlim
  simpa only [F, lintegral_indicator measurableSet_ball, lintegral_zero] using ht

/-- Uniform ambient translation bound for a kernel section on any measurable
subset.  No regularity or positive volume of that subset is needed. -/
lemma section_lintegral_le_radial {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (G : Set (Euclidean d)) (hG : MeasurableSet G) (k : G × G → 𝕜)
    (α : ℝ) (C M : ℝ≥0) (r : ℝ)
    (hb : ∀ x y : G, ‖k (x,y)‖ₑ ≤
      (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
        ((x : Euclidean d) - y)) (x : G) :
    ∫⁻ y, ‖k (x,y)‖ₑ ∂domainMeasure G ≤
      ∫⁻ z in Metric.ball (0 : Euclidean d) r, radialMajorant d α C M z := by
  calc
    _ ≤ ∫⁻ y : G,
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) ∂domainMeasure G := lintegral_mono (hb x)
    _ = ∫⁻ y in G,
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) := by
      simpa only [domainMeasure] using (lintegral_subtype_comap (μ := volume) hG
        (fun z => (Metric.ball (0 : Euclidean d) r).indicator
          (radialMajorant d α C M) ((x : Euclidean d) - z)))
    _ ≤ ∫⁻ y : Euclidean d,
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_sub_left_eq_self, lintegral_indicator measurableSet_ball]

lemma column_lintegral_le_radial {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (G : Set (Euclidean d)) (hG : MeasurableSet G) (k : G × G → 𝕜)
    (α : ℝ) (C M : ℝ≥0) (r : ℝ)
    (hb : ∀ x y : G, ‖k (x,y)‖ₑ ≤
      (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
        ((x : Euclidean d) - y)) (y : G) :
    ∫⁻ x, ‖k (x,y)‖ₑ ∂domainMeasure G ≤
      ∫⁻ z in Metric.ball (0 : Euclidean d) r, radialMajorant d α C M z := by
  calc
    _ ≤ ∫⁻ x : G,
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) ∂domainMeasure G := lintegral_mono (fun x => hb x y)
    _ = ∫⁻ x in G,
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) := by
      simpa only [domainMeasure] using (lintegral_subtype_comap (μ := volume) hG
        (fun z => (Metric.ball (0 : Euclidean d) r).indicator
          (radialMajorant d α C M) (z - (y : Euclidean d))))
    _ ≤ ∫⁻ x : Euclidean d,
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      rw [lintegral_sub_right_eq_self, lintegral_indicator measurableSet_ball]

lemma zeroDiagonal_continuousOn {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (k : X × X → 𝕜) (hk : ContinuousOn k {z | z.1 ≠ z.2}) :
    ContinuousOn (zeroDiagonal k) {z | z.1 ≠ z.2} := by
  apply hk.congr
  intro z hz
  simp only [zeroDiagonal, if_neg hz]

lemma zeroDiagonal_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Euclidean d)} {k : G × G → 𝕜} {α : ℝ} {C M : ℝ≥0}
    (hk : Admissible G k α C M) (x y : G) :
    ‖zeroDiagonal k (x,y)‖ₑ ≤ radialMajorant d α C M ((x : Euclidean d) - y) := by
  by_cases hxy : x = y
  · simp [zeroDiagonal, hxy]
  · rw [zeroDiagonal, if_neg hxy, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [radialMajorant, Subtype.dist_eq, dist_eq_norm] using hk.2 x y hxy

lemma cutoff_error_radial_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Euclidean d)} {k : G × G → 𝕜} {α : ℝ} {C M : ℝ≥0}
    (hk : Admissible G k α C M) {δ : ℝ} (hδ : 0 < δ) (x y : G) :
    ‖zeroDiagonal k (x,y) - cutoffKernel δ (zeroDiagonal k) (x,y)‖ₑ ≤
      (Metric.ball (0 : Euclidean d) (2 * δ)).indicator (radialMajorant d α C M)
        ((x : Euclidean d) - y) := by
  classical
  by_cases hxy : dist x y < 2 * δ
  · rw [Set.indicator_of_mem]
    · exact (enorm_le_iff_norm_le.mpr (cutoffKernel_error_le δ (zeroDiagonal k) (x,y))).trans
        (zeroDiagonal_bound hk x y)
    · simpa only [Metric.mem_ball, dist_zero_right, Subtype.dist_eq, dist_eq_norm, sub_zero] using hxy
  · rw [cutoffKernel_eq_self _ hδ (le_of_not_gt hxy), sub_self, enorm_zero]
    exact zero_le

/-- All sections of the normalized kernel have a single finite bound. -/
lemma zeroDiagonal_uniform_bounds {d : ℕ} (hd : 0 < d) {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Euclidean d)} (hG : IsCompact G) {k : G × G → 𝕜}
    {α : ℝ} (hα : 0 < α) {C M : ℝ≥0} (hk : Admissible G k α C M) :
    ∃ A : ℝ≥0, (∀ x, ∫⁻ y, ‖zeroDiagonal k (x,y)‖ₑ ∂domainMeasure G ≤ A) ∧
      (∀ y, ∫⁻ x, ‖zeroDiagonal k (x,y)‖ₑ ∂domainMeasure G ≤ A) := by
  classical
  obtain ⟨R, hR⟩ := hG.isBounded.exists_norm_le
  let r := 2 * |R| + 1
  have hb (x y : G) :
      ‖zeroDiagonal k (x,y)‖ₑ ≤
        (Metric.ball (0 : Euclidean d) r).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) := by
    rw [Set.indicator_of_mem]
    · exact zeroDiagonal_bound hk x y
    · rw [Metric.mem_ball, dist_zero_right]
      have hn := norm_sub_le (x : Euclidean d) (y : Euclidean d)
      have hx := (hR x x.property).trans (le_abs_self R)
      have hy := (hR y y.property).trans (le_abs_self R)
      dsimp [r]
      linarith
  have hf := radialMajorant_ball_ne_top hd hα C M r
  refine ⟨(∫⁻ z in Metric.ball (0 : Euclidean d) r,
    radialMajorant d α C M z).toNNReal, ?_, ?_⟩
  · intro x
    rw [ENNReal.coe_toNNReal hf]
    exact section_lintegral_le_radial G hG.measurableSet _ α C M r hb x
  · intro y
    rw [ENNReal.coe_toNNReal hf]
    exact column_lintegral_le_radial G hG.measurableSet _ α C M r hb y

/-- The normalized weakly singular kernel admits uniformly small continuous
cutoff errors in both Schur norms, including every individual row. -/
theorem uniform_cutoff_approximation : Spec.UniformCutoffApproximation := by
  intro d hd 𝕜 _ _ _ G hG k α C M hα hk
  refine ⟨zeroDiagonal_measurable k hk.1, zeroDiagonal_uniform_bounds hd hG hα hk, ?_⟩
  let δ (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) / 2
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  let h (n : ℕ) : C(G × G, 𝕜) :=
    ⟨cutoffKernel (δ n) (zeroDiagonal k),
      cutoff_continuous _ (zeroDiagonal_continuousOn _ hk.1) _ (hδ n)⟩
  let e (n : ℕ) : ℝ≥0 := (∫⁻ z in Metric.ball (0 : Euclidean d) (2 * δ n),
    radialMajorant d α C M z).toNNReal
  have hδlim : Tendsto (fun n => 2 * δ n) atTop (𝓝 0) := by
    simpa only [δ, mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδle (n : ℕ) : 2 * δ n ≤ 1 := by
    dsimp [δ]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hi : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  refine ⟨h, e, ?_, ?_⟩
  · exact (ENNReal.tendsto_toNNReal (by simp)).comp
      (radialMajorant_mass_tendsto_zero hd hα C M hδlim hδle)
  · intro n
    have he : (e n : ℝ≥0∞) = ∫⁻ z in Metric.ball (0 : Euclidean d) (2 * δ n),
        radialMajorant d α C M z :=
      ENNReal.coe_toNNReal (radialMajorant_ball_ne_top hd hα C M _)
    rw [he]
    have hb : ∀ x y : G, ‖(fun z => zeroDiagonal k z - h n z) (x,y)‖ₑ ≤
        (Metric.ball (0 : Euclidean d) (2 * δ n)).indicator (radialMajorant d α C M)
          ((x : Euclidean d) - y) := cutoff_error_radial_bound hk (hδ n)
    exact ⟨section_lintegral_le_radial G hG.measurableSet
        (fun z => zeroDiagonal k z - h n z) α C M (2 * δ n) hb,
      column_lintegral_le_radial G hG.measurableSet
        (fun z => zeroDiagonal k z - h n z) α C M (2 * δ n) hb⟩

section ContinuousApproximation
variable {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure X) [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
lemma row_integrable_mul (k : X × X → 𝕜) (hk : Measurable k) (A : ℝ≥0)
    (hrow : ∀ x, ∫⁻ y, ‖k (x,y)‖ₑ ∂μ ≤ A) (f : C(X, 𝕜)) (x : X) :
    Integrable (fun y => k (x,y) * f y) μ := by
  have hi : Integrable (fun y => k (x,y)) μ := by
    refine ⟨(hk.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    exact hasFiniteIntegral_iff_enorm.mpr ((hrow x).trans_lt ENNReal.coe_lt_top)
  exact hi.mul_bdd f.continuous.aestronglyMeasurable
    (Eventually.of_forall f.norm_coe_le_norm)

omit [IsFiniteMeasure μ] in
lemma row_integral_norm_le (k : X × X → 𝕜) (hk : Measurable k) (A : ℝ≥0)
    (hrow : ∀ x, ∫⁻ y, ‖k (x,y)‖ₑ ∂μ ≤ A) (f : C(X, 𝕜)) (x : X) :
    ‖∫ y, k (x,y) * f y ∂μ‖ ≤ (A : ℝ) * ‖f‖ := by
  have hi : Integrable (fun y => k (x,y)) μ := by
    refine ⟨(hk.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    exact hasFiniteIntegral_iff_enorm.mpr ((hrow x).trans_lt ENNReal.coe_lt_top)
  have hr : ∫ y, ‖k (x,y)‖ ∂μ ≤ (A : ℝ) := by
    rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
    exact ENNReal.toReal_mono ENNReal.coe_ne_top (hrow x)
  calc
    ‖∫ y, k (x,y) * f y ∂μ‖ ≤ ∫ y, ‖k (x,y) * f y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖k (x,y)‖ * ‖f‖ ∂μ := by
      apply integral_mono (row_integrable_mul μ k hk A hrow f x).norm
        (hi.norm.mul_const ‖f‖)
      intro y
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _)
    _ = (∫ y, ‖k (x,y)‖ ∂μ) * ‖f‖ := integral_mul_const _ _
    _ ≤ (A : ℝ) * ‖f‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)

lemma compact_continuous_map_of_uniform_kernel_approximation
    (k : X × X → 𝕜) (hk : Measurable k) (ha : UniformKernelApproximation μ k) :
    ∃ T : C(X, 𝕜) →L[𝕜] C(X, 𝕜), IsCompactOperator T ∧
      ∀ f x, Integrable (fun y => k (x,y) * f y) μ ∧
        T f x = ∫ y, k (x,y) * f y ∂μ := by
  obtain ⟨⟨A, hrow, hcol⟩, h, e, he, herr⟩ := ha
  have he' : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast (NNReal.continuous_coe.tendsto 0).comp he
  have hi := row_integrable_mul μ k hk A hrow
  have hidiff (n : ℕ) : Measurable (fun z => k z - h n z) := hk.sub (h n).continuous.measurable
  have hdiff (n : ℕ) (f : C(X, 𝕜)) (x : X) :
      ‖(∫ y, k (x,y) * f y ∂μ) - ContinuousKernel.kernelOperator μ (h n) f x‖ ≤
        (e n : ℝ) * ‖f‖ := by
    rw [ContinuousKernel.kernelOperator_apply]
    change ‖(∫ y, k (x,y) * f y ∂μ) - ∫ y, h n (x,y) * f y ∂μ‖ ≤ _
    rw [← integral_sub (hi f x) (ContinuousKernel.kernel_integrable_section μ (h n) f x)]
    simp_rw [← sub_mul]
    exact row_integral_norm_le μ _ (hidiff n) (e n) (herr n).1 f x
  have hc (f : C(X, 𝕜)) : Continuous (fun x => ∫ y, k (x,y) * f y ∂μ) := by
    have hu : TendstoUniformly
        (fun n x => ContinuousKernel.kernelOperator μ (h n) f x)
        (fun x => ∫ y, k (x,y) * f y ∂μ) atTop := by
      apply Metric.tendstoUniformly_iff.mpr
      intro ε hε
      have hlim : Tendsto (fun n => (e n : ℝ) * ‖f‖) atTop (𝓝 0) := by
        simpa using he'.mul_const ‖f‖
      filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn x
      rw [dist_eq_norm]
      exact (hdiff n f x).trans_lt hn
    exact hu.continuous (Eventually.of_forall (fun n =>
      (ContinuousKernel.kernelOperator μ (h n) f).continuous)).frequently
  let L : C(X, 𝕜) →ₗ[𝕜] C(X, 𝕜) :=
    { toFun := fun f => ⟨fun x => ∫ y, k (x,y) * f y ∂μ, hc f⟩
      map_add' := by
        intro f g
        ext x
        change (∫ y, k (x,y) * (f y + g y) ∂μ) = _
        simp_rw [mul_add]
        exact integral_add (hi f x) (hi g x)
      map_smul' := by
        intro c f
        ext x
        change (∫ y, k (x,y) * (c * f y) ∂μ) = c * ∫ y, k (x,y) * f y ∂μ
        simp_rw [← mul_assoc, mul_comm (k _) c, mul_assoc]
        exact integral_const_mul _ _ }
  let T : C(X, 𝕜) →L[𝕜] C(X, 𝕜) := L.mkContinuous (A : ℝ) (by
    intro f
    apply (ContinuousMap.norm_le (L f) (mul_nonneg A.coe_nonneg (norm_nonneg f))).mpr
    intro x
    exact row_integral_norm_le μ k hk A hrow f x)
  have ht (n : ℕ) : ‖T - ContinuousKernel.kernelOperator μ (h n)‖ ≤ (e n : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (e n).coe_nonneg
    intro f
    apply (ContinuousMap.norm_le _ (mul_nonneg (e n).coe_nonneg (norm_nonneg f))).mpr
    intro x
    exact hdiff n f x
  have hT : Tendsto (fun n => ContinuousKernel.kernelOperator μ (h n)) atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun n => ?_) he'
    simpa only [norm_sub_rev] using ht n
  refine ⟨T, isCompactOperator_of_tendsto hT (Eventually.of_forall fun n =>
    ContinuousKernel.kernelOperator_isCompact μ (h n)), ?_⟩
  intro f x
  exact ⟨hi f x, rfl⟩

end ContinuousApproximation

section ContinuousLp
variable {X 𝕜 : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure X) [IsFiniteMeasure μ]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

lemma lp_integral_norm_le (f : Lp 𝕜 p μ) :
    ∫ x, ‖f x‖ ∂μ ≤ ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * ‖f‖ := by
  have hp : 0 ≤ 1 - 1 / p.toReal := by
    by_cases hpt : p = ∞
    · simp [hpt]
    · have hpr : 1 ≤ p.toReal := by
        simpa using (ENNReal.toReal_mono hpt (Fact.out : 1 ≤ p))
      exact sub_nonneg.mpr (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hpr)
  have hc := ENNReal.rpow_ne_top_of_nonneg hp (measure_ne_top μ Set.univ)
  have hf := Lp.memLp f
  have h1 := memLp_one_iff_integrable.mp (hf.mono_exponent (Fact.out : 1 ≤ p))
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p) hf.aestronglyMeasurable
  have hb' := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.ne (by simpa using hc)) hb
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable] at hb'
  simpa only [ENNReal.toReal_one, div_one, ENNReal.toReal_mul, Lp.norm_def, mul_comm] using hb'

variable (k : C(X × X, 𝕜))

lemma lp_kernel_section_integrable (f : Lp 𝕜 p μ) :
    Integrable (fun y => f y • ContinuousKernel.kernelSection k y) μ := by
  have hf := memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p))
  apply Integrable.mono' (hf.norm.mul_const ‖k‖)
    ((Lp.aestronglyMeasurable f).smul (ContinuousKernel.kernelSection k).continuous.aestronglyMeasurable)
  apply ae_of_all
  intro y
  change ‖f y • ContinuousKernel.kernelSection k y‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (by
    apply ((ContinuousKernel.kernelSection k y).norm_le (norm_nonneg k)).mpr
    intro x
    exact k.norm_coe_le_norm (x,y)) (norm_nonneg _)

noncomputable def lpKernelImage (f : Lp 𝕜 p μ) : C(X, 𝕜) :=
  ∫ y, f y • ContinuousKernel.kernelSection k y ∂μ

lemma lpKernelImage_apply (f : Lp 𝕜 p μ) (x : X) :
    lpKernelImage μ p k f x = ∫ y, k (x,y) * f y ∂μ := by
  rw [lpKernelImage, ContinuousMap.integral_apply (lp_kernel_section_integrable μ p k f)]
  simp [ContinuousKernel.kernelSection, ContinuousKernel.Spec.kernelSection, mul_comm]

lemma lp_kernel_integrable (f : Lp 𝕜 p μ) (x : X) :
    Integrable (fun y => k (x,y) * f y) μ := by
  have h := (ContinuousMap.evalCLM 𝕜 x).integrable_comp (lp_kernel_section_integrable μ p k f)
  simpa [ContinuousKernel.kernelSection, ContinuousKernel.Spec.kernelSection, mul_comm] using h

lemma lpKernelImage_norm_le (f : Lp 𝕜 p μ) :
    ‖lpKernelImage μ p k f‖ ≤
      (‖k‖ * ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal) * ‖f‖ := by
  apply ((lpKernelImage μ p k f).norm_le (by positivity)).mpr
  intro x
  rw [lpKernelImage_apply]
  calc
    ‖∫ y, k (x,y) * f y ∂μ‖ ≤ ∫ y, ‖k‖ * ‖f y‖ ∂μ := by
      apply norm_integral_le_of_norm_le
        ((memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p))).norm.const_mul ‖k‖)
      apply ae_of_all
      intro y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (k.norm_coe_le_norm (x,y)) (norm_nonneg _)
    _ = ‖k‖ * ∫ y, ‖f y‖ ∂μ := integral_const_mul _ _
    _ ≤ ‖k‖ * (((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lp_integral_norm_le μ p f) (norm_nonneg _)
    _ = _ := by ring

noncomputable def lpKernelLinear : Lp 𝕜 p μ →ₗ[𝕜] C(X, 𝕜) where
  toFun := lpKernelImage μ p k
  map_add' f g := by
    ext x
    simp only [lpKernelImage_apply, ContinuousMap.add_apply]
    have hfg : (fun y => k (x,y) * (f + g) y) =ᵐ[μ] (fun y => k (x,y) * f y + k (x,y) * g y) :=
      (Lp.coeFn_add f g).mono (fun y hy => by simp only [hy, Pi.add_apply, mul_add])
    rw [integral_congr_ae hfg]
    exact integral_add (lp_kernel_integrable μ p k f x) (lp_kernel_integrable μ p k g x)
  map_smul' c f := by
    ext x
    simp only [lpKernelImage_apply, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hcf : (fun y => k (x,y) * (c • f) y) =ᵐ[μ] (fun y => c * (k (x,y) * f y)) :=
      (Lp.coeFn_smul c f).mono (fun y hy => by
        simp only [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm (k (x,y)) c])
    rw [integral_congr_ae hcf]
    exact integral_const_mul _ _

noncomputable def lpKernelToContinuous : Lp 𝕜 p μ →L[𝕜] C(X, 𝕜) :=
  (lpKernelLinear μ p k).mkContinuous
    (‖k‖ * ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal)
    (lpKernelImage_norm_le μ p k)

lemma lpKernelToContinuous_apply (f : Lp 𝕜 p μ) (x : X) :
    lpKernelToContinuous μ p k f x = ∫ y, k (x,y) * f y ∂μ := lpKernelImage_apply μ p k f x

lemma lpKernelToContinuous_dist_le (f : Lp 𝕜 p μ) (x x' : X) :
    dist (lpKernelToContinuous μ p k f x) (lpKernelToContinuous μ p k f x') ≤
      ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * ‖f‖ * dist (k.curry x) (k.curry x') := by
  rw [dist_eq_norm, lpKernelToContinuous_apply, lpKernelToContinuous_apply]
  rw [← integral_sub (lp_kernel_integrable μ p k f x) (lp_kernel_integrable μ p k f x')]
  calc
    ‖∫ y, k (x,y) * f y - k (x',y) * f y ∂μ‖ ≤
        ∫ y, ‖k.curry x - k.curry x'‖ * ‖f y‖ ∂μ := by
      apply norm_integral_le_of_norm_le
        ((memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (Fact.out : 1 ≤ p))).norm.const_mul _)
      apply ae_of_all
      intro y
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ((k.curry x - k.curry x').norm_coe_le_norm y) (norm_nonneg _)
    _ = ‖k.curry x - k.curry x'‖ * ∫ y, ‖f y‖ ∂μ := integral_const_mul _ _
    _ ≤ ‖k.curry x - k.curry x'‖ * (((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * ‖f‖) :=
      mul_le_mul_of_nonneg_left (lp_integral_norm_le μ p f) (norm_nonneg _)
    _ = _ := by rw [dist_eq_norm]; ring

lemma lpKernelToContinuous_unitBall_equicontinuous :
    Equicontinuous (fun f : lpKernelToContinuous μ p k '' Metric.closedBall 0 1 =>
      ((f : C(X, 𝕜)) : X → 𝕜)) := by
  intro x₀
  apply Metric.equicontinuousAt_of_continuity_modulus
    (fun x => ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * dist (k.curry x₀) (k.curry x))
  · have h : Continuous (fun x => ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * dist (k.curry x₀) (k.curry x)) :=
      continuous_const.mul (continuous_const.dist k.curry.continuous)
    simpa using (h.continuousAt (x := x₀)).tendsto
  · filter_upwards with x f
    obtain ⟨u, hu, huf⟩ := f.property
    have hu' : ‖u‖ ≤ 1 := by simpa using hu
    change dist ((f : C(X, 𝕜)) x₀) ((f : C(X, 𝕜)) x) ≤ _
    rw [← huf]
    exact (lpKernelToContinuous_dist_le μ p k u x₀ x).trans (by
      calc
        _ ≤ ((μ Set.univ) ^ (1 - 1 / p.toReal)).toReal * 1 * dist (k.curry x₀) (k.curry x) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hu' ENNReal.toReal_nonneg) dist_nonneg
        _ = _ := by rw [mul_one])

lemma lpKernelToContinuous_isCompact : IsCompactOperator (lpKernelToContinuous μ p k) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall _ zero_lt_one).mpr
  apply (ExpandedFA.PartV.Ascoli.arzela_ascoli 𝕜 X
    (lpKernelToContinuous μ p k '' Metric.closedBall 0 1)).mpr
  refine ⟨?_, lpKernelToContinuous_unitBall_equicontinuous μ p k⟩
  refine ⟨‖lpKernelToContinuous μ p k‖, norm_nonneg _, ?_⟩
  rintro f ⟨u, hu, rfl⟩ x
  have hu' : ‖u‖ ≤ 1 := by simpa using hu
  exact ((lpKernelToContinuous μ p k u).norm_coe_le_norm x).trans
    (((lpKernelToContinuous μ p k).le_opNorm u).trans (by
      simpa using mul_le_mul_of_nonneg_left hu' (norm_nonneg (lpKernelToContinuous μ p k))))

lemma continuous_kernel_lp_compact : IsCompactOperator
    (SchurLp.kernelLpOperator μ μ k k.continuous.measurable _ _ (continuous_kernel_bounds μ k) p) := by
  have he : SchurLp.kernelLpOperator μ μ k k.continuous.measurable _ _ (continuous_kernel_bounds μ k) p =
      (ContinuousMap.toLp (E := 𝕜) p μ 𝕜).comp (lpKernelToContinuous μ p k) := by
    ext f
    refine (SchurLp.kernelLpLinear_coe μ μ k k.continuous.measurable _ _ (continuous_kernel_bounds μ k) p f).trans ?_
    exact ((ContinuousMap.coeFn_toLp (p := p) (𝕜 := 𝕜) μ (lpKernelToContinuous μ p k f)).trans
      (ae_of_all μ (lpKernelToContinuous_apply μ p k f))).symm
  rw [he]
  exact (lpKernelToContinuous_isCompact μ p k).clm_comp (ContinuousMap.toLp (E := 𝕜) p μ 𝕜)

end ContinuousLp

lemma schurConstant_diag (A : ℝ≥0) (p : ℝ≥0∞) : SchurLp.schurConstant A A p = A := by
  unfold SchurLp.schurConstant
  rw [← Real.rpow_add' A.coe_nonneg (by ring_nf; norm_num), sub_add_cancel, Real.rpow_one]

section KernelDifference
variable {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) [SigmaFinite μ]
  (k l : X × X → 𝕜) (hk : Measurable k) (hl : Measurable l)
  (A B C D E F : ℝ≥0)
  (h : SchurLp.KernelBounds μ μ k A B)
  (h' : SchurLp.KernelBounds μ μ l C D)
  (hd : SchurLp.KernelBounds μ μ (k-l) E F)
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
lemma kernelLpOperator_sub :
    SchurLp.kernelLpOperator μ μ k hk A B h p -
      SchurLp.kernelLpOperator μ μ l hl C D h' p =
    SchurLp.kernelLpOperator μ μ (k-l) (hk.sub hl) E F hd p := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub
    (SchurLp.kernelLpOperator μ μ k hk A B h p f)
    (SchurLp.kernelLpOperator μ μ l hl C D h' p f),
    SchurLp.kernelLpLinear_coe μ μ k hk A B h p f,
    SchurLp.kernelLpLinear_coe μ μ l hl C D h' p f,
    SchurLp.kernelLpLinear_coe μ μ (k-l) (hk.sub hl) E F hd p f,
    (SchurLp.kernel_estimate μ μ k hk A B h p Fact.out (Lp.memLp f)).1,
    (SchurLp.kernel_estimate μ μ l hl C D h' p Fact.out (Lp.memLp f)).1]
    with x hx hkx hlx hdx hik hil
  change ((SchurLp.kernelLpOperator μ μ k hk A B h p f -
    SchurLp.kernelLpOperator μ μ l hl C D h' p f : Lp 𝕜 p μ) : X → 𝕜) x = _
  rw [hx]
  change (SchurLp.kernelLpLinear μ μ k hk A B h p f : X → 𝕜) x -
    (SchurLp.kernelLpLinear μ μ l hl C D h' p f : X → 𝕜) x =
    (SchurLp.kernelLpLinear μ μ (k-l) (hk.sub hl) E F hd p f : X → 𝕜) x
  rw [hkx, hlx, hdx]
  simp only [SchurLp.kernelValue, Pi.sub_apply]
  simp_rw [sub_mul]
  exact (integral_sub hik hil).symm
end KernelDifference

section Approximation
variable {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ]

lemma kernel_lp_compact_of_approximation
    (hcompact : ∀ (l : C(X × X, 𝕜)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
      IsCompactOperator (SchurLp.kernelLpOperator μ μ l l.continuous.measurable
        _ _ (continuous_kernel_bounds μ l) p))
    (k : X × X → 𝕜) (hk : Measurable k) (ha : UniformKernelApproximation μ k) :
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      ∃ T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ, IsCompactOperator T ∧
        ∀ f : Lp 𝕜 p μ,
          (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) μ) ∧
          (T f : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * f y ∂μ := by
  obtain ⟨⟨A, hAr, hAc⟩, l, e, he, hb⟩ := ha
  have hA : SchurLp.KernelBounds μ μ k A A :=
    ⟨ae_of_all μ hAr, ae_of_all μ hAc⟩
  have hdiff (n : ℕ) : SchurLp.KernelBounds μ μ (k - (l n : X × X → 𝕜)) (e n) (e n) :=
    ⟨ae_of_all μ (hb n).1, ae_of_all μ (hb n).2⟩
  intro p hp
  let T := SchurLp.kernelLpOperator μ μ k hk A A hA p
  let Tn (n : ℕ) := SchurLp.kernelLpOperator μ μ (l n) (l n).continuous.measurable
    _ _ (continuous_kernel_bounds μ (l n)) p
  have hn (n : ℕ) : ‖T - Tn n‖ ≤ (e n : ℝ) := by
    dsimp only [T, Tn]
    rw [kernelLpOperator_sub μ k (l n) hk (l n).continuous.measurable
      A A _ _ (e n) (e n) hA (continuous_kernel_bounds μ (l n)) (hdiff n) p]
    simpa only [schurConstant_diag] using SchurLp.kernelLpOperator_norm_le μ μ
      (k - (l n : X × X → 𝕜)) (hk.sub (l n).continuous.measurable) (e n) (e n) (hdiff n) p
  have he' : Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) := by
    exact NNReal.tendsto_coe.mpr he
  have ht : Tendsto Tn atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      rw [norm_sub_rev]
      exact hn n) he'
  refine ⟨T, isCompactOperator_of_tendsto ht (Eventually.of_forall fun n => hcompact (l n) p), ?_⟩
  intro f
  exact ⟨(SchurLp.kernel_estimate μ μ k hk A A hA p Fact.out (Lp.memLp f)).1,
    SchurLp.kernelLpLinear_coe μ μ k hk A A hA p f⟩
end Approximation

/-- Uniform row and column L¹ approximation by continuous kernels gives both
compact integral maps, including the endpoint spaces L¹ and L∞. -/
lemma compactIntegralMaps_of_uniformKernelApproximation
    {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ]
    (k : X × X → 𝕜) (hk : Measurable k)
    (ha : UniformKernelApproximation μ k) : CompactIntegralMaps μ k := by
  exact ⟨compact_continuous_map_of_uniform_kernel_approximation μ k hk ha,
    kernel_lp_compact_of_approximation μ
      (fun l p _ => continuous_kernel_lp_compact μ p l) k hk ha⟩

/-- The full Euclidean assertion for the source's original kernel. Diagonal
normalization is removed sectionwise, so no extra measurability is imposed
on the arbitrary diagonal values. -/
theorem euclidean_compactness : Spec.EuclideanCompactness := by
  intro d 𝕜 _ _ _ G hG k α C M hα hk
  by_cases hd : d = 0
  · subst d
    exact zero_dimensional_compactness 𝕜 G hG k
  · letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
    haveI := domainMeasure_finite G hG
    haveI := domainMeasure_null_singletons (Nat.pos_of_ne_zero hd) G hG
    obtain ⟨hm, ha⟩ := uniform_cutoff_approximation d (Nat.pos_of_ne_zero hd)
      𝕜 G hG k α C M hα hk
    exact (compactIntegralMaps_zeroDiagonal_iff (domainMeasure G) k).mp
      (compactIntegralMaps_of_uniformKernelApproximation (domainMeasure G)
        (zeroDiagonal k) hm ha)

end ExpandedFA.PartV.WeaklySingularEuclidean
