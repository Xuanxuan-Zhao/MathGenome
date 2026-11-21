import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.LinfinityDualBoundary
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.D11.Ch05.AtomicIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch01.ElementaryMeasuresLimits
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction
namespace D11.Ch20.LinfinityDualBoundary
open Specs.D11.Ch20.LinfinityDualBoundary (unitSequence)

variable {𝕜 : Type} [RCLike 𝕜]

/-- Every bounded scalar sequence has a limit along every ultrafilter. -/
theorem exists_ultralimit (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜) :
    ∃ z, Tendsto a (U : Filter ℕ) (𝓝 z) := by
  obtain ⟨z, _, hz⟩ := (isCompact_closedBall (0 : 𝕜) ‖a‖).ultrafilter_le_nhds'
    (U.map a) (by
      change {n | a n ∈ Metric.closedBall (0 : 𝕜) ‖a‖} ∈ (U : Filter ℕ)
      exact Filter.Eventually.of_forall (fun n => by simpa using a.norm_coe_le_norm n))
  exact ⟨z, hz⟩

def ultralimit (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜) : 𝕜 :=
  Filter.limUnder (U : Filter ℕ) a

theorem tendsto_ultralimit (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜) :
    Tendsto a (U : Filter ℕ) (𝓝 (ultralimit U a)) :=
  tendsto_nhds_limUnder (exists_ultralimit U a)

def limitLinear (U : Ultrafilter ℕ) : (ℕ →ᵇ 𝕜) →ₗ[𝕜] 𝕜 where
  toFun := ultralimit U
  map_add' a b := ((tendsto_ultralimit U a).add (tendsto_ultralimit U b)).limUnder_eq
  map_smul' c a := ((tendsto_ultralimit U a).const_smul c).limUnder_eq

theorem norm_ultralimit_le (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜) :
    ‖ultralimit U a‖ ≤ ‖a‖ :=
  le_of_tendsto (tendsto_ultralimit U a).norm
    (Filter.Eventually.of_forall (fun n => a.norm_coe_le_norm n))

def limitFunctional (U : Ultrafilter ℕ) : (ℕ →ᵇ 𝕜) →L[𝕜] 𝕜 :=
  (limitLinear U).mkContinuous 1 (fun a => by
    change ‖ultralimit U a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using norm_ultralimit_le U a)

@[simp] theorem limitFunctional_apply (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜) :
    limitFunctional U a = ultralimit U a := rfl

@[simp] theorem limitFunctional_const (U : Ultrafilter ℕ) (c : 𝕜) :
    limitFunctional U (BoundedContinuousFunction.const ℕ c) = c :=
  tendsto_const_nhds.limUnder_eq

theorem norm_limitFunctional (U : Ultrafilter ℕ) :
    ‖limitFunctional (𝕜 := 𝕜) U‖ = 1 := by
  apply le_antisymm
  · apply (limitFunctional (𝕜 := 𝕜) U).opNorm_le_bound (by exact zero_le_one)
    intro a
    rw [limitFunctional_apply, one_mul]
    exact norm_ultralimit_le U a
  · have h := (limitFunctional (𝕜 := 𝕜) U).le_opNorm
      (BoundedContinuousFunction.const ℕ 1)
    simpa only [limitFunctional_const, BoundedContinuousFunction.norm_const_eq,
      norm_one, mul_one] using h


theorem limitFunctional_unitSequence (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ cofinite) (n : ℕ) :
    limitFunctional U (unitSequence 𝕜 n) = 0 := by
  have heq : (unitSequence 𝕜 n : ℕ → 𝕜) =ᶠ[(U : Filter ℕ)] (fun _ => 0) := by
    filter_upwards [hU (Set.finite_singleton n).compl_mem_cofinite] with j hj
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj
    simp [unitSequence, hj]
  exact (tendsto_const_nhds.congr' heq.symm).limUnder_eq

theorem limitFunctional_re_nonneg (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜)
    (ha : ∀ n, 0 ≤ RCLike.re (a n)) :
    0 ≤ RCLike.re (limitFunctional U a) := by
  exact ge_of_tendsto ((RCLike.continuous_re.tendsto _).comp (tendsto_ultralimit U a))
    (Eventually.of_forall ha)

theorem limitFunctional_im_zero (U : Ultrafilter ℕ) (a : ℕ →ᵇ 𝕜)
    (ha : ∀ n, RCLike.im (a n) = 0) :
    RCLike.im (limitFunctional U a) = 0 := by
  apply tendsto_nhds_unique
    ((RCLike.continuous_im.tendsto _).comp (tendsto_ultralimit U a))
  simpa only [Function.comp_def, ha] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) (U : Filter ℕ) (𝓝 0))

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

theorem sequence_memLp (a : ℕ →ᵇ 𝕜) : MemLp a ∞ (Measure.count : Measure ℕ) :=
  memLp_top_of_bound (measurable_of_countable a).stronglyMeasurable.aestronglyMeasurable
    ‖a‖ (ae_of_all _ (fun n => a.norm_coe_le_norm n))

def sequenceToLp : (ℕ →ᵇ 𝕜) →ₗ[𝕜] Lp 𝕜 ∞ (Measure.count : Measure ℕ) where
  toFun a := (sequence_memLp a).toLp a
  map_add' a b := MemLp.toLp_add (sequence_memLp a) (sequence_memLp b)
  map_smul' c a := MemLp.toLp_const_smul c (sequence_memLp a)

@[simp] theorem sequenceToLp_apply (a : ℕ →ᵇ 𝕜) (n : ℕ) :
    sequenceToLp a n = a n :=
  Measure.ae_count_iff.mp (MemLp.coeFn_toLp (sequence_memLp a)) n

omit [MeasurableSpace 𝕜] [BorelSpace 𝕜] in
theorem counting_coordinate_le (f : Lp 𝕜 ∞ (Measure.count : Measure ℕ)) (n : ℕ) :
    ‖f n‖ ≤ ‖f‖ := by
  rw [Lp.norm_def]
  have h := ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (enorm_le_eLpNorm_count f n ENNReal.top_ne_zero)
  simpa using h

theorem norm_sequenceToLp (a : ℕ →ᵇ 𝕜) : ‖sequenceToLp a‖ = ‖a‖ := by
  apply le_antisymm
  · rw [Lp.norm_def]
    have h := eLpNorm_le_of_ae_bound (p := (∞ : ℝ≥0∞))
      (Lp.aestronglyMeasurable (sequenceToLp a))
      (ae_of_all (Measure.count : Measure ℕ) (fun n => by
        simpa using a.norm_coe_le_norm n))
    simp only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul] at h
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
      (ENNReal.toReal_ofReal (norm_nonneg a))
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro n
    simpa using counting_coordinate_le (sequenceToLp a) n

def countingEquiv : (ℕ →ᵇ 𝕜) ≃ₗᵢ[𝕜] Lp 𝕜 ∞ (Measure.count : Measure ℕ) :=
  LinearIsometryEquiv.ofSurjective
    { sequenceToLp (𝕜 := 𝕜) with norm_map' := norm_sequenceToLp }
    (by
      intro f
      let a : ℕ →ᵇ 𝕜 := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
        f ‖f‖ (counting_coordinate_le f)
      refine ⟨a, ?_⟩
      apply Lp.ext
      exact ae_of_all _ (fun n => sequenceToLp_apply a n))

@[simp] theorem countingEquiv_apply (a : ℕ →ᵇ 𝕜) (n : ℕ) :
    countingEquiv a n = a n := sequenceToLp_apply a n

@[simp] theorem countingEquiv_symm_apply
    (f : Lp 𝕜 ∞ (Measure.count : Measure ℕ)) (n : ℕ) :
    (countingEquiv.symm f) n = f n := by
  have h := countingEquiv_apply (countingEquiv.symm f) n
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

theorem counting_equivalence : Specs.D11.Ch20.LinfinityDualBoundary.counting_equivalence := by
  intro 𝕜 _ _ _
  exact ⟨countingEquiv, sequenceToLp_apply⟩

theorem pairing_integrable (g : ℕ → 𝕜) (hg : Integrable g Measure.count)
    (a : ℕ →ᵇ 𝕜) : Integrable (fun n => a n * g n) Measure.count :=
  hg.bdd_mul (measurable_of_countable a).stronglyMeasurable.aestronglyMeasurable
    (ae_of_all _ (fun n => a.norm_coe_le_norm n))

theorem singleton_pairing (g : ℕ → 𝕜) (hg : Integrable g Measure.count) (n : ℕ) :
    (∫ j, unitSequence 𝕜 n j * g j ∂Measure.count) = g n := by
  rw [integral_countable (pairing_integrable g hg (unitSequence 𝕜 n))]
  simp [unitSequence]

theorem no_density (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite)
    (g : ℕ → 𝕜) (hg : Integrable g Measure.count) :
    ¬ (∀ a : ℕ →ᵇ 𝕜, limitFunctional U a = ∫ n, a n * g n ∂Measure.count) := by
  intro h
  have hz : ∀ n, g n = 0 := by
    intro n
    have hn := h (unitSequence 𝕜 n)
    rw [limitFunctional_unitSequence U hU, singleton_pairing g hg n] at hn
    exact hn.symm
  have hone := h (BoundedContinuousFunction.const ℕ 1)
  simp only [limitFunctional_const, hz, mul_zero, integral_zero] at hone
  exact one_ne_zero hone

theorem ultrafilter_boundary : Specs.D11.Ch20.LinfinityDualBoundary.ultrafilter_boundary := by
  refine ⟨hyperfilter ℕ, hyperfilter_le_cofinite,
    (fun n => (Set.finite_singleton n).notMem_hyperfilter), ?_⟩
  intro 𝕜 _ _ _
  refine ⟨limitFunctional (hyperfilter ℕ), tendsto_ultralimit _, norm_limitFunctional _,
    limitFunctional_const _ _, limitFunctional_unitSequence _ hyperfilter_le_cofinite,
    limitFunctional_re_nonneg _, limitFunctional_im_zero _, ?_⟩
  intro g hg
  exact ⟨pairing_integrable g hg, no_density _ hyperfilter_le_cofinite g hg⟩

theorem counting_dual_boundary :
    Specs.D11.Ch20.LinfinityDualBoundary.counting_dual_boundary := by
  intro 𝕜 _ _ _
  let ell := (limitFunctional (𝕜 := 𝕜) (hyperfilter ℕ)).comp
    ((countingEquiv (𝕜 := 𝕜)).symm :
      Lp 𝕜 ∞ (Measure.count : Measure ℕ) →L[𝕜] (ℕ →ᵇ 𝕜))
  refine ⟨countingEquiv, countingEquiv_apply, ell, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
      (limitFunctional (𝕜 := 𝕜) (hyperfilter ℕ))
      (countingEquiv (𝕜 := 𝕜)).symm).trans (norm_limitFunctional _)
  · change limitFunctional (hyperfilter ℕ)
      (countingEquiv.symm (countingEquiv _)) = 1
    rw [LinearIsometryEquiv.symm_apply_apply, limitFunctional_const]
  · intro n
    change limitFunctional (hyperfilter ℕ)
      (countingEquiv.symm (countingEquiv _)) = 0
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact limitFunctional_unitSequence _ hyperfilter_le_cofinite n
  · intro f hf
    apply limitFunctional_re_nonneg (hyperfilter ℕ) (countingEquiv.symm f)
    simpa only [countingEquiv_symm_apply] using hf
  · intro f hf
    apply limitFunctional_im_zero (hyperfilter ℕ) (countingEquiv.symm f)
    simpa only [countingEquiv_symm_apply] using hf
  · intro g
    have hg := memLp_one_iff_integrable.mp (Lp.memLp g)
    constructor
    · intro f
      simpa only [countingEquiv_symm_apply] using
        pairing_integrable g hg (countingEquiv.symm f)
    · intro h
      apply no_density (hyperfilter ℕ) hyperfilter_le_cofinite g hg
      intro a
      have ha := h (countingEquiv a)
      change limitFunctional (hyperfilter ℕ)
        (countingEquiv.symm (countingEquiv a)) = _ at ha
      simpa only [LinearIsometryEquiv.symm_apply_apply, countingEquiv_apply] using ha

end D11.Ch20.LinfinityDualBoundary
