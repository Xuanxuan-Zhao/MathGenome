import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTraceBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.FractionalSobolev
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.MeanInequalities

noncomputable section
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.Trace ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The independent condition is the actual accepted trace predicate. -/
theorem coordinateTraceCondition_iff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) :
    CoordinateTraceCondition i T ↔ IsCoordinateTrace i T := Iff.rfl

/-- Existence is supplied by the accepted half-space trace, not postulated. -/
theorem coordinate_trace_exists {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃! T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)), CoordinateTraceCondition i T :=
  coordinate_upper_trace_exists i hp

/-- The endpoint exponent lies strictly between zero and one. -/
theorem endpoint_exponent {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    0 < 1 - 1 / p.toReal ∧ 1 - 1 / p.toReal < 1 := by
  have hpr : 1 < p.toReal := by
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  constructor
  · exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hpr)
  · exact sub_lt_self _ (by positivity)

/-- The cancellation in the radial weight retains precisely sp=p-1. -/
theorem endpoint_weight {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    (1 - 1 / p.toReal) * p.toReal = p.toReal - 1 := by
  have hp0 : p.toReal ≠ 0 := ne_of_gt (lt_trans zero_lt_one
    ((ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1))
  field_simp

/-- The reindexed trace really is smooth restriction at height zero. -/
theorem reindexedTrace_smooth {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : CoordinateTraceCondition i T)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict
      (upper i : Set (Domain (n + 1)))] f) :
    reindexedTrace i T u =ᵐ[volume] fun z : Domain n => f (i.insertNth 0 z) := by
  have h := (boundaryCoordinates_measurePreserving i).quasiMeasurePreserving.ae_eq_comp
    (hT u f hf hu)
  have hc := Lp.coeFn_compMeasurePreserving (T u) (boundaryCoordinates_measurePreserving i)
  apply hc.trans
  change (fun z => T u (transverseFinEquiv i z)) =ᵐ[volume]
    (fun z => f (coordinateLine i (transverseFinEquiv i z) 0)) at h
  change (fun z => T u (transverseFinEquiv i z)) =ᵐ[volume]
    (fun z => f (i.insertNth 0 z))
  simpa only [coordinateLine_transverseFinEquiv] using h

/-- Uniform Lp part of the trace bound on the entire graph, by density. -/
theorem reindexedTrace_norm_le {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : CoordinateTraceCondition i T)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) :
    ‖reindexedTrace i T u‖ ≤ 4 * ‖u‖ := by
  have hs : IsClosed {v : SpaceValue 𝕜 (n + 1) (upper i) 1 p |
      ‖reindexedTrace i T v‖ ≤ 4 * ‖v‖} :=
    isClosed_le (reindexedTrace i T).continuous.norm (continuous_const.mul continuous_norm)
  apply hs.closure_subset (a := u)
  apply closure_mono (s := (c1BoundarySubmodule (𝕜 := 𝕜) (upper i) p : Set _)) ?_
    (coordinate_upper_c1_density i hp u)
  rintro v ⟨f, hf, hv⟩
  have hb := (coordinate_upper_c1_trace_bound i hp v f hf hv).2
  have he : eLpNorm (fun y : Transverse i => f (coordinateLine i y 0)) p volume =
      eLpNorm (T v) p volume := eLpNorm_congr_ae (hT v f hf hv).symm
  rw [he, ← Lp.norm_def] at hb
  change ‖boundaryPullback i p (T v)‖ ≤ 4 * ‖v‖
  rw [(boundaryPullback i p).norm_map]
  exact hb

/-- For each fixed translation, the Lp increment is continuous in its input. -/
theorem lpIncrement_continuous_input {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : Domain d) :
    Continuous (fun u : Lp 𝕜 p (volume : Measure (Domain d)) => lpIncrement p h u) := by
  let e := Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : Domain d => x - (-h))
    (measurePreserving_sub_right volume (-h)) (p := p) (E := 𝕜)
  exact e.continuous.sub continuous_id

/-- Fatou on the weighted increment space: an Lp limit preserves a convergent
upper bound on the fractional seminorm, without assuming completeness of the
fractional space or pointwise convergence of scalar representatives. -/
theorem differenceSeminorm_le_of_tendsto {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {v : ℕ → Lp 𝕜 p (volume : Measure (Domain d))}
    {u : Lp 𝕜 p (volume : Measure (Domain d))}
    (hv : Tendsto v atTop (𝓝 u)) {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ j, (differenceEnergy s p (v j)) ^ (1 / p.toReal) ≤ b j) :
    (differenceEnergy s p u) ^ (1 / p.toReal) ≤ B := by
  have hf := Lp.eLpNorm_lim_le_liminf_eLpNorm
    (μ := differenceMeasure (d := d) s p) (p := p)
    (fun j => (lpIncrement_continuous p hp (v j)).stronglyMeasurable.aestronglyMeasurable)
    (fun h => lpIncrement p h u)
    (lpIncrement_continuous p hp u).stronglyMeasurable.aestronglyMeasurable
    (ae_of_all _ fun h => ((lpIncrement_continuous_input p h).tendsto u).comp hv)
  simp_rw [← difference_energy_weightedLp 𝕜 d s p hp] at hf
  exact hf.trans ((Filter.liminf_le_liminf (Eventually.of_forall hbound)).trans_eq hb.liminf_eq)

/-- Once the smooth fractional seminorm estimate is available, density and
Fatou give exactly the same estimate on the original entire Sobolev graph. -/
theorem extend_smooth_seminorm_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (s K : ℝ)
    (hbound : ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p)
      (f : Domain (n + 1) → 𝕜), ContDiff ℝ 1 f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict
        (upper i : Set (Domain (n + 1)))] f →
      (differenceEnergy s p (reindexedTrace i T u)) ^ (1 / p.toReal) ≤
        ENNReal.ofReal (K * ‖u‖))
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) :
    (differenceEnergy s p (reindexedTrace i T u)) ^ (1 / p.toReal) ≤
      ENNReal.ofReal (K * ‖u‖) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp (coordinate_upper_c1_density i hp u)
  apply differenceSeminorm_le_of_tendsto s p hp
    ((reindexedTrace i T).continuous.tendsto u |>.comp hlim)
    ((ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_norm)).tendsto u
      |>.comp hlim)
  intro j
  obtain ⟨f, hf, hvf⟩ := hv j
  exact hbound (v j) f hf hvf

/-- Converting the extended seminorm estimate back to the full real norm
retains finiteness and adds the Lp trace constant four. -/
theorem full_trace_bound_of_seminorm_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : CoordinateTraceCondition i T) (s K : ℝ) (hK : 0 ≤ K)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p)
    (hbound : (differenceEnergy s p (reindexedTrace i T u)) ^ (1 / p.toReal) ≤
      ENNReal.ofReal (K * ‖u‖)) :
    ∃ h : differenceEnergy s p (reindexedTrace i T u) < ∞,
      fractionalNorm s p ⟨reindexedTrace i T u, h⟩ ≤ (4 + K) * ‖u‖ := by
  have hfin : (differenceEnergy s p (reindexedTrace i T u)) ^ (1 / p.toReal) < ∞ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  have hmem := (difference_seminorm_finite_iff 𝕜 n s p hp (reindexedTrace i T u)).mp hfin
  refine ⟨hmem, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (mul_nonneg hK (norm_nonneg _)), ← ENNReal.toReal_rpow] at hreal
  change ‖reindexedTrace i T u‖ +
    (differenceEnergy s p (reindexedTrace i T u)).toReal ^ (1 / p.toReal) ≤ (4 + K) * ‖u‖
  have hLp := reindexedTrace_norm_le i hp T hT u
  nlinarith

/-- The boundary of a one-dimensional half-line is zero dimensional, so
its fractional difference seminorm is zero. This case needs no Hardy estimate. -/
theorem half_line_full_trace_bound {𝕜 : Type} [RCLike 𝕜]
    (i : Fin (0 + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 (0 + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : CoordinateTraceCondition i T) (s : ℝ)
    (u : SpaceValue 𝕜 (0 + 1) (upper i) 1 p) :
    ∃ h : differenceEnergy s p (reindexedTrace i T u) < ∞,
      fractionalNorm s p ⟨reindexedTrace i T u, h⟩ ≤ 4 * ‖u‖ := by
  have hz := difference_zero_dimension 𝕜 s p (reindexedTrace i T u)
  refine ⟨hz.2, ?_⟩
  rw [fractionalNorm_zero_dimension 𝕜 s p hp]
  exact reindexedTrace_norm_le i hp T hT u

/-- All nonsmooth and zero-boundary-dimensional work is discharged here.
The only input is the positive-dimensional estimate for actual C1 restrictions. -/
theorem sharp_trace_bound_of_smooth
    (h : Specs.ExpandedFA.PartIV.SharpTraceBound.SmoothSeminormEstimate) :
    Specs.ExpandedFA.PartIV.SharpTraceBound.BoundedTrace := by
  intro n p _ hp1 hp
  by_cases hn : n = 0
  · subst n
    refine ⟨4, by norm_num, ?_⟩
    intro 𝕜 _ i
    exact ⟨coordinate_trace_exists i hp, fun T hT u =>
      half_line_full_trace_bound i hp T hT (1 - 1 / p.toReal) u⟩
  · obtain ⟨K, hK, hbound⟩ := h n (Nat.pos_of_ne_zero hn) p hp1 hp
    refine ⟨4 + K, by positivity, ?_⟩
    intro 𝕜 _ i
    refine ⟨coordinate_trace_exists i hp, ?_⟩
    intro T hT u
    apply full_trace_bound_of_seminorm_bound i hp T hT (1 - 1 / p.toReal) K hK u
    apply extend_smooth_seminorm_bound i hp T (1 - 1 / p.toReal) K (u := u)
    intro v f hf hv
    exact hbound 𝕜 i v f (reindexedTrace i T v) hf hv
      (reindexedTrace_smooth i T hT v f hf hv)

/-! The real-variable Hardy step is proved with extended integrals, so no
slice integrability or finite-energy hypothesis is built into the estimate.
Weighted Hölder uses β=(p-1)/2; Tonelli then cancels the opposite powers of t.
The resulting constant is finite for every p>1; optimality is unnecessary. -/
namespace AnalyticEstimates

lemma power_lintegral_near {b r : ℝ} (hb : -1 < b) (hr : 0 < r) :
    ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal t ^ b =
      ENNReal.ofReal (1 / (b + 1)) * ENNReal.ofReal r ^ (b + 1) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ b) (Ioo (0 : ℝ) r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr hb
  have he : ∫ t in Ioo (0 : ℝ) r, t ^ b = r ^ (b + 1) / (b + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
      integral_rpow (Or.inl hb), Real.zero_rpow (by linarith : b + 1 ≠ 0), sub_zero]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) r)] fun t : ℝ => t ^ b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  calc
    _ = ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ b) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ENNReal.ofReal_rpow_of_pos ht.1
    _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) r, t ^ b) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnn).symm
    _ = _ := by rw [he, div_eq_mul_one_div, ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
                    ← ENNReal.ofReal_rpow_of_pos hr]; rw [mul_comm]

lemma power_lintegral_far {b t : ℝ} (hb : b < -1) (ht : 0 < t) :
    ∫⁻ r in Ioi t, ENNReal.ofReal r ^ b =
      ENNReal.ofReal (-(1 / (b + 1))) * ENNReal.ofReal t ^ (b + 1) := by
  have hi := integrableOn_Ioi_rpow_of_lt hb ht
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi t)] fun r : ℝ => r ^ b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact Real.rpow_nonneg (ht.trans hr).le _
  calc
    _ = ∫⁻ r in Ioi t, ENNReal.ofReal (r ^ b) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact ENNReal.ofReal_rpow_of_pos (ht.trans hr)
    _ = ENNReal.ofReal (∫ r in Ioi t, r ^ b) :=
      (ofReal_integral_eq_lintegral_ofReal hi hnn).symm
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt hb ht]
      rw [show -(t ^ (b+1)) / (b+1) = (-(1 / (b+1))) * t ^ (b+1) by ring,
        ENNReal.ofReal_mul (by
          have hb1 : b + 1 < 0 := by linarith
          exact neg_nonneg.mpr (one_div_nonpos.mpr hb1.le)), ← ENNReal.ofReal_rpow_of_pos ht]

lemma hardy_pointwise {a : ℝ → ℝ≥0∞} (ha : Measurable a)
    {p r : ℝ} (hp : 1 < p) (hr : 0 < r) :
    (∫⁻ t in Ioo (0 : ℝ) r, a t) ^ p ≤
      (2 : ℝ≥0∞) ^ (p-1) * ENNReal.ofReal r ^ ((p-1)/2) *
        ∫⁻ t in Ioo (0 : ℝ) r, a t ^ p * ENNReal.ofReal t ^ ((p-1)/2) := by
  let q := p / (p-1)
  let β := (p-1)/2
  have hp0 : 0 < p := by linarith
  have hpz : p ≠ 0 := hp0.ne'
  have hpm : p-1 ≠ 0 := by linarith
  have hpq : p.HolderConjugate q := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hp, ?_⟩
    dsimp [q]
    field_simp
    ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Ioo (0 : ℝ) r)) hpq
    ((ha.mul (measurable_id.ennreal_ofReal.pow_const (β/p))).aemeasurable)
    ((measurable_id.ennreal_ofReal.pow_const (-β/p)).aemeasurable)
  simp only [Pi.mul_apply, id_eq] at h
  have hc : (∫⁻ t in Ioo (0 : ℝ) r,
      (a t * ENNReal.ofReal t ^ (β/p)) * ENNReal.ofReal t ^ (-β/p)) =
        ∫⁻ t in Ioo (0 : ℝ) r, a t := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [mul_assoc, ← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr ht.1)) ENNReal.ofReal_ne_top]
    simp [neg_div]
  rw [hc] at h
  have hf : (∫⁻ t in Ioo (0 : ℝ) r, (a t * ENNReal.ofReal t ^ (β/p)) ^ p) =
      ∫⁻ t in Ioo (0 : ℝ) r, a t ^ p * ENNReal.ofReal t ^ β := by
    congr 1
    funext t
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
      div_mul_cancel₀ _ hpz]
  have hg : (∫⁻ t in Ioo (0 : ℝ) r, (ENNReal.ofReal t ^ (-β/p)) ^ q) =
      (2 : ℝ≥0∞) * ENNReal.ofReal r ^ (1/2 : ℝ) := by
    simp_rw [← ENNReal.rpow_mul]
    have he : (-β/p)*q = (-1/2 : ℝ) := by dsimp [β,q]; field_simp
    rw [he, power_lintegral_near (by norm_num : (-1:ℝ) < -1/2) hr]
    norm_num
  rw [hf, hg] at h
  have he : (1/q)*p = p-1 := by dsimp [q]; field_simp
  have h := ENNReal.rpow_le_rpow h hp0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hpz, ENNReal.rpow_one, ← ENNReal.rpow_mul, he,
    ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p-1), ← ENNReal.rpow_mul] at h
  convert h using 1
  dsimp [β]
  ring_nf

lemma lintegral_triangle_swap (F G : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ r in Ioi (0 : ℝ), G r * ∫⁻ t in Ioo (0 : ℝ) r, F t) =
      ∫⁻ t in Ioi (0 : ℝ), F t * ∫⁻ r in Ioi t, G r := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hnear (r : ℝ) : (∫⁻ t in Ioo (0 : ℝ) r, F t) =
      ∫⁻ t, (Iio r).indicator F t ∂μ := by
    change _ = ∫⁻ t, (Iio r).indicator F t ∂volume.restrict (Ioi (0:ℝ))
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have hs : Iio r ∩ Ioi (0:ℝ) = Ioo 0 r := by ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
    rw [hs]
  have hfar (t : ℝ) (ht : 0 < t) :
      (∫⁻ r, (Ioi t).indicator G r ∂μ) = ∫⁻ r in Ioi t, G r := by
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi ht.le)]
  have hm : Measurable (fun z : ℝ × ℝ => G z.1 * (Iio z.1).indicator F z.2) := by
    have he : (fun z : ℝ × ℝ => (Iio z.1).indicator F z.2) =
        {z : ℝ × ℝ | z.2 < z.1}.indicator (fun z => F z.2) := by
      funext z
      simp only [indicator_apply, mem_Iio, mem_ofPred_eq]
    apply Measurable.mul (hG.comp measurable_fst)
    rw [he]
    exact (hF.comp measurable_snd).indicator (measurableSet_lt measurable_snd measurable_fst)
  calc
    _ = ∫⁻ r, ∫⁻ t, G r * (Iio r).indicator F t ∂μ ∂μ := by
      apply lintegral_congr
      intro r
      rw [hnear, lintegral_const_mul _ (hF.indicator measurableSet_Iio)]
    _ = ∫⁻ t, ∫⁻ r, G r * (Iio r).indicator F t ∂μ ∂μ :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ t, F t * ∫⁻ r, (Ioi t).indicator G r ∂μ ∂μ := by
      apply lintegral_congr
      intro t
      rw [← lintegral_const_mul _ (hG.indicator measurableSet_Ioi)]
      apply lintegral_congr
      intro r
      by_cases htr : t < r <;> simp [htr, mul_comm]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hfar t ht]

/-- A finite (not necessarily optimal) Hardy constant. No finiteness assumption
is made on the datum or its p-power integral. -/
lemma hardy_lintegral {a : ℝ → ℝ≥0∞} (ha : Measurable a)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) *
      (∫⁻ t in Ioo (0 : ℝ) r, a t) ^ p) ≤
      ((2 : ℝ≥0∞) ^ (p-1) * ENNReal.ofReal (2/(p-1))) *
        ∫⁻ t in Ioi (0 : ℝ), a t ^ p := by
  let β : ℝ := (p-1)/2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβp : β-p < -1 := by dsimp [β]; linarith
  have hF : Measurable (fun t : ℝ => a t ^ p * ENNReal.ofReal t ^ β) :=
    (ha.pow_const p).mul (measurable_id.ennreal_ofReal.pow_const β)
  have hG : Measurable (fun r : ℝ => ENNReal.ofReal r ^ (β-p)) :=
    measurable_id.ennreal_ofReal.pow_const _
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), (2 : ℝ≥0∞) ^ (p-1) *
        (ENNReal.ofReal r ^ (β-p) *
          ∫⁻ t in Ioo (0 : ℝ) r, a t ^ p * ENNReal.ofReal t ^ β) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      calc
        _ ≤ ENNReal.ofReal r ^ (-p) *
            ((2 : ℝ≥0∞) ^ (p-1) * ENNReal.ofReal r ^ β *
              ∫⁻ t in Ioo (0 : ℝ) r, a t ^ p * ENNReal.ofReal t ^ β) :=
          by gcongr; exact hardy_pointwise ha hp hr
        _ = _ := by
          rw [ENNReal.rpow_sub _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top]
          rw [ENNReal.rpow_neg, div_eq_mul_inv]
          ring
    _ = (2 : ℝ≥0∞) ^ (p-1) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (β-p) *
          ∫⁻ t in Ioo (0 : ℝ) r, a t ^ p * ENNReal.ofReal t ^ β := by
      rw [lintegral_const_mul']
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    _ = (2 : ℝ≥0∞) ^ (p-1) *
        ∫⁻ t in Ioi (0 : ℝ), (a t ^ p * ENNReal.ofReal t ^ β) *
          ∫⁻ r in Ioi t, ENNReal.ofReal r ^ (β-p) := by
      rw [lintegral_triangle_swap _ _ hF hG]
    _ = (2 : ℝ≥0∞) ^ (p-1) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2/(p-1)) * a t ^ p := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [power_lintegral_far hβp ht]
      have he : β-p+1 = -β := by dsimp [β]; ring
      have hc : -(1/(β-p+1)) = 2/(p-1) := by rw [he]; dsimp [β]; field_simp
      rw [hc, he]
      calc
        _ = ENNReal.ofReal (2/(p-1)) * a t ^ p *
            (ENNReal.ofReal t ^ β * ENNReal.ofReal t ^ (-β)) := by ring
        _ = _ := by
          rw [← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr ht)) ENNReal.ofReal_ne_top]
          simp
    _ = _ := by rw [lintegral_const_mul _ (ha.pow_const p)]; ring

lemma lintegral_fun_norm_addHaar {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F ‖x‖ ∂μ) = (Module.finrank ℝ E * μ (Metric.ball 0 1)) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (Module.finrank ℝ E - 1) * F r := by
  calc
    _ = ∫⁻ x : ({(0)}ᶜ : Set E), F ‖x.val‖ ∂μ.comap (↑) := by
      rw [lintegral_subtype_comap (measurableSet_singleton (0:E)).compl (fun x => F ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ x, F x.2.val ∂μ.toSphere.prod (.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using
        μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp
          ((hF.comp measurable_subtype_coe).comp measurable_snd)
    _ = μ.toSphere Set.univ *
        ∫⁻ x : Ioi (0 : ℝ), F x.val ∂.volumeIoiPow (Module.finrank ℝ E - 1) := by
      rw [lintegral_prod (fun x : Metric.sphere (0:E) 1 × Ioi (0:ℝ) => F x.2.val) (by fun_prop)]
      simp only [lintegral_const, mul_comm]
    _ = _ := by
      rw [Measure.toSphere_apply_univ, Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul (f := fun r : Ioi (0:ℝ) => ENNReal.ofReal (r.val ^ (Module.finrank ℝ E - 1)))
          (g := fun r : Ioi (0:ℝ) => F r.val) _
          (by fun_prop) (by fun_prop)]
      simp only [Pi.mul_apply]
      rw [lintegral_subtype_comap measurableSet_Ioi
          (fun r : ℝ => ENNReal.ofReal (r ^ (Module.finrank ℝ E - 1)) * F r)]
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [ENNReal.ofReal_pow hr.le]

lemma measurable_cumulative {a : ℝ → ℝ≥0∞} (ha : Measurable a) :
    Measurable (fun r => ∫⁻ t in Ioo (0 : ℝ) r, a t) := by
  have hm : Measurable (fun z : ℝ × ℝ => (Iio z.1).indicator a z.2) := by
    have he : (fun z : ℝ × ℝ => (Iio z.1).indicator a z.2) =
        {z : ℝ × ℝ | z.2 < z.1}.indicator (fun z => a z.2) := by
      funext z
      simp only [indicator_apply, mem_Iio, mem_ofPred_eq]
    rw [he]
    exact (ha.comp measurable_snd).indicator (measurableSet_lt measurable_snd measurable_fst)
  have he : (fun r => ∫⁻ t in Ioo (0 : ℝ) r, a t) =
      fun r => ∫⁻ t, (Iio r).indicator a t ∂volume.restrict (Ioi (0:ℝ)) := by
    funext r
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have hs : Iio r ∩ Ioi (0:ℝ) = Ioo 0 r := by ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
    rw [hs]
  rw [he]
  exact hm.lintegral_prod_right'

lemma hardy_profile_lintegral {a b : ℝ → ℝ≥0∞} (ha : Measurable a)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) *
      (2 * (∫⁻ t in Ioo (0 : ℝ) r, a t) + ENNReal.ofReal r * b r) ^ p) ≤
      (2 : ℝ≥0∞) ^ (p-1) *
        (2 ^ p * (((2 : ℝ≥0∞) ^ (p-1) * ENNReal.ofReal (2/(p-1))) *
          ∫⁻ t in Ioi (0 : ℝ), a t ^ p) + ∫⁻ t in Ioi (0 : ℝ), b t ^ p) := by
  let A := fun r => ∫⁻ t in Ioo (0 : ℝ) r, a t
  have hA : Measurable A := measurable_cumulative ha
  have hp0 : 0 ≤ p := by linarith
  have hC : (2 : ℝ≥0∞) ^ (p-1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
  have hN : (2 : ℝ≥0∞) ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0 (by norm_num)
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), (2 : ℝ≥0∞) ^ (p-1) *
        (2 ^ p * (ENNReal.ofReal r ^ (-p) * A r ^ p) + b r ^ p) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      calc
        _ ≤ ENNReal.ofReal r ^ (-p) *
            ((2 : ℝ≥0∞) ^ (p-1) * ((2 * A r) ^ p + (ENNReal.ofReal r * b r) ^ p)) := by
          gcongr
          exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp.le
        _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0, ENNReal.mul_rpow_of_nonneg _ _ hp0]
          have hc : ENNReal.ofReal r ^ (-p) * ENNReal.ofReal r ^ p = 1 := by
            rw [← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top]
            simp
          calc
            _ = 2 ^ (p-1) * (2 ^ p * (ENNReal.ofReal r ^ (-p) * A r ^ p) +
                (ENNReal.ofReal r ^ (-p) * ENNReal.ofReal r ^ p) * b r ^ p) := by ring
            _ = _ := by rw [hc, one_mul]
    _ = (2 : ℝ≥0∞) ^ (p-1) *
        (2 ^ p * (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) * A r ^ p) +
          ∫⁻ r in Ioi (0 : ℝ), b r ^ p) := by
      rw [lintegral_const_mul' _ _ hC, lintegral_add_left (f := fun r => (2 : ℝ≥0∞) ^ p * (ENNReal.ofReal r ^ (-p) * A r ^ p)) (by fun_prop) (fun r => b r ^ p), lintegral_const_mul' _ _ hN]
    _ ≤ _ := by gcongr; exact hardy_lintegral ha hp

lemma normal_difference_enorm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : ContDiff ℝ 1 f)
    {r : ℝ} (hr : 0 ≤ r) :
    ‖f r - f 0‖ₑ ≤ ∫⁻ t in Ioo (0 : ℝ) r, ‖deriv f t‖ₑ := by
  have h := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hf.contDiffOn hr
  rw [← restrict_Ioo_eq_restrict_Icc] at h
  exact h

lemma normal_comparison_lintegral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) [SFinite μ] (f g : X × ℝ → E)
    (hf : Measurable f) (hg : Measurable g)
    (hfC1 : ∀ x, ContDiff ℝ 1 (fun t => f (x, t)))
    (hderiv : ∀ x, deriv (fun t => f (x, t)) = fun t => g (x, t))
    {p : ℝ} (hp : 1 < p) (H : ℝ≥0∞)
    (hardy : ∀ (a : ℝ → ℝ≥0∞), Measurable a →
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) *
        (∫⁻ t in Ioo (0 : ℝ) r, a t) ^ p) ≤
      H * ∫⁻ t in Ioi (0 : ℝ), a t ^ p) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) *
      ∫⁻ x, ‖f (x, r) - f (x, 0)‖ₑ ^ p ∂μ) ≤
    H * ∫⁻ r in Ioi (0 : ℝ), ∫⁻ x, ‖g (x, r)‖ₑ ^ p ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hdiff : Measurable (fun z : X × ℝ => ‖f z - f (z.1, 0)‖ₑ ^ p) :=
    (hf.sub (hf.comp (measurable_fst.prodMk measurable_const))).enorm.pow_const p
  have hnormal : Measurable (fun z : X × ℝ => ‖g z‖ₑ ^ p) :=
    hg.enorm.pow_const p
  have hweight : Measurable (fun r : ℝ => ENNReal.ofReal r ^ (-p)) :=
    measurable_id.ennreal_ofReal.pow_const _
  have hweighted : Measurable (fun z : X × ℝ =>
      ENNReal.ofReal z.2 ^ (-p) * ‖f z - f (z.1, 0)‖ₑ ^ p) :=
    (hweight.comp measurable_snd).mul hdiff
  calc
    _ = ∫⁻ r, ∫⁻ x, ENNReal.ofReal r ^ (-p) *
          ‖f (x, r) - f (x, 0)‖ₑ ^ p ∂μ ∂ν := by
      apply lintegral_congr
      intro r
      exact (lintegral_const_mul _ (hdiff.comp measurable_prodMk_right)).symm
    _ = ∫⁻ x, ∫⁻ r, ENNReal.ofReal r ^ (-p) *
          ‖f (x, r) - f (x, 0)‖ₑ ^ p ∂ν ∂μ := by
      exact lintegral_lintegral_swap (hweighted.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ x, H * ∫⁻ r, ‖g (x, r)‖ₑ ^ p ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      apply le_trans _ (hardy (fun t => ‖g (x, t)‖ₑ) (hg.comp measurable_prodMk_left).enorm)
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow _ (by linarith)
      simpa only [hderiv x] using normal_difference_enorm_le (fun t => f (x, t)) (hfC1 x) hr.le
    _ = H * ∫⁻ r, ∫⁻ x, ‖g (x, r)‖ₑ ^ p ∂μ ∂ν := by
      rw [lintegral_const_mul _ hnormal.lintegral_prod_right']
      congr 1
      exact lintegral_lintegral_swap hnormal.aemeasurable

open ExpandedFA.Distributions ExpandedFA.Sobolev.Lines ExpandedFA.Sobolev.Trace

lemma insertNth_contDiff_path {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (i : Fin (n + 1))
    (f : Domain (n + 1) → E) (hf : ContDiff ℝ 1 f) (x : Domain n) :
    ContDiff ℝ 1 (fun t => f (i.insertNth t x)) := by
  have h := hf.comp ((coordinateLine_contDiff i (transverseFinEquiv i x)).of_le (by simp))
  simpa only [Function.comp_def, coordinateLine_transverseFinEquiv] using h

lemma insertNth_deriv_path {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (i : Fin (n + 1))
    (f : Domain (n + 1) → E) (hf : ContDiff ℝ 1 f) (x : Domain n) :
    deriv (fun t => f (i.insertNth t x)) =
      fun t => fderiv ℝ f (i.insertNth t x) (coordinateVector i) := by
  funext t
  have h := ((hf.differentiable_one _).hasFDerivAt.comp_hasDerivAt t
    (coordinateLine_hasDerivAt i (transverseFinEquiv i x) t)).deriv
  simpa only [Function.comp_def, coordinateLine_transverseFinEquiv] using h

lemma normal_insertNth_comparison {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {n : ℕ} (i : Fin (n + 1)) (f : Domain (n + 1) → E) (hf : ContDiff ℝ 1 f)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) *
      ∫⁻ x : Domain n, ‖f (i.insertNth r x) - f (i.insertNth 0 x)‖ₑ ^ p) ≤
    ((2 : ℝ≥0∞) ^ (p - 1) * ENNReal.ofReal (2 / (p - 1))) *
      ∫⁻ r in Ioi (0 : ℝ), ∫⁻ x : Domain n,
        ‖fderiv ℝ f (i.insertNth r x) (coordinateVector i)‖ₑ ^ p := by
  let e : Domain n × ℝ → Domain (n + 1) := fun z => i.insertNth z.2 z.1
  have he : Continuous e := by
    apply continuous_pi
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simpa [e] using (continuous_snd : Continuous (fun z : Domain n × ℝ => z.2))
    · simpa [e, Function.comp_def] using ((continuous_apply k).comp continuous_fst :
        Continuous (fun z : Domain n × ℝ => z.1 k))
  have hd : Continuous (fun y => fderiv ℝ f y (coordinateVector i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact normal_comparison_lintegral volume (f ∘ e)
    ((fun y => fderiv ℝ f y (coordinateVector i)) ∘ e)
    (hf.continuous.measurable.comp he.measurable) (hd.measurable.comp he.measurable)
    (insertNth_contDiff_path i f hf) (insertNth_deriv_path i f hf) hp _
    (fun a ha => hardy_lintegral ha hp)


lemma segment_rpow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (x h : E) {p : ℝ} (hp : 1 ≤ p) :
    ‖f (x+h) - f x‖ₑ ^ p ≤
      ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ f (x+t • h) h‖ₑ ^ p := by
  have hc : ContDiff ℝ 1 (fun t : ℝ => f (x+t • h)) :=
    hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hd (t : ℝ) : deriv (fun t : ℝ => f (x+t • h)) t =
      fderiv ℝ f (x+t • h) h := by
    simpa only [Function.comp_def, Pi.add_apply, zero_add, one_smul, id_eq] using
      ((hf.differentiable_one (x+t • h)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const h))).deriv
  have hFTC := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hc.contDiffOn
    (by norm_num : (0:ℝ) ≤ 1)
  simp only [zero_smul, add_zero, one_smul] at hFTC
  rw [← restrict_Ioc_eq_restrict_Icc] at hFTC
  simp_rw [hd] at hFTC
  refine (ENNReal.rpow_le_rpow hFTC (by linarith)).trans ?_
  apply lintegral_enorm_unit_rpow_le _ _ hp
  exact ((hf.continuous_fderiv (by norm_num)).comp
    (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

lemma segment_operator_rpow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (x h : E) {p : ℝ} (hp : 1 ≤ p) :
    ‖f (x+h) - f x‖ₑ ^ p ≤ ‖h‖ₑ ^ p *
      ∫⁻ t in Ioc (0:ℝ) 1, ‖fderiv ℝ f (x+t • h)‖ₑ ^ p := by
  refine (segment_rpow f hf x h hp).trans ?_
  calc
    _ ≤ ∫⁻ t in Ioc (0:ℝ) 1, (‖fderiv ℝ f (x+t • h)‖ₑ * ‖h‖ₑ) ^ p := by
      apply lintegral_mono
      intro t
      exact ENNReal.rpow_le_rpow ((fderiv ℝ f (x+t • h)).le_opENorm h) (by linarith)
    _ = _ := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p), mul_comm _ (‖h‖ₑ ^ p)]
      rw [lintegral_const_mul']
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by finiteness)

lemma translation_affine_rpow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ}
    (f : E → F) (hf : ContDiff ℝ 1 f) (L : (Fin n → ℝ) →L[ℝ] E)
    (b : E) (h : Fin n → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖f (b+L (x+h)) - f (b+L x)‖ₑ ^ p) ≤
      ‖L h‖ₑ ^ p * ∫⁻ x, ‖fderiv ℝ f (b+L x)‖ₑ ^ p := by
  have hD : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hm : Measurable (fun z : (Fin n → ℝ) × ℝ =>
      ‖fderiv ℝ f (b+L (z.1+z.2 • h))‖ₑ ^ p) := by
    exact ((hD.comp (continuous_const.add (L.continuous.comp
      (continuous_fst.add (continuous_snd.smul continuous_const))))).enorm.measurable).pow_const _
  calc
    _ ≤ ∫⁻ x, ‖L h‖ₑ ^ p * ∫⁻ t in Ioc (0:ℝ) 1,
        ‖fderiv ℝ f (b+L (x+t • h))‖ₑ ^ p := by
      apply lintegral_mono
      intro x
      simpa only [map_add, map_smul, add_assoc] using
        segment_operator_rpow f hf (b+L x) (L h) hp
    _ = ‖L h‖ₑ ^ p * ∫⁻ t in Ioc (0:ℝ) 1, ∫⁻ x,
        ‖fderiv ℝ f (b+L (x+t • h))‖ₑ ^ p := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by finiteness))]
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = _ := by
      congr 1
      have he (t : ℝ) : (∫⁻ x : Fin n → ℝ, ‖fderiv ℝ f (b+L (x+t • h))‖ₑ ^ p) =
          ∫⁻ x : Fin n → ℝ, ‖fderiv ℝ f (b+L x)‖ₑ ^ p := by
        exact (measurePreserving_add_right (volume : Measure (Fin n → ℝ)) (t • h)).lintegral_comp
          (((hD.comp (continuous_const.add L.continuous)).enorm.measurable).pow_const _)
      simp_rw [he]
      simp

def insertZeroCLM {n : ℕ} (i : Fin (n+1)) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun x : Fin n → ℝ => i.insertNth (0 : ℝ) x
      map_add' := by
        intro x y
        ext j
        induction j using i.succAboveCases <;> simp
      map_smul' := by
        intro c x
        ext j
        induction j using i.succAboveCases <;> simp }
    1 (by
      intro x
      simp only [one_mul]
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro j
      induction j using i.succAboveCases
      · simp
      · simpa using norm_le_pi_norm x _)

lemma insert_affine {n : ℕ} (i : Fin (n+1)) (r : ℝ) (x : Fin n → ℝ) :
    i.insertNth r x = i.insertNth r 0 + insertZeroCLM i x := by
  ext j
  induction j using i.succAboveCases <;> simp [insertZeroCLM, LinearMap.mkContinuous_apply]

lemma norm_insertZeroCLM {n : ℕ} (i : Fin (n+1)) (x : Fin n → ℝ) :
    ‖insertZeroCLM i x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  induction j using i.succAboveCases
  · simp [insertZeroCLM, LinearMap.mkContinuous_apply]
  · simpa [insertZeroCLM, LinearMap.mkContinuous_apply] using norm_le_pi_norm x _

lemma tangential_height_rpow {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {n : ℕ} (i : Fin (n+1))
    (f : (Fin (n+1) → ℝ) → F) (hf : ContDiff ℝ 1 f)
    (r : ℝ) (h : Fin n → ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖f (i.insertNth r (x+h)) - f (i.insertNth r x)‖ₑ ^ p) ≤
      ‖h‖ₑ ^ p * ∫⁻ x, ‖fderiv ℝ f (i.insertNth r x)‖ₑ ^ p := by
  have H := translation_affine_rpow f hf (insertZeroCLM i) (i.insertNth r 0) h hp
  have he (x : Fin n → ℝ) : i.insertNth r 0 + insertZeroCLM i x = i.insertNth r x :=
    (insert_affine i r x).symm
  simp_rw [he] at H
  refine H.trans ?_
  gcongr
  simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (norm_insertZeroCLM i h)


lemma lintegral_euclideanLength {n : ℕ} (hn : 0 < n)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h : Fin n → ℝ, F ‖WithLp.toLp 2 h‖) =
      ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (n - 1) * F r := by
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa using hn)
  calc
    _ = ∫⁻ h : EuclideanSpace ℝ (Fin n), F ‖h‖ :=
      (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp (hF.comp measurable_norm)
    _ = _ := by
      rw [lintegral_fun_norm_addHaar volume F hF]
      simp only [finrank_euclideanSpace_fin]

lemma weighted_radial_lintegral {n : ℕ} (hn : 0 < n) (p : ℝ)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h : Fin n → ℝ,
      (if h = 0 then 0 else ENNReal.ofReal ‖WithLp.toLp 2 h‖ ^ (-(n + p - 1))) *
        F ‖WithLp.toLp 2 h‖) =
      ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) * F r := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have h0 : ∀ᵐ h : Fin n → ℝ, h ≠ 0 := by
    simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using (measure_singleton (0 : Fin n → ℝ))
  calc
    _ = ∫⁻ h : Fin n → ℝ,
        ENNReal.ofReal ‖WithLp.toLp 2 h‖ ^ (-(n + p - 1)) * F ‖WithLp.toLp 2 h‖ := by
      apply lintegral_congr_ae
      filter_upwards [h0] with h hh
      rw [ite_eq_right hh]
    _ = ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (n - 1) *
          (ENNReal.ofReal r ^ (-(n + p - 1)) * F r) :=
      lintegral_euclideanLength hn _ ((measurable_id.ennreal_ofReal.pow_const _).mul hF)
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [← ENNReal.rpow_natCast, hncast, ← mul_assoc,
        ← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top]
      congr 2
      ring

lemma radial_factor_lt_top (n : ℕ) :
    (n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) < ∞ := by
  exact ENNReal.mul_lt_top (by simp) measure_ball_lt_top

lemma energy_root_bound {E A : ℝ≥0∞} (hA : A ≠ ∞) {p x : ℝ}
    (hp : 0 < p) (_hx : 0 ≤ x) (h : E ≤ A * (ENNReal.ofReal x) ^ p) :
    E ^ (1 / p) ≤ ENNReal.ofReal (A.toReal ^ (1 / p) * x) := by
  calc
    _ ≤ (A * (ENNReal.ofReal x) ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow h (by positivity)
    _ = A ^ (1 / p) * ENNReal.ofReal x := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      rw [mul_one_div_cancel hp.ne', ENNReal.rpow_one]
    _ = _ := by
      have hAp : A ^ (1 / p) = ENNReal.ofReal (A.toReal ^ (1 / p)) := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hA]
        exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)
      rw [hAp, ← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

lemma root_constant_nonneg (A : ℝ≥0∞) (p : ℝ) : 0 ≤ A.toReal ^ (1 / p) :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _



lemma endpoint_radial_lintegral {n : ℕ} (hn : 0 < n)
    {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h : Fin n → ℝ, differenceKernel (1 - 1 / p.toReal) p h *
        F (euclideanLength h)) =
      ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p.toReal) * F r := by
  have he : (n : ℝ) + (1 - 1 / p.toReal) * p.toReal = n + p.toReal - 1 := by
    rw [endpoint_weight hp1 hp]
    ring
  simpa only [differenceKernel, euclideanLength, he] using
    weighted_radial_lintegral hn p.toReal F hF

lemma weighted_radial_root_bound {n : ℕ} (hn : 0 < n) {p x : ℝ}
    (hp : 0 < p) (hx : 0 ≤ x) (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    {B : ℝ≥0∞} (hB : B ≠ ∞)
    (h : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p) * F r) ≤
      B * (ENNReal.ofReal x) ^ p) :
    (∫⁻ h : Fin n → ℝ,
      (if h = 0 then 0 else ENNReal.ofReal ‖WithLp.toLp 2 h‖ ^ (-(n + p - 1))) *
        F ‖WithLp.toLp 2 h‖) ^ (1 / p) ≤
      ENNReal.ofReal ((((n : ℝ≥0∞) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) * B).toReal ^ (1 / p) * x) := by
  apply energy_root_bound (ENNReal.mul_ne_top (radial_factor_lt_top n).ne hB) hp hx
  rw [weighted_radial_lintegral hn p F hF]
  exact (mul_le_mul_right h _).trans_eq (mul_assoc _ _ _).symm


lemma lintegral_insertNth {n : ℕ} (i : Fin (n+1))
    (F : Domain (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Domain n, F (i.insertNth t x)) =
      ∫⁻ z in (upper i : Set (Domain (n+1))), F z := by
  have hm := (coordinateEquiv_measurePreserving i).symm (coordinateEquiv i)
  have he := hm.setLIntegral_comp_preimage_emb (coordinateEquiv i).symm.measurableEmbedding F
    (upper i : Set (Domain (n+1)))
  have hs : (coordinateEquiv i).symm ⁻¹' (upper i : Set (Domain (n+1))) =
      Ioi (0 : ℝ) ×ˢ (univ : Set (Transverse i)) := by
    ext z
    rcases z with ⟨t, y⟩
    simp [upper, coordinateEquiv_symm_apply]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at he
  rw [lintegral_prod _ (by exact hF.comp (coordinateEquiv i).symm.measurable |>.aemeasurable)] at he
  rw [← he]
  apply lintegral_congr
  intro t
  have ht : Measurable (fun y : Transverse i => coordinateLine i y t) := by
    apply Measurable.of_eval
    intro j
    dsimp [coordinateLine]
    split_ifs
    · exact measurable_const
    · exact measurable_pi_apply _
  have h := (transverseFinEquiv_measurePreserving i).lintegral_comp (hF.comp ht)
  simpa only [Function.comp_def, coordinateEquiv_symm_apply, coordinateLine_transverseFinEquiv] using h

lemma opNorm_le_sum_coordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d : ℕ} (A : (Fin d → ℝ) →L[ℝ] E) :
    ‖A‖ ≤ ∑ i, ‖A (Pi.single i 1)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg fun i hi => norm_nonneg _)
  intro x
  have hx : x = ∑ i : Fin d, x i • (Pi.single i (1 : ℝ)) := by
    simpa using pi_eq_sum_univ' x
  calc
    ‖A x‖ = ‖∑ i : Fin d, x i • A (Pi.single i 1)‖ := by conv_lhs => rw [hx]; simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin d, ‖x i • A (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ‖A (Pi.single i 1)‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

lemma enorm_opNorm_rpow_le_sum_coordinate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {d : ℕ} (A : (Fin d → ℝ) →L[ℝ] E)
    {p : ℝ} (hp : 1 ≤ p) :
    ‖A‖ₑ ^ p ≤ (d : ℝ≥0∞) ^ (p - 1) * ∑ i, ‖A (Pi.single i 1)‖ₑ ^ p := by
  have h := ENNReal.ofReal_le_ofReal (opNorm_le_sum_coordinate A)
  simp only [ofReal_norm, ENNReal.ofReal_sum_of_nonneg (fun i hi => norm_nonneg _)] at h
  exact (ENNReal.rpow_le_rpow h (by linarith)).trans (by
    simpa using ENNReal.rpow_sum_le_const_mul_sum_rpow Finset.univ
      (fun i : Fin d => ‖A (Pi.single i 1)‖ₑ) hp)

lemma smooth_partial_energy_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i j : Fin d) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f) :
    (∫⁻ z in (upper i : Set (Domain d)),
      ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal) ≤
      ENNReal.ofReal ‖u‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hd := C1Extension.Classical.c1_representative_derivative u f hf.contDiffOn hu j
  have he : (∫⁻ z in (upper i : Set (Domain d)), ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal) =
      ∫⁻ z in (upper i : Set (Domain d)), ‖u.val (coordinateIndex j) z‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [hd] with z hz
    rw [hz]
  rw [he,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' hpR,
    ← eLpNorm_eq_eLpNorm' hp0 hp (Lp.memLp _).aestronglyMeasurable,
    ← Lp.enorm_def, ← ofReal_norm]
  apply ENNReal.rpow_le_rpow _ hpR.le
  exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val (coordinateIndex j))

lemma smooth_fderiv_energy_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (i : Fin d) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f) :
    (∫⁻ z in (upper i : Set (Domain d)), ‖fderiv ℝ f z‖ₑ ^ p.toReal) ≤
      ((d : ℝ≥0∞) ^ (p.toReal-1) * d) * ENNReal.ofReal ‖u‖ ^ p.toReal := by
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hD := hf.continuous_fderiv (by norm_num)
  calc
    _ ≤ ∫⁻ z in (upper i : Set (Domain d)),
        (d : ℝ≥0∞) ^ (p.toReal-1) * ∑ j : Fin d,
          ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal :=
      lintegral_mono (fun z => enorm_opNorm_rpow_le_sum_coordinate _ hpR)
    _ = (d : ℝ≥0∞) ^ (p.toReal-1) * ∑ j : Fin d,
        ∫⁻ z in (upper i : Set (Domain d)), ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal := by
      rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ (by intro j hj; fun_prop)]
    _ ≤ _ := by
      calc
        _ ≤ (d : ℝ≥0∞) ^ (p.toReal-1) * ∑ j : Fin d, ENNReal.ofReal ‖u‖ ^ p.toReal := by
          gcongr with j
          exact smooth_partial_energy_bound i j hp u f hf hu
        _ = _ := by simp [mul_assoc]

lemma smooth_boundary_energy {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n+1)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Lp 𝕜 p (volume : Measure (Domain n))) (f : Domain (n+1) → 𝕜)
    (hg : g =ᵐ[volume] fun x => f (i.insertNth 0 x)) :
    differenceEnergy s p g = ∫⁻ h : Domain n, differenceKernel s p h *
      ∫⁻ x : Domain n, ‖f (i.insertNth 0 (x+h)) - f (i.insertNth 0 x)‖ₑ ^ p.toReal := by
  unfold differenceEnergy
  apply lintegral_congr
  intro h
  congr 1
  apply lintegral_congr_ae
  have hh := (measurePreserving_add_right (volume : Measure (Domain n)) h).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hg, hh] with x hx hxh
  simp only [Function.comp_def] at hxh
  rw [hx, hxh]

lemma enorm_three_sub_rpow_le {E : Type*} [NormedAddCommGroup E]
    (a b c d : E) {p : ℝ} (hp : 1 ≤ p) :
    ‖a-d‖ₑ ^ p ≤ (3 : ℝ≥0∞) ^ (p-1) *
      (‖a-b‖ₑ ^ p + ‖b-c‖ₑ ^ p + ‖c-d‖ₑ ^ p) := by
  have he : a-d = ((a-b)+(b-c))+(c-d) := by abel
  have ht : ‖a-d‖ₑ ≤ ‖a-b‖ₑ + ‖b-c‖ₑ + ‖c-d‖ₑ := by
    rw [he]
    exact (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
  apply (ENNReal.rpow_le_rpow ht (by linarith)).trans
  simpa [Fin.sum_univ_three, add_assoc] using ENNReal.rpow_sum_le_const_mul_sum_rpow
    Finset.univ (fun j : Fin 3 => ![‖a-b‖ₑ, ‖b-c‖ₑ, ‖c-d‖ₑ] j) hp


lemma radial_profile_bound {V B : ℝ → ℝ≥0∞} (hV : Measurable V) (hB : Measurable B)
    {p : ℝ} (_hp : 1 < p) {H D A : ℝ≥0∞}
    (hN : (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r ^ (-p) * V r) ≤ H * A)
    (hT : (∫⁻ r in Ioi (0:ℝ), B r) ≤ D * A) :
    (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r ^ (-p) *
      ((3:ℝ≥0∞) ^ (p-1) * (2 * V r + ENNReal.ofReal r ^ p * B r))) ≤
      ((3:ℝ≥0∞) ^ (p-1) * (2*H+D)) * A := by
  have hm : Measurable (fun r : ℝ => ENNReal.ofReal r ^ (-p) * V r) :=
    (measurable_id.ennreal_ofReal.pow_const _).mul hV
  calc
    _ = ∫⁻ r in Ioi (0:ℝ), (3:ℝ≥0∞) ^ (p-1) *
        (2 * (ENNReal.ofReal r ^ (-p) * V r) + B r) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hc : ENNReal.ofReal r ^ (-p) * ENNReal.ofReal r ^ p = 1 := by
        rw [← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top]
        simp
      calc
        _ = (3:ℝ≥0∞) ^ (p-1) *
            (2 * (ENNReal.ofReal r ^ (-p) * V r) +
              (ENNReal.ofReal r ^ (-p) * ENNReal.ofReal r ^ p) * B r) := by ring
        _ = _ := by rw [hc, one_mul]
    _ = (3:ℝ≥0∞) ^ (p-1) *
        (2 * (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal r ^ (-p) * V r) +
          ∫⁻ r in Ioi (0:ℝ), B r) := by
      rw [lintegral_const_mul _ (show Measurable (fun r : ℝ =>
        2 * (ENNReal.ofReal r ^ (-p) * V r) + B r) by fun_prop)]
      rw [lintegral_add_left (f := fun r : ℝ => 2 * (ENNReal.ofReal r ^ (-p) * V r))
        (hm.const_mul 2) (fun r => B r), lintegral_const_mul _ hm]
    _ ≤ (3:ℝ≥0∞) ^ (p-1) * (2 * (H*A) + D*A) := by gcongr
    _ = _ := by ring


lemma boundary_increment_lintegral_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {n : ℕ} (f₀ fᵣ : Domain n → E) (hf₀ : Measurable f₀) (hfᵣ : Measurable fᵣ)
    (h : Domain n) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖f₀ (x+h) - f₀ x‖ₑ ^ p) ≤
      (3 : ℝ≥0∞) ^ (p-1) *
        (2 * (∫⁻ x, ‖fᵣ x - f₀ x‖ₑ ^ p) +
          ∫⁻ x, ‖fᵣ (x+h) - fᵣ x‖ₑ ^ p) := by
  have hshift : Measurable (fun x : Domain n => x+h) :=
    (continuous_id.add continuous_const).measurable
  have hV : Measurable (fun x : Domain n => ‖fᵣ x - f₀ x‖ₑ ^ p) :=
    (hfᵣ.sub hf₀).enorm.pow_const _
  have hT : Measurable (fun x : Domain n => ‖fᵣ (x+h) - fᵣ x‖ₑ ^ p) :=
    ((hfᵣ.comp hshift).sub hfᵣ).enorm.pow_const _
  have hVshift : Measurable (fun x : Domain n => ‖fᵣ (x+h) - f₀ (x+h)‖ₑ ^ p) :=
    hV.comp hshift
  have htrans : (∫⁻ x : Domain n, ‖fᵣ (x+h) - f₀ (x+h)‖ₑ ^ p) =
      ∫⁻ x : Domain n, ‖fᵣ x - f₀ x‖ₑ ^ p := by
    exact (measurePreserving_add_right (volume : Measure (Domain n)) h).lintegral_comp hV
  calc
    _ ≤ ∫⁻ x : Domain n, (3 : ℝ≥0∞) ^ (p-1) *
        (‖fᵣ (x+h) - f₀ (x+h)‖ₑ ^ p + ‖fᵣ (x+h) - fᵣ x‖ₑ ^ p +
          ‖fᵣ x - f₀ x‖ₑ ^ p) := by
      apply lintegral_mono
      intro x
      simpa only [enorm_sub_rev (f₀ (x+h)) (fᵣ (x+h))] using
        enorm_three_sub_rpow_le (f₀ (x+h)) (fᵣ (x+h)) (fᵣ x) (f₀ x) hp
    _ = _ := by
      have h₁ := lintegral_add_left (μ := (volume : Measure (Domain n)))
        (hVshift.add hT) (fun x => ‖fᵣ x - f₀ x‖ₑ ^ p)
      have h₂ := lintegral_add_left (μ := (volume : Measure (Domain n)))
        hVshift (fun x => ‖fᵣ (x+h) - fᵣ x‖ₑ ^ p)
      simp only [Pi.add_apply] at h₁ h₂
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
        h₁, h₂, htrans]
      congr 1
      ring


end AnalyticEstimates

open AnalyticEstimates

/-- Pointwise FTC, Jensen, Hardy and Euclidean radial integration give the
smooth estimate on the original distributional graph, with no assumed
fractional membership. -/
theorem smooth_seminorm_estimate :
    Specs.ExpandedFA.PartIV.SharpTraceBound.SmoothSeminormEstimate := by
  intro n hn p _ hp1 hp
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).mpr hp1
  let H : ℝ≥0∞ := (2 : ℝ≥0∞) ^ (p.toReal-1) * ENNReal.ofReal (2/(p.toReal-1))
  let D : ℝ≥0∞ := ((n+1 : ℕ) : ℝ≥0∞) ^ (p.toReal-1) * ((n+1 : ℕ) : ℝ≥0∞)
  let S : ℝ≥0∞ := (n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  let A : ℝ≥0∞ := S * ((3 : ℝ≥0∞) ^ (p.toReal-1) * (2*H+D))
  have hA : A ≠ ∞ := by
    dsimp [A, S, H, D]
    apply ENNReal.mul_ne_top (radial_factor_lt_top n).ne
    finiteness
  refine ⟨A.toReal ^ (1/p.toReal), root_constant_nonneg A p.toReal, ?_⟩
  intro 𝕜 _ i u f g hf hu hg
  let e : ℝ × Domain n → Domain (n+1) := fun z => i.insertNth z.1 z.2
  have he : Continuous e := by
    apply continuous_pi
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · simpa [e] using (continuous_fst : Continuous (fun z : ℝ × Domain n => z.1))
    · simpa [e, Function.comp_def] using ((continuous_apply k).comp continuous_snd :
        Continuous (fun z : ℝ × Domain n => z.2 k))
  have he0 : Continuous (fun z : ℝ × Domain n => (i.insertNth (0 : ℝ) z.2 : Domain (n+1))) := by
    change Continuous (e ∘ fun z : ℝ × Domain n => ((0 : ℝ), z.2))
    exact he.comp (continuous_const.prodMk continuous_snd)
  have hes (r : ℝ) : Continuous (fun x : Domain n => (i.insertNth r x : Domain (n+1))) := by
    change Continuous (e ∘ fun x : Domain n => (r, x))
    exact he.comp (continuous_const.prodMk continuous_id)
  let V : ℝ → ℝ≥0∞ := fun r =>
    ∫⁻ x : Domain n, ‖f (i.insertNth r x) - f (i.insertNth 0 x)‖ₑ ^ p.toReal
  let B : ℝ → ℝ≥0∞ := fun r =>
    ∫⁻ x : Domain n, ‖fderiv ℝ f (i.insertNth r x)‖ₑ ^ p.toReal
  let M : ℝ → ℝ≥0∞ := fun r =>
    (3 : ℝ≥0∞) ^ (p.toReal-1) * (2*V r+ENNReal.ofReal r ^ p.toReal * B r)
  have hV : Measurable V :=
    (((hf.continuous.comp he).sub (hf.continuous.comp he0)).enorm.measurable.pow_const _).lintegral_prod_right'
  have hdf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hB : Measurable B :=
    ((hdf.comp he).enorm.measurable.pow_const _).lintegral_prod_right'
  have hM : Measurable M := by dsimp [M]; fun_prop
  have hN : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p.toReal) * V r) ≤
      H * ENNReal.ofReal ‖u‖ ^ p.toReal := by
    have h := normal_insertNth_comparison i f hf hpR
    rw [lintegral_insertNth i _ (((hdf.clm_apply continuous_const).enorm.measurable).pow_const _)] at h
    apply h.trans
    exact mul_le_mul_right (smooth_partial_energy_bound i i hp u f hf hu) H
  have hT : (∫⁻ r in Ioi (0 : ℝ), B r) ≤ D * ENNReal.ofReal ‖u‖ ^ p.toReal := by
    change (∫⁻ r in Ioi (0 : ℝ), ∫⁻ x : Domain n,
      ‖fderiv ℝ f (i.insertNth r x)‖ₑ ^ p.toReal) ≤ _
    rw [lintegral_insertNth i _ (hdf.enorm.measurable.pow_const _)]
    exact smooth_fderiv_energy_bound i hp u f hf hu
  have hprofile : (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p.toReal) * M r) ≤
      ((3 : ℝ≥0∞) ^ (p.toReal-1) * (2*H+D)) * ENNReal.ofReal ‖u‖ ^ p.toReal :=
    radial_profile_bound hV hB hpR hN hT
  have hincrement (h : Domain n) :
      (∫⁻ x : Domain n,
        ‖f (i.insertNth 0 (x+h)) - f (i.insertNth 0 x)‖ₑ ^ p.toReal) ≤
      M (euclideanLength h) := by
    apply (boundary_increment_lintegral_le
      (fun x => f (i.insertNth 0 x)) (fun x => f (i.insertNth (euclideanLength h) x))
      (hf.continuous.comp (hes 0)).measurable
      (hf.continuous.comp (hes (euclideanLength h))).measurable h hpR.le).trans
    dsimp [M, V, B]
    apply mul_le_mul_right
    apply add_le_add_right
    apply (tangential_height_rpow i f hf (euclideanLength h) h hpR.le).trans
    apply mul_le_mul_left
    apply ENNReal.rpow_le_rpow _ (by linarith)
    simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (norm_le_euclideanLength h)
  apply energy_root_bound hA (by linarith : 0 < p.toReal) (norm_nonneg u)
  calc
    _ = ∫⁻ h : Domain n, differenceKernel (1-1/p.toReal) p h *
        ∫⁻ x : Domain n,
          ‖f (i.insertNth 0 (x+h)) - f (i.insertNth 0 x)‖ₑ ^ p.toReal :=
      smooth_boundary_energy i _ p g f hg
    _ ≤ ∫⁻ h : Domain n, differenceKernel (1-1/p.toReal) p h * M (euclideanLength h) :=
      lintegral_mono (fun h => mul_le_mul_right (hincrement h) _)
    _ = S * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (-p.toReal) * M r :=
      endpoint_radial_lintegral hn hp1 hp M hM
    _ ≤ S * (((3 : ℝ≥0∞) ^ (p.toReal-1) * (2*H+D)) * ENNReal.ofReal ‖u‖ ^ p.toReal) :=
      mul_le_mul_right hprofile S
    _ = A * ENNReal.ofReal ‖u‖ ^ p.toReal := (mul_assoc _ _ _).symm

/-- The sharp half-space trace bound with its full Lp-plus-difference norm. -/
theorem sharp_trace_bound : Specs.ExpandedFA.PartIV.SharpTraceBound.BoundedTrace := by
  exact sharp_trace_bound_of_smooth smooth_seminorm_estimate

end ExpandedFA.PartIV.SharpTraceBound
