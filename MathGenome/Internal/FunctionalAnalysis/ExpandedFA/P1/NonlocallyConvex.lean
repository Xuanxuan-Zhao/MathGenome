import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.NonlocallyConvex
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.HahnBanach
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Order.Zorn
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Continuity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.P1.NonlocallyConvex
open NonlocallyConvexSpec

section Metric
variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
  {μ : Measure α} {p : ℝ≥0∞}

lemma powerEDist_ne_top (hp : 0 < p) (hp1 : p < 1) (f g : Lp 𝕜 p μ) :
    powerEDist p μ f g ≠ ∞ := by
  exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp.ne'
    (hp1.trans ENNReal.one_lt_top).ne ((Lp.memLp f).sub (Lp.memLp g)).eLpNorm_lt_top).ne

lemma powerEDist_self (hp : 0 < p) (hp1 : p < 1) (f : Lp 𝕜 p μ) :
    powerEDist p μ f f = 0 := by
  simp [powerEDist, ENNReal.toReal_pos hp.ne' (hp1.trans ENNReal.one_lt_top).ne]

lemma powerEDist_comm (f g : Lp 𝕜 p μ) :
    powerEDist p μ f g = powerEDist p μ g f := by
  unfold powerEDist
  congr 1
  funext x
  rw [enorm_sub_rev]

lemma eq_of_powerEDist_eq_zero (hp : 0 < p) (hp1 : p < 1)
    (f g : Lp 𝕜 p μ) (h : powerEDist p μ f g = 0) : f = g := by
  have hpow := (lintegral_eq_zero_iff' (((Lp.aestronglyMeasurable f).sub
    (Lp.aestronglyMeasurable g)).enorm.pow_const p.toReal)).mp h
  apply Lp.ext
  filter_upwards [hpow] with x hx
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp.ne' (hp1.trans ENNReal.one_lt_top).ne
  have hz : ‖f x - g x‖ₑ = 0 := (ENNReal.rpow_eq_zero_iff_of_pos hpR).mp hx
  exact sub_eq_zero.mp (enorm_eq_zero.mp hz)

lemma powerEDist_triangle (hp : 0 < p) (hp1 : p < 1) (f g h : Lp 𝕜 p μ) :
    powerEDist p μ f h ≤ powerEDist p μ f g + powerEDist p μ g h := by
  unfold powerEDist
  calc
   _ ≤ ∫⁻ x, (‖f x - g x‖ₑ ^ p.toReal + ‖g x - h x‖ₑ ^ p.toReal) ∂μ := ?_
   _ = _ := lintegral_add_left' (((Lp.aestronglyMeasurable f).sub
      (Lp.aestronglyMeasurable g)).enorm.pow_const p.toReal) _
  apply lintegral_mono
  intro x
  calc
    ‖f x - h x‖ₑ ^ p.toReal ≤ (‖f x - g x‖ₑ + ‖g x - h x‖ₑ) ^ p.toReal := by
      gcongr
      calc
        ‖f x - h x‖ₑ = ‖(f x - g x) + (g x - h x)‖ₑ := by congr 1; abel
        _ ≤ _ := enorm_add_le _ _
    _ ≤ _ := ENNReal.rpow_add_le_add_rpow _ _ ENNReal.toReal_nonneg
      (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1.le))

lemma powerEDist_add_right (f g h : Lp 𝕜 p μ) :
    powerEDist p μ (f + h) (g + h) = powerEDist p μ f g := by
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_add f h, Lp.coeFn_add g h] with x hx hy
  simp only [hx, hy, Pi.add_apply, add_sub_add_right_eq_sub]

/-- This metric is used explicitly; the usual `Lp` normed instance is unavailable
in this exponent range and is never assumed. -/
@[instance_reducible]
def powerMetric (hp : 0 < p) (hp1 : p < 1) : MetricSpace (Lp 𝕜 p μ) where
  dist := powerDist p μ
  dist_self f := by rw [powerDist, powerEDist_self hp hp1, ENNReal.toReal_zero]
  dist_comm f g := by rw [powerDist, powerDist, powerEDist_comm]
  dist_triangle f g h := by
    unfold powerDist
    rw [← ENNReal.toReal_add (powerEDist_ne_top hp hp1 f g) (powerEDist_ne_top hp hp1 g h)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨powerEDist_ne_top hp hp1 f g, powerEDist_ne_top hp hp1 g h⟩)
      (powerEDist_triangle hp hp1 f g h)
  eq_of_dist_eq_zero {f g} h := by
    apply eq_of_powerEDist_eq_zero hp hp1 f g
    exact (ENNReal.toReal_eq_zero_iff _).mp h |>.resolve_right (powerEDist_ne_top hp hp1 f g)

lemma powerDist_eq_integral (hp : 0 < p) (hp1 : p < 1) (f g : Lp 𝕜 p μ) :
    powerDist p μ f g = ∫ x, ‖f x - g x‖ ^ p.toReal ∂μ := by
  symm
  calc
    _ = (∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ p.toReal) ∂μ).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))
        (((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g)).norm.aemeasurable.pow_const
          p.toReal).aestronglyMeasurable
    _ = powerDist p μ f g := by
      unfold powerDist powerEDist
      congr 1
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]

lemma powerEDist_smul (c : 𝕜) (f g : Lp 𝕜 p μ) :
    powerEDist p μ (c • f) (c • g) = ‖c‖ₑ ^ p.toReal * powerEDist p μ f g := by
  unfold powerEDist
  calc
    _ = ∫⁻ x, ‖c‖ₑ ^ p.toReal * ‖f x - g x‖ₑ ^ p.toReal ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with x hf hg
      simp only [hf, hg, Pi.smul_apply, ← smul_sub, enorm_smul,
        ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
    _ = _ := lintegral_const_mul'' _ (((Lp.aestronglyMeasurable f).sub
      (Lp.aestronglyMeasurable g)).enorm.pow_const p.toReal)

lemma powerDist_smul (c : 𝕜) (f g : Lp 𝕜 p μ) :
    powerDist p μ (c • f) (c • g) = ‖c‖ ^ p.toReal * powerDist p μ f g := by
  simp only [powerDist, powerEDist_smul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    toReal_enorm]

lemma powerDist_add_right (f g h : Lp 𝕜 p μ) :
    powerDist p μ (f + h) (g + h) = powerDist p μ f g :=
  congrArg ENNReal.toReal (powerEDist_add_right f g h)

lemma powerDist_add_le (hp : 0 < p) (hp1 : p < 1) (f₁ f₂ g₁ g₂ : Lp 𝕜 p μ) :
    powerDist p μ (f₁ + f₂) (g₁ + g₂) ≤ powerDist p μ f₁ g₁ + powerDist p μ f₂ g₂ := by
  letI := powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1
  letI : Dist (Lp 𝕜 p μ) := (powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1).toDist
  letI : EDist (Lp 𝕜 p μ) := (powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1).toEDist
  calc
    _ ≤ powerDist p μ (f₁ + f₂) (g₁ + f₂) + powerDist p μ (g₁ + f₂) (g₁ + g₂) :=
      (powerMetric hp hp1).dist_triangle _ _ _
    _ = _ := by rw [powerDist_add_right, add_comm g₁ f₂, add_comm g₁ g₂,
      powerDist_add_right]

lemma powerDist_sub (hp : 0 < p) (hp1 : p < 1) (f g : Lp 𝕜 p μ) :
    powerDist p μ f g = powerDist p μ (f - g) 0 := by
  simpa only [← sub_eq_add_neg, sub_self] using (powerDist_add_right (p := p) f g (-g)).symm

/-- The power metric makes the original vector space a TVS. -/
theorem powerMetric_tvs (hp : 0 < p) (hp1 : p < 1) :
    letI := powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1
    TVS 𝕜 (Lp 𝕜 p μ) := by
  letI := powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1
  letI : Dist (Lp 𝕜 p μ) := (powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1).toDist
  letI : EDist (Lp 𝕜 p μ) := (powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1).toEDist
  have hadd : Continuous (fun q : Lp 𝕜 p μ × Lp 𝕜 p μ => q.1 + q.2) := by
    apply LipschitzWith.continuous (K := 2)
    apply LipschitzWith.of_dist_le_mul
    intro f g
    change powerDist p μ (f.1 + f.2) (g.1 + g.2) ≤ 2 * max _ _
    calc
      _ ≤ powerDist p μ f.1 g.1 + powerDist p μ f.2 g.2 := powerDist_add_le hp hp1 _ _ _ _
      _ ≤ _ := by
        change powerDist p μ f.1 g.1 + powerDist p μ f.2 g.2 ≤
          2 * max (powerDist p μ f.1 g.1) (powerDist p μ f.2 g.2)
        nlinarith [le_max_left (powerDist p μ f.1 g.1) (powerDist p μ f.2 g.2),
          le_max_right (powerDist p μ f.1 g.1) (powerDist p μ f.2 g.2)]
  have hneg : Continuous (fun f : Lp 𝕜 p μ => -f) := by
    have hdist (f g : Lp 𝕜 p μ) : dist (-f) (-g) = dist f g := by
      change powerDist p μ (-f) (-g) = powerDist p μ f g
      simpa only [neg_one_smul, norm_neg, norm_one, Real.one_rpow, one_mul] using
        powerDist_smul (-1 : 𝕜) f g
    exact (Isometry.of_dist_eq hdist).continuous
  letI : IsTopologicalAddGroup (Lp 𝕜 p μ) := { continuous_add := hadd, continuous_neg := hneg }
  refine ⟨inferInstance, ⟨continuous_iff_continuousAt.mpr fun q => ?_⟩⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound (v : 𝕜 × Lp 𝕜 p μ) :
      dist (v.1 • v.2) (q.1 • q.2) ≤
        ‖v.1‖ ^ p.toReal * dist v.2 q.2 + ‖v.1 - q.1‖ ^ p.toReal * dist q.2 0 := by
    calc
      _ ≤ dist (v.1 • v.2) (v.1 • q.2) + dist (v.1 • q.2) (q.1 • q.2) :=
        dist_triangle _ _ _
      _ = _ := by
        change powerDist p μ (v.1 • v.2) (v.1 • q.2) +
          powerDist p μ (v.1 • q.2) (q.1 • q.2) =
          ‖v.1‖ ^ p.toReal * powerDist p μ v.2 q.2 +
            ‖v.1 - q.1‖ ^ p.toReal * powerDist p μ q.2 0
        rw [powerDist_smul, powerDist_sub hp hp1 (v.1 • q.2), ← sub_smul]
        congr 1
        simpa only [smul_zero] using powerDist_smul (v.1 - q.1) q.2 (0 : Lp 𝕜 p μ)
  have hlim : Tendsto (fun v : 𝕜 × Lp 𝕜 p μ =>
      ‖v.1‖ ^ p.toReal * dist v.2 q.2 + ‖v.1 - q.1‖ ^ p.toReal * dist q.2 0)
      (𝓝 q) (𝓝 0) := by
    have hc : Continuous (fun v : 𝕜 × Lp 𝕜 p μ =>
        ‖v.1‖ ^ p.toReal * dist v.2 q.2 + ‖v.1 - q.1‖ ^ p.toReal * dist q.2 0) := by
      fun_prop (disch := exact Or.inr ENNReal.toReal_nonneg)
    simpa [Real.zero_rpow (ENNReal.toReal_pos hp.ne' (hp1.trans ENNReal.one_lt_top).ne).ne'] using hc.tendsto q
  exact squeeze_zero (fun _ => dist_nonneg) hbound hlim

/-! Completeness is reduced to ordinary Bochner `L¹` with values in the
snowflaked scalar additive group. Its norm is `‖z‖^p`; scalar homogeneity is
not asserted for this auxiliary norm. Its metric uniformity agrees with the
usual scalar uniformity, so it is complete. -/

abbrev Snow (𝕜 : Type*) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p < 1) :=
  Metric.Snowflaking 𝕜 p.toReal
    (ENNReal.toReal_pos hp.ne' (hp1.trans ENNReal.one_lt_top).ne)
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1.le))

instance snowAddCommGroup {r : ℝ} {hr0 : 0 < r} {hr1 : r ≤ 1} :
    AddCommGroup (Metric.Snowflaking 𝕜 r hr0 hr1) :=
  Metric.Snowflaking.ofSnowflaking.addCommGroup

instance snowNorm {r : ℝ} {hr0 : 0 < r} {hr1 : r ≤ 1} :
    Norm (Metric.Snowflaking 𝕜 r hr0 hr1) :=
  ⟨fun x => ‖x.val‖ ^ r⟩

instance snowNormedAddCommGroup {r : ℝ} {hr0 : 0 < r} {hr1 : r ≤ 1} :
    NormedAddCommGroup (Metric.Snowflaking 𝕜 r hr0 hr1) where
  dist_eq x y := by
    change dist x.val y.val ^ r = ‖-x.val + y.val‖ ^ r
    rw [dist_eq_norm_neg_add]

instance snowCompleteSpace {r : ℝ} {hr0 : 0 < r} {hr1 : r ≤ 1} :
    CompleteSpace (Metric.Snowflaking 𝕜 r hr0 hr1) :=
  (Metric.Snowflaking.uniformEquiv.completeSpace_iff).mpr inferInstance

lemma snow_enorm (hp : 0 < p) (hp1 : p < 1) (x : Snow 𝕜 p hp hp1) :
    ‖x‖ₑ = ‖x.val‖ₑ ^ p.toReal := by
  rw [← ofReal_norm]
  change ENNReal.ofReal (‖x.val‖ ^ p.toReal) = _
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg, ofReal_norm]

lemma memLp_snow (hp : 0 < p) (hp1 : p < 1) (f : Lp 𝕜 p μ) :
    MemLp (fun x => (⟨f x⟩ : Snow 𝕜 p hp hp1)) 1 μ := by
  have hm : AEStronglyMeasurable (fun x => (⟨f x⟩ : Snow 𝕜 p hp hp1)) μ :=
    Metric.Snowflaking.continuous_toSnowflaking.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)
  change eLpNorm (fun x => (⟨f x⟩ : Snow 𝕜 p hp hp1)) 1 μ < ∞
  rw [eLpNorm_one_eq_lintegral_enorm hm]
  simp_rw [snow_enorm hp hp1]
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp.ne'
    (hp1.trans ENNReal.one_lt_top).ne (Lp.eLpNorm_lt_top f)

lemma memLp_of_snow (hp : 0 < p) (hp1 : p < 1) (g : Lp (Snow 𝕜 p hp hp1) 1 μ) :
    MemLp (fun x => (g x).val) p μ := by
  have hm := Metric.Snowflaking.continuous_ofSnowflaking.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable g)
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp.ne'
    (hp1.trans ENNReal.one_lt_top).ne hm).mpr
  simp_rw [← snow_enorm hp hp1]
  change (∫⁻ a, ‖g a‖ₑ ∂μ) < ∞
  rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable g)]
  exact (Lp.eLpNorm_lt_top g)

def toSnowLp (hp : 0 < p) (hp1 : p < 1) (f : Lp 𝕜 p μ) : Lp (Snow 𝕜 p hp hp1) 1 μ :=
  (memLp_snow hp hp1 f).toLp _

def fromSnowLp (hp : 0 < p) (hp1 : p < 1) (g : Lp (Snow 𝕜 p hp hp1) 1 μ) : Lp 𝕜 p μ :=
  (memLp_of_snow hp hp1 g).toLp _

lemma from_toSnowLp (hp : 0 < p) (hp1 : p < 1) (f : Lp 𝕜 p μ) :
    fromSnowLp hp hp1 (toSnowLp hp hp1 f) = f := by
  apply Lp.ext
  filter_upwards [(memLp_of_snow hp hp1 (toSnowLp hp hp1 f)).coeFn_toLp,
    (memLp_snow hp hp1 f).coeFn_toLp] with x hx hy
  exact hx.trans (congrArg Metric.Snowflaking.val hy)

lemma to_fromSnowLp (hp : 0 < p) (hp1 : p < 1) (g : Lp (Snow 𝕜 p hp hp1) 1 μ) :
    toSnowLp hp hp1 (fromSnowLp hp hp1 g) = g := by
  apply Lp.ext
  filter_upwards [(memLp_snow hp hp1 (fromSnowLp hp hp1 g)).coeFn_toLp,
    (memLp_of_snow hp hp1 g).coeFn_toLp] with x hx hy
  exact hx.trans (congrArg (fun z => (⟨z⟩ : Snow 𝕜 p hp hp1)) hy)

lemma dist_toSnowLp (hp : 0 < p) (hp1 : p < 1) (f g : Lp 𝕜 p μ) :
    dist (toSnowLp hp hp1 f) (toSnowLp hp hp1 g) = powerDist p μ f g := by
  rw [Lp.dist_def, eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
  unfold powerDist powerEDist
  congr 1
  apply lintegral_congr_ae
  filter_upwards [(memLp_snow hp hp1 f).coeFn_toLp,
    (memLp_snow hp hp1 g).coeFn_toLp] with x hx hy
  change (toSnowLp hp hp1 f) x = (⟨f x⟩ : Snow 𝕜 p hp hp1) at hx
  change (toSnowLp hp hp1 g) x = (⟨g x⟩ : Snow 𝕜 p hp hp1) at hy
  simp only [Pi.sub_apply, hx, hy, snow_enorm hp hp1]
  rfl

/-- The exact power metric is complete on every measure space. -/
theorem powerMetric_complete (hp : 0 < p) (hp1 : p < 1) :
    @CompleteSpace (Lp 𝕜 p μ) (powerMetric hp hp1).toUniformSpace := by
  letI := powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1
  let e : Lp 𝕜 p μ ≃ᵢ Lp (Snow 𝕜 p hp hp1) 1 μ :=
    { toFun := toSnowLp hp hp1
      invFun := fromSnowLp hp hp1
      left_inv := from_toSnowLp hp hp1
      right_inv := to_fromSnowLp hp hp1
      isometry_toFun := Isometry.of_dist_eq (dist_toSnowLp hp hp1) }
  exact e.completeSpace_iff.mpr inferInstance

end Metric

theorem metric_realization : NonlocallyConvexSpec.MetricRealization := by
  intro α 𝕜 _ _ μ p hp hp1
  refine ⟨powerMetric hp hp1, fun _ _ => rfl, ?_, powerDist_eq_integral hp hp1⟩
  intro f g h
  exact congrArg ENNReal.toReal (powerEDist_add_right f g h)

/-- A metric realizing the prescribed distance is uniquely determined,
including its topology and uniformity. -/
lemma powerMetric_unique {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    {μ : Measure α} {p : ℝ≥0∞} (hp : 0 < p) (hp1 : p < 1)
    (m : MetricSpace (Lp 𝕜 p μ))
    (hm : ∀ f g, @dist _ m.toDist f g = powerDist p μ f g) :
    m = powerMetric hp hp1 := by
  apply MetricSpace.ext
  ext f g
  exact hm f g

theorem complete_vector_topology : NonlocallyConvexSpec.CompleteVectorTopology := by
  intro α 𝕜 _ _ μ p hp hp1 m hm
  have heq := powerMetric_unique hp hp1 m hm
  subst m
  exact ⟨powerMetric_complete hp hp1, powerMetric_tvs hp hp1⟩

/-! Finite nonatomic measures have subsets of every intermediate mass. -/

section FinitePartitions
open Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma finite_half_subset
    (hμ : ∀ s : Set α, MeasurableSet s → 0 < μ s →
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s)
    {s : Set α} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ.real t ∧ μ.real t ≤ μ.real s / 2 := by
  have hspos : 0 < μ s := (ENNReal.toReal_pos_iff.mp hpos).1
  obtain ⟨t, ht, hts, htpos, htlt⟩ := hμ s hs hspos
  have htRpos : 0 < μ.real t := ENNReal.toReal_pos htpos.ne' (measure_ne_top _ _)
  have htRlt : μ.real t < μ.real s :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr htlt
  by_cases hsmall : μ.real t ≤ μ.real s / 2
  · exact ⟨t, ht, hts, htRpos, hsmall⟩
  · refine ⟨s \ t, hs.diff ht, sdiff_subset, ?_, ?_⟩
    all_goals rw [measureReal_sdiff hts ht]
    · linarith
    · linarith

lemma finite_small_subset
    (hμ : ∀ s : Set α, MeasurableSet s → 0 < μ s →
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s)
    {s : Set α} (hs : MeasurableSet s) (hpos : 0 < μ.real s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ.real t ∧ μ.real t ≤ ε := by
  have hiter : ∀ n : ℕ, ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧
      0 < μ.real t ∧ μ.real t ≤ μ.real s * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => exact ⟨s, hs, Subset.rfl, hpos, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, hts, htpos, htle⟩ := ih
      obtain ⟨u, hu, hut, hupos, hule⟩ := finite_half_subset hμ ht htpos
      refine ⟨u, hu, hut.trans hts, hupos, ?_⟩
      rw [pow_succ]
      nlinarith
  have hlim : Tendsto (fun n : ℕ => μ.real s * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul (μ.real s)
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨t, ht, hts, htpos, htle⟩ := hiter n
  exact ⟨t, ht, hts, htpos, htle.trans hn.le⟩

lemma finite_subset_measureReal_eq
    (hμ : ∀ s : Set α, MeasurableSet s → 0 < μ s →
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s)
    {s : Set α} (hs : MeasurableSet s) {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ μ.real s) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ μ.real t = b := by
  classical
  let P := {t : Set α // MeasurableSet t ∧ t ⊆ s ∧ μ.real t ≤ b}
  let R : P → P → Prop := fun t u => t = u ∨ (t.val ⊆ u.val ∧ μ.real t.val < μ.real u.val)
  have htrans : ∀ {a b c : P}, R a b → R b c → R a c := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨hab, hμab⟩
    · exact hbc
    rcases hbc with rfl | ⟨hbc, hμbc⟩
    · exact Or.inr ⟨hab, hμab⟩
    · exact Or.inr ⟨hab.trans hbc, hμab.trans hμbc⟩
  have hbound : ∀ c : Set P, IsChain R c → ∃ ub : P, ∀ a ∈ c, R a ub := by
    intro c hc
    rcases c.eq_empty_or_nonempty with rfl | hcn
    · exact ⟨⟨∅, MeasurableSet.empty, empty_subset _, by simpa using hb0⟩, by simp⟩
    let M : Set ℝ := (fun t : P => μ.real t.val) '' c
    have hMn : M.Nonempty := hcn.image _
    have hMb : BddAbove M := ⟨b, by rintro _ ⟨t, ht, rfl⟩; exact t.property.2.2⟩
    have hMle (t : P) (ht : t ∈ c) : μ.real t.val ≤ sSup M :=
      le_csSup hMb (mem_image_of_mem _ ht)
    by_cases hmax : sSup M ∈ M
    · obtain ⟨t, ht, hteq⟩ := hmax
      refine ⟨t, ?_⟩
      intro a ha
      by_cases hat : a = t
      · exact Or.inl hat
      · rcases hc ha ht hat with h | h
        · exact h
        · rcases h with h | ⟨_, hlt⟩
          · exact (hat h.symm).elim
          · exact (not_lt_of_ge (hMle a ha) (hteq ▸ hlt)).elim
    · obtain ⟨v, hvmono, hvlim, hvmem⟩ := exists_seq_tendsto_sSup hMn hMb
      choose t ht htval using hvmem
      change ∀ n, μ.real (t n).val = v n at htval
      have htmono : Monotone (fun n => (t n).val) := by
        intro n m hnm
        change (t n).val ⊆ (t m).val
        by_cases htm : t n = t m
        · rw [htm]
        rcases hc (ht n) (ht m) htm with h | h
        · rcases h with h | ⟨h, _⟩
          · exact h ▸ Subset.rfl
          · exact h
        · rcases h with h | ⟨_, hlt⟩
          · exact h.symm ▸ Subset.rfl
          · rw [htval m, htval n] at hlt
            exact (not_lt_of_ge (hvmono hnm) hlt).elim
      let u : Set α := ⋃ n, (t n).val
      have hum : MeasurableSet u := MeasurableSet.iUnion fun n => (t n).property.1
      have hulim : Tendsto (fun n => μ.real (t n).val) atTop (𝓝 (μ.real u)) := by
        exact ENNReal.continuousAt_toReal (measure_ne_top μ u) |>.tendsto.comp
          (tendsto_measure_iUnion_atTop htmono)
      have hμu : μ.real u = sSup M := by
        apply tendsto_nhds_unique hulim
        simpa only [htval] using hvlim
      have huP : MeasurableSet u ∧ u ⊆ s ∧ μ.real u ≤ b := by
        refine ⟨hum, iUnion_subset fun n => (t n).property.2.1, ?_⟩
        rw [hμu]
        exact csSup_le hMn (by rintro _ ⟨a, ha, rfl⟩; exact a.property.2.2)
      refine ⟨⟨u, huP⟩, ?_⟩
      intro a ha
      have hlt : μ.real a.val < sSup M := lt_of_le_of_ne (hMle a ha)
        (fun heq => hmax (heq ▸ mem_image_of_mem (fun t : P => μ.real t.val) ha))
      have hex : ∃ n, μ.real a.val < v n := by
        obtain ⟨n, hn⟩ := (hvlim.eventually (lt_mem_nhds hlt)).exists
        exact ⟨n, hn⟩
      obtain ⟨n, hn⟩ := hex
      have han : R a (t n) := by
        by_cases han : a = t n
        · exact Or.inl han
        rcases hc ha (ht n) han with h | h
        · exact h
        · rcases h with h | ⟨_, hlt'⟩
          · exact (han h.symm).elim
          · rw [htval n] at hlt'
            exact (not_lt_of_ge hn.le hlt').elim
      refine Or.inr ⟨?_, by simpa only [hμu] using hlt⟩
      change a.val ⊆ u
      rcases han with rfl | ⟨han, _⟩
      · exact subset_iUnion (fun n => (t n).val) n
      · exact han.trans (subset_iUnion (fun n => (t n).val) n)
  obtain ⟨t, htmax⟩ := exists_maximal_of_chains_bounded hbound htrans
  have hteq : μ.real t.val = b := by
    by_contra hne
    have htlt : μ.real t.val < b := lt_of_le_of_ne t.property.2.2 hne
    have hrempos : 0 < μ.real (s \ t.val) := by
      rw [measureReal_sdiff t.property.2.1 t.property.1]
      linarith
    obtain ⟨a, ham, has, hapos, hale⟩ := finite_small_subset hμ
      (hs.diff t.property.1) hrempos (sub_pos.mpr htlt)
    have hdis : Disjoint t.val a := disjoint_left.mpr fun x hxt hxa => (has hxa).2 hxt
    have hmass : μ.real (t.val ∪ a) = μ.real t.val + μ.real a := measureReal_union hdis ham
    let u : P := ⟨t.val ∪ a, t.property.1.union ham,
      union_subset t.property.2.1 (has.trans sdiff_subset), by rw [hmass]; linarith⟩
    have htu : R t u := Or.inr ⟨subset_union_left, by change _ < μ.real (t.val ∪ a); rw [hmass]; linarith⟩
    rcases htmax u htu with h | ⟨_, hlt⟩
    · have := congrArg (fun z : P => μ.real z.val) h
      change μ.real (t.val ∪ a) = μ.real t.val at this
      rw [hmass] at this
      linarith
    · change μ.real (t.val ∪ a) < μ.real t.val at hlt
      rw [hmass] at hlt
      linarith
  exact ⟨t.val, t.property.1, t.property.2.1, hteq⟩

lemma finite_subset_measure_eq
    (hμ : ∀ s : Set α, MeasurableSet s → 0 < μ s →
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s)
    {s : Set α} (hs : MeasurableSet s) {b : ℝ≥0∞} (hb : b ≤ μ s) :
    ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ μ t = b := by
  have hbtop : b ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ s) hb
  obtain ⟨t, htm, hts, htb⟩ := finite_subset_measureReal_eq hμ hs ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (measure_ne_top μ s) hb)
  refine ⟨t, htm, hts, ?_⟩
  calc
    μ t = ENNReal.ofReal (μ.real t) := (ofReal_measureReal (measure_ne_top μ t)).symm
    _ = ENNReal.ofReal b.toReal := congrArg ENNReal.ofReal htb
    _ = b := ENNReal.ofReal_toReal hbtop

theorem finite_partition_of_divisibility {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    (hdiv : ∀ s, MeasurableSet s → ∀ b : ℝ≥0∞, b ≤ μ s →
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ t = b)
    (n : ℕ) (hn : 0 < n) {A : Set α} (hA : MeasurableSet A) (r : ℝ≥0∞)
    (hmass : μ A = n * r) :
    ∃ s : Fin n → Set α,
      (∀ i, MeasurableSet (s i) ∧ s i ⊆ A ∧ μ (s i) = r) ∧
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧ (⋃ i, s i) = A := by
  induction n generalizing A with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨fun _ ↦ A, ?_, ?_, ?_⟩
      · intro i
        exact ⟨hA, subset_refl _, by simpa using hmass⟩
      · intro i j hij
        have hij0 : i = j := by apply Fin.ext; omega
        exact (hij hij0).elim
      · ext x
        simp only [mem_iUnion]
        exact ⟨fun h ↦ h.choose_spec, fun hx ↦ ⟨⟨0, by omega⟩, hx⟩⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hrle : r ≤ μ A := by
      rw [hmass, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact le_add_left le_rfl
    obtain ⟨t, ht, htA, htmeasure⟩ := hdiv A hA r hrle
    have hrfin : r ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ A) hrle
    have hremmass : μ (A \ t) = n * r := by
      rw [measure_sdiff htA ht.nullMeasurableSet (measure_ne_top μ t),
        hmass, htmeasure, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        ENNReal.add_sub_cancel_right hrfin]
    obtain ⟨s, hs, hdisj, hcover⟩ := ih hnpos (hA.diff ht) hremmass
    let S : Fin (n + 1) → Set α := Fin.cons t s
    refine ⟨S, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact ⟨ht, htA, htmeasure⟩
      · exact ⟨(hs j).1, (hs j).2.1.trans sdiff_subset, (hs j).2.2⟩
    · apply (pairwise_fin_succ_iff (R := fun i j : Fin (n + 1) ↦
        Disjoint (S i) (S j))).mpr
      refine ⟨?_, ?_, ?_⟩
      · intro i
        exact (disjoint_sdiff_left.mono_left (hs i).2.1)
      · intro i
        exact (disjoint_sdiff_right.mono_right (hs i).2.1)
      · simpa only [S, Fin.cons_succ] using hdisj
    · ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        refine Fin.cases ?_ (fun j hj ↦ ?_) i hi
        · intro hxt
          exact htA (by simpa only [S, Fin.cons_zero] using hxt)
        · exact ((hs j).2.1 (by simpa only [S, Fin.cons_succ] using hj)).1
      · intro hx
        by_cases hxt : x ∈ t
        · exact ⟨0, hxt⟩
        · have hxrem : x ∈ ⋃ i, s i := by rw [hcover]; exact ⟨hx, hxt⟩
          obtain ⟨i, hi⟩ := mem_iUnion.mp hxrem
          exact ⟨i.succ, hi⟩

theorem equal_finite_partition_of_divisibility {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    (hdiv : ∀ s, MeasurableSet s → ∀ b : ℝ≥0∞, b ≤ μ s →
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ t = b)
    (n : ℕ) (hn : 0 < n) :
    ∃ s : Fin n → Set α,
      (∀ i, MeasurableSet (s i)) ∧
      Pairwise (fun i j ↦ Disjoint (s i) (s j)) ∧
      (⋃ i, s i) = univ ∧ (∀ i, μ (s i) = μ univ / n) := by
  have hncast : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨s, hs, hdisj, hcover⟩ := finite_partition_of_divisibility hdiv n hn
    MeasurableSet.univ (μ univ / n)
    (ENNReal.mul_div_cancel hncast (ENNReal.natCast_ne_top n)).symm
  exact ⟨s, fun i ↦ (hs i).1, hdisj, hcover, fun i ↦ (hs i).2.2⟩


end FinitePartitions

/-! Nonatomic weighted measures and restriction to measurable partitions. -/

theorem nonatomic_withDensity {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : Nonatomic μ) (w : α → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∫⁻ x, w x ∂μ < ∞) : Nonatomic (μ.withDensity w) := by
  let : IsFiniteMeasure (μ.withDensity w) := isFiniteMeasure_withDensity hfin.ne
  intro s hs hpos
  let A := {x | w x ≠ 0} ∩ s
  have hA : MeasurableSet A := (hw (measurableSet_singleton 0)).compl.inter hs
  have hApos : 0 < μ A := by
    apply pos_iff_ne_zero.mpr
    intro hz
    exact hpos.ne' ((withDensity_apply_eq_zero hw).mpr hz)
  obtain ⟨t, ht, htA, htpos, htlt⟩ := hμ A hA hApos
  have hts : t ⊆ s := fun x hx ↦ (htA hx).2
  have htSupp : {x | w x ≠ 0} ∩ t = t := by
    ext x
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(htA h).1, h⟩⟩
  have hνt : 0 < μ.withDensity w t := by
    apply pos_iff_ne_zero.mpr
    intro hz
    apply htpos.ne'
    rw [← htSupp]
    exact (withDensity_apply_eq_zero hw).mp hz
  have hAdiff : 0 < μ (A \ t) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    exact htlt.ne (measure_eq_measure_of_null_sdiff htA hz)
  have hSuppdiff : {x | w x ≠ 0} ∩ (s \ t) = A \ t := by
    ext x
    simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hνdiff : 0 < μ.withDensity w (s \ t) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    apply hAdiff.ne'
    rw [← hSuppdiff]
    exact (withDensity_apply_eq_zero hw).mp hz
  refine ⟨t, ht, hts, hνt, ?_⟩
  have heq : μ.withDensity w t + μ.withDensity w (s \ t) = μ.withDensity w s := by
    rw [measure_add_sdiff ht.nullMeasurableSet, Set.union_eq_self_of_subset_left hts]
  calc
    μ.withDensity w t < μ.withDensity w t + μ.withDensity w (s \ t) := by
      exact ENNReal.lt_add_right (measure_ne_top _ _) hνdiff.ne'
    _ = μ.withDensity w s := heq


theorem nonatomic_withDensity_of_aemeasurable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (hμ : Nonatomic μ) (w : α → ℝ≥0∞) (hw : AEMeasurable w μ)
    (hfin : ∫⁻ x, w x ∂μ < ∞) : Nonatomic (μ.withDensity w) := by
  rw [withDensity_congr_ae hw.ae_eq_mk]
  apply nonatomic_withDensity hμ _ hw.measurable_mk
  rwa [← lintegral_congr_ae hw.ae_eq_mk]

theorem lp_weight_measurable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (p : ℝ≥0∞) (μ : Measure α) (f : Lp 𝕜 p μ) :
    Measurable (fun x ↦ ‖f x‖ₑ ^ p.toReal) := by
  exact (Lp.stronglyMeasurable f).measurable.enorm.pow_const _

theorem lp_weight_lt_top {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (p : ℝ≥0∞) (μ : Measure α) (hp : 0 < p) (hp1 : p < 1) (f : Lp 𝕜 p μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ < ∞ := by
  exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp.ne'
    (ne_of_lt (hp1.trans ENNReal.one_lt_top)) (Lp.eLpNorm_lt_top f)

theorem nonatomic_lp_weight {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (p : ℝ≥0∞) (μ : Measure α) (hp : 0 < p) (hp1 : p < 1)
    (hμ : Nonatomic μ) (f : Lp 𝕜 p μ) :
    Nonatomic (μ.withDensity (fun x ↦ ‖f x‖ₑ ^ p.toReal)) :=
  nonatomic_withDensity hμ _ (lp_weight_measurable p μ f) (lp_weight_lt_top p μ hp hp1 f)


section Partitions
variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
  {μ : Measure α} {p : ℝ≥0∞}

def restrictLp (f : Lp 𝕜 p μ) (s : Set α) (hs : MeasurableSet s) : Lp 𝕜 p μ :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)

lemma restrictLp_coe (f : Lp 𝕜 p μ) (s : Set α) (hs : MeasurableSet s) :
    ⇑(restrictLp f s hs) =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp

lemma powerEDist_restrictLp (hp : 0 < p) (hp1 : p < 1)
    (f : Lp 𝕜 p μ) (s : Set α) (hs : MeasurableSet s) :
    powerEDist p μ (restrictLp f s hs) 0 =
      (μ.withDensity (fun x => ‖f x‖ₑ ^ p.toReal)) s := by
  rw [withDensity_apply _ hs]
  unfold powerEDist
  rw [← lintegral_indicator hs]
  apply lintegral_congr_ae
  filter_upwards [restrictLp_coe f s hs, Lp.coeFn_zero 𝕜 p μ] with x hx hz
  simp only [hx, hz, Pi.zero_apply, sub_zero]
  by_cases hxs : x ∈ s
  · simp [Set.indicator_of_mem hxs]
  · simp [Set.indicator_of_notMem hxs,
      ENNReal.toReal_pos hp.ne' (hp1.trans ENNReal.one_lt_top).ne]

lemma sum_restrictLp {n : ℕ} (f : Lp 𝕜 p μ)
    (s : Fin n → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : (⋃ i, s i) = Set.univ) :
    ∑ i, restrictLp f (s i) (hs i) = f := by
  classical
  apply Lp.ext
  have heq : ∀ᵐ x ∂μ, ∀ i, restrictLp f (s i) (hs i) x = (s i).indicator f x :=
    ae_all_iff.mpr fun i => restrictLp_coe f (s i) (hs i)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => restrictLp f (s i) (hs i)),
    heq] with x hx hi
  rw [hx]
  simp_rw [hi]
  obtain ⟨i, hix⟩ : ∃ i, x ∈ s i := by
    have : x ∈ ⋃ i, s i := by rw [hcover]; trivial
    simpa only [Set.mem_iUnion] using this
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hix _
  · intro j _ hji
    exact Set.indicator_of_notMem (fun hjx => (Set.disjoint_left.mp (hdisj hji)) hjx hix) _
  · simp

lemma weightedMeasure_univ (f : Lp 𝕜 p μ) :
    (μ.withDensity (fun x => ‖f x‖ₑ ^ p.toReal)) Set.univ = powerEDist p μ f 0 := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold powerEDist
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_zero 𝕜 p μ] with x hx
  simp only [hx, Pi.zero_apply, sub_zero]

lemma decompositions_of_weighted_partition (hp : 0 < p) (hp1 : p < 1)
    (f : Lp 𝕜 p μ) {n : ℕ}
    (s : Fin n → Set α) (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise fun i j => Disjoint (s i) (s j))
    (hcover : (⋃ i, s i) = Set.univ)
    (hmass : ∀ i, (μ.withDensity (fun x => ‖f x‖ₑ ^ p.toReal)) (s i) ≤
      (μ.withDensity (fun x => ‖f x‖ₑ ^ p.toReal)) Set.univ / (n : ℝ≥0∞)) :
    ∃ g : Fin n → Lp 𝕜 p μ, (∑ i, g i) = f ∧
      ∀ i, powerDist p μ (g i) 0 ≤ powerDist p μ f 0 / n := by
  refine ⟨fun i => restrictLp f (s i) (hs i), sum_restrictLp f s hs hdisj hcover, ?_⟩
  intro i
  unfold powerDist
  rw [powerEDist_restrictLp hp hp1]
  have hfin : (μ.withDensity (fun x => ‖f x‖ₑ ^ p.toReal)) Set.univ / (n : ℝ≥0∞) ≠ ∞ := by
    rw [weightedMeasure_univ]
    exact ENNReal.div_ne_top (powerEDist_ne_top hp hp1 f 0) (by simpa using (Nat.zero_lt_of_lt i.isLt).ne')
  have hle := ENNReal.toReal_mono hfin (hmass i)
  rwa [weightedMeasure_univ, ENNReal.toReal_div, ENNReal.toReal_natCast] at hle

/-- Nonatomicity supplies all the finite equal-mass decompositions used in the
continuous-dual argument. Only the weighted measure is required to be finite. -/
theorem equal_mass_decompositions (hp : 0 < p) (hp1 : p < 1) (hμ : Nonatomic μ) :
    EqualMassDecompositions (𝕜 := 𝕜) p μ := by
  intro f n hn
  let ν := μ.withDensity (fun x => ‖f x‖ₑ ^ p.toReal)
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity (lp_weight_lt_top p μ hp hp1 f).ne
  have hν : Nonatomic ν := nonatomic_lp_weight p μ hp hp1 hμ f
  obtain ⟨s, hs, hdisj, hcover, hmass⟩ := equal_finite_partition_of_divisibility
    (μ := ν) (fun A hA b hb => finite_subset_measure_eq hν hA hb) n hn
  exact decompositions_of_weighted_partition hp hp1 f s hs hdisj hcover
    (fun i => (hmass i).le)

end Partitions

/-- Equal-mass decompositions force every continuous functional to vanish.
Scaling each of the `n` pieces by `n` gives distance of order `n^(p-1)`,
while linearity recovers `n • ℓ f`; continuity contradicts a nonzero `ℓ f`. -/
theorem dual_from_decompositions : NonlocallyConvexSpec.DualFromDecompositions := by
  intro α 𝕜 _ _ μ p hp hp1 hpart m hm ℓ
  have heq := powerMetric_unique hp hp1 m hm
  subst m
  letI := powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1
  letI : Dist (Lp 𝕜 p μ) := (powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1).toDist
  letI : EDist (Lp 𝕜 p μ) := (powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1).toEDist
  apply ContinuousLinearMap.ext
  intro f
  by_contra hf
  have hnorm : 0 < ‖ℓ f‖ := norm_pos_iff.mpr hf
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp
    ℓ.continuous.continuousAt (‖ℓ f‖ / 2) (by positivity)
  have hpR : p.toReal < 1 := by
    have := (ENNReal.toReal_lt_toReal (hp1.trans ENNReal.one_lt_top).ne
      ENNReal.one_ne_top).mpr hp1
    simpa using this
  have hdecay : Tendsto (fun n : ℕ => (n : ℝ) ^ (p.toReal - 1) * powerDist p μ f 0)
      atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (sub_pos.mpr hpR)).comp
      tendsto_natCast_atTop_atTop).mul_const (powerDist p μ f 0)
    simpa only [neg_sub, zero_mul, Function.comp_def] using h
  obtain ⟨n, hn, hb⟩ := ((eventually_gt_atTop (0 : ℕ)).and
    (hdecay.eventually (gt_mem_nhds hδ))).exists
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨g, hsum, hg⟩ := hpart f n hn
  have hpiece (i : Fin n) : ‖ℓ ((n : 𝕜) • g i)‖ < ‖ℓ f‖ / 2 := by
    have hd : dist ((n : 𝕜) • g i) 0 < δ := by
      change powerDist p μ ((n : 𝕜) • g i) 0 < δ
      have he : powerDist p μ ((n : 𝕜) • g i) 0 =
          (n : ℝ) ^ p.toReal * powerDist p μ (g i) 0 := by
        simpa only [smul_zero, RCLike.norm_natCast] using
          powerDist_smul (n : 𝕜) (g i) (0 : Lp 𝕜 p μ)
      rw [he]
      calc
        _ ≤ (n : ℝ) ^ p.toReal * (powerDist p μ f 0 / n) :=
          mul_le_mul_of_nonneg_left (hg i) (Real.rpow_nonneg hnR.le _)
        _ = (n : ℝ) ^ (p.toReal - 1) * powerDist p μ f 0 := by
          rw [Real.rpow_sub_one hnR.ne']
          ring
        _ < δ := hb
    simpa only [map_zero, dist_zero_right] using hsmall hd
  have hsumℓ : (∑ i, ℓ ((n : 𝕜) • g i)) = (n : 𝕜) • ℓ f := by
    rw [← map_sum, ← Finset.smul_sum, hsum, map_smul]
  have hstrict : (n : ℝ) * ‖ℓ f‖ < (n : ℝ) * (‖ℓ f‖ / 2) := by
    calc
      _ = ‖(n : 𝕜) • ℓ f‖ := by rw [norm_smul, RCLike.norm_natCast]
      _ = ‖∑ i, ℓ ((n : 𝕜) • g i)‖ := congrArg norm hsumℓ.symm
      _ ≤ ∑ i, ‖ℓ ((n : 𝕜) • g i)‖ := norm_sum_le _ _
      _ < ∑ _i : Fin n, ‖ℓ f‖ / 2 := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
        · intro i _
          exact hpiece i
      _ = _ := by simp
  nlinarith [mul_pos hnR hnorm]

/-- Once triviality of the dual is supplied, the source's final consequences
follow from accepted Hahn–Banach, with nontriviality needed only here. -/
theorem nonconvex_of_trivialDual : NonlocallyConvexSpec.NonconvexFromTrivialDual := by
  intro hdual α 𝕜 _ _ μ p hp hp1 hμ m hm hnontrivial
  have heq := powerMetric_unique hp hp1 m hm
  subst m
  letI := powerMetric (μ := μ) (𝕜 := 𝕜) hp hp1
  letI := hnontrivial
  have hnot : ¬ LocallyConvexSpace ℝ (Lp 𝕜 p μ) := by
    intro hlc
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Lp 𝕜 p μ)
    obtain ⟨ℓ, hℓ⟩ := continuous_dual_separates_points 𝕜 (Lp 𝕜 p μ)
      ⟨powerMetric_tvs hp hp1, hlc⟩ x y hxy
    have hz := hdual α 𝕜 μ p hp hp1 hμ (powerMetric hp hp1) (fun _ _ => rfl) ℓ
    exact hℓ (by simp only [hz, zero_apply])
  refine ⟨hnot, ?_⟩
  rintro ⟨q, hq⟩
  exact hnot hq.toLocallyConvexSpace

/-- The full unconditional zero-dual assertion on any nonatomic measure space. -/
theorem trivial_dual : NonlocallyConvexSpec.TrivialDual := by
  intro α 𝕜 _ _ μ p hp hp1 hμ
  exact dual_from_decompositions α 𝕜 μ p hp hp1 (equal_mass_decompositions hp hp1 hμ)

/-- A nonzero nonatomic Lp space for 0<p<1 is neither locally convex nor normable. -/
theorem nonconvex_and_nonnormable : NonlocallyConvexSpec.NonconvexAndNonnormable :=
  nonconvex_of_trivialDual trivial_dual

end ExpandedFA.P1.NonlocallyConvex
