import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.GrothendieckBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.FspaceOpenGraph
import Mathlib.Topology.MetricSpace.Snowflaking

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

universe u
namespace ExpandedFA.PartIV.GrothendieckBound

/-- The metric used below really is the integral metric in the fractional range. -/
theorem fractional_metric : Spec.FractionalMetric.{u} := by
  intro X _ 𝕜 _ μ p hp hp1
  letI := lpNormedGroup (V := 𝕜) p hp μ
  intro f g
  change (lpMass p μ (-f + g)).toReal = _
  rw [neg_add_eq_sub]
  rw [lpMass_eq_inhmg hp, inhmgELpNorm_eq_lintegral hp1.le hp.ne'
    (Lp.aestronglyMeasurable (g - f))]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub g f] with x hx
  rw [hx]
  simp only [Pi.sub_apply, enorm_sub_rev]

private abbrev SnowScalar (𝕜 : Type*) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :=
  Metric.Snowflaking 𝕜 r hr hr1

private instance snowAddCommGroup (𝕜 : Type*) [AddCommGroup 𝕜]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : AddCommGroup (SnowScalar 𝕜 r hr hr1) :=
  Metric.Snowflaking.ofSnowflaking.addCommGroup

private instance snowNormedGroup (𝕜 : Type*) [NormedAddCommGroup 𝕜]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : NormedAddCommGroup (SnowScalar 𝕜 r hr hr1) where
  norm x := ‖x.val‖ ^ r
  dist_eq x y := by
    change dist x.val y.val ^ r = ‖-x.val + y.val‖ ^ r
    rw [dist_eq_norm', neg_add_eq_sub]

private instance snowComplete (𝕜 : Type*) [NormedAddCommGroup 𝕜] [CompleteSpace 𝕜]
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) : CompleteSpace (SnowScalar 𝕜 r hr hr1) :=
  Metric.Snowflaking.uniformEquiv.completeSpace_iff.mpr inferInstance

private lemma snow_enorm {𝕜 : Type*} [NormedAddCommGroup 𝕜]
    {r : ℝ} {hr : 0 < r} {hr1 : r ≤ 1} (z : 𝕜) :
    ‖(Metric.Snowflaking.toSnowflaking z : SnowScalar 𝕜 r hr hr1)‖ₑ = ‖z‖ₑ ^ r := by
  rw [← ofReal_norm, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hr.le]
  rfl

private lemma fractionalExponent_pos {p : ℝ≥0∞} (hp : 0 < p) (hp1 : p ≤ 1) :
    0 < p.toReal := ENNReal.toReal_pos hp.ne' (hp1.trans_lt ENNReal.one_lt_top).ne

private lemma fractionalExponent_le_one {p : ℝ≥0∞} (hp1 : p ≤ 1) : p.toReal ≤ 1 := by
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hp1

private abbrev SnowLpScalar (𝕜 : Type*) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1) :=
  SnowScalar 𝕜 p.toReal (fractionalExponent_pos hp hp1) (fractionalExponent_le_one hp1)

private lemma snow_eLpNorm {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1)
    {f : X → 𝕜} (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => (Metric.Snowflaking.toSnowflaking (f x) :
      SnowLpScalar 𝕜 p hp hp1)) 1 μ =
      eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (Metric.Snowflaking.continuous_toSnowflaking.comp_aestronglyMeasurable hf)]
  simp_rw [snow_enorm]
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm'
    (ENNReal.toReal_pos hp.ne' (hp1.trans_lt ENNReal.one_lt_top).ne),
    eLpNorm_eq_eLpNorm' hp.ne' (hp1.trans_lt ENNReal.one_lt_top).ne hf]

private lemma memLp_snow_iff {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1) (f : X → 𝕜) :
    MemLp (fun x => (Metric.Snowflaking.toSnowflaking (f x) :
      SnowLpScalar 𝕜 p hp hp1)) 1 μ ↔ MemLp f p μ := by
  constructor
  · intro h
    have hf : AEStronglyMeasurable f μ :=
      Metric.Snowflaking.continuous_ofSnowflaking.comp_aestronglyMeasurable
        h.aestronglyMeasurable
    have hfin := h.eLpNorm_lt_top
    rw [snow_eLpNorm μ p hp hp1 hf] at hfin
    exact (ENNReal.rpow_lt_top_iff_of_pos (fractionalExponent_pos hp hp1)).mp hfin
  · intro h
    change eLpNorm _ 1 μ < ∞
    rw [snow_eLpNorm μ p hp hp1 h.aestronglyMeasurable]
    exact (ENNReal.rpow_lt_top_iff_of_pos (fractionalExponent_pos hp hp1)).mpr h.eLpNorm_lt_top

private def toSnowLp {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1) (f : Lp 𝕜 p μ) :
    Lp (SnowLpScalar 𝕜 p hp hp1) 1 μ :=
  ((memLp_snow_iff μ p hp hp1 f).mpr (Lp.memLp f)).toLp
    (fun x => Metric.Snowflaking.toSnowflaking (f x))

private lemma coe_toSnowLp {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1) (f : Lp 𝕜 p μ) :
    ⇑(toSnowLp μ p hp hp1 f) =ᵐ[μ] fun x => Metric.Snowflaking.toSnowflaking (f x) :=
  MemLp.coeFn_toLp _

private def fromSnowLp {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1)
    (f : Lp (SnowLpScalar 𝕜 p hp hp1) 1 μ) : Lp 𝕜 p μ :=
  ((memLp_snow_iff μ p hp hp1 (fun x => (f x).val)).mp (Lp.memLp f)).toLp
    (fun x => (f x).val)

private lemma coe_fromSnowLp {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1)
    (f : Lp (SnowLpScalar 𝕜 p hp hp1) 1 μ) :
    ⇑(fromSnowLp μ p hp hp1 f) =ᵐ[μ] fun x => (f x).val := MemLp.coeFn_toLp _

private def snowLpEquiv {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p ≤ 1) :
    Lp 𝕜 p μ ≃ Lp (SnowLpScalar 𝕜 p hp hp1) 1 μ where
  toFun := toSnowLp μ p hp hp1
  invFun := fromSnowLp μ p hp hp1
  left_inv f := by
    apply Lp.ext
    filter_upwards [coe_fromSnowLp μ p hp hp1 (toSnowLp μ p hp hp1 f),
      coe_toSnowLp μ p hp hp1 f] with x h₁ h₂
    rw [h₁, h₂]
    rfl
  right_inv f := by
    apply Lp.ext
    filter_upwards [coe_toSnowLp μ p hp hp1 (fromSnowLp μ p hp hp1 f),
      coe_fromSnowLp μ p hp hp1 f] with x h₁ h₂
    rw [h₁, h₂]
    rfl

private def snowLpIsometryEquiv {X 𝕜 : Type*} [MeasurableSpace X] [NormedAddCommGroup 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (hp1 : p < 1) :
    letI := lpNormedGroup (V := 𝕜) p hp μ
    Lp 𝕜 p μ ≃ᵢ Lp (SnowLpScalar 𝕜 p hp hp1.le) 1 μ := by
  letI := lpNormedGroup (V := 𝕜) p hp μ
  refine ⟨snowLpEquiv μ p hp hp1.le, Isometry.of_dist_eq fun f g => ?_⟩
  simp only [Lp.dist_eq_eLpNorm_neg_add]
  change (eLpNorm (-⇑(toSnowLp μ p hp hp1.le f) +
    ⇑(toSnowLp μ p hp hp1.le g)) 1 μ).toReal =
    (lpMass p μ (-f + g)).toReal
  have heq : (-⇑(toSnowLp μ p hp hp1.le f) + ⇑(toSnowLp μ p hp hp1.le g)) =ᵐ[μ]
      fun x => Metric.Snowflaking.toSnowflaking ((-f + g) x) := by
    filter_upwards [coe_toSnowLp μ p hp hp1.le f, coe_toSnowLp μ p hp hp1.le g,
      Lp.coeFn_add (-f) g, Lp.coeFn_neg f] with x h₁ h₂ h₃ h₄
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [h₁, h₂, h₃, Pi.add_apply, h₄]
    rfl
  rw [eLpNorm_congr_ae heq, snow_eLpNorm μ p hp hp1.le (Lp.aestronglyMeasurable (-f + g))]
  congr 1
  unfold lpMass metricExponent
  rw [ite_eq_left hp1]

/-- In the Banach range the canonical metric agrees with the existing Lp
metric, so closedness is exactly the usual Lp closedness. -/
lemma lpMetric_eq_native {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 0 < p) :
    (lpNormedGroup (V := 𝕜) p hp μ).toMetricSpace =
      (inferInstance : MetricSpace (Lp 𝕜 p μ)) := by
  apply MetricSpace.ext
  apply Dist.ext
  funext f g
  simp only [Lp.dist_eq_eLpNorm_neg_add]
  change (lpMass p μ (-f + g)).toReal = (eLpNorm (-⇑f + ⇑g) p μ).toReal
  unfold lpMass metricExponent
  rw [ite_eq_right (not_lt_of_ge (Fact.out : 1 ≤ p)), ENNReal.rpow_one]
  congr 1
  rw [eLpNorm_congr_ae (Lp.coeFn_add (-f) g)]
  rw [eLpNorm_congr_ae ((Lp.coeFn_neg f).add Filter.EventuallyEq.rfl)]

/-- Completeness below one is obtained by the isometry onto L¹ with scalar
metric |z-w|^p; completeness of that scalar metric follows from its unchanged
uniformity. This is valid on arbitrary measures. -/
theorem positiveLp_complete : Spec.PositiveLpComplete.{u} := by
  intro X _ 𝕜 _ μ p hp
  by_cases hp1 : p < 1
  · letI := lpNormedGroup (V := 𝕜) p hp μ
    exact (snowLpIsometryEquiv μ p hp hp1).completeSpace_iff.mpr inferInstance
  · have hpge : 1 ≤ p := le_of_not_gt hp1
    letI : Fact (1 ≤ p) := ⟨hpge⟩
    let original : NormedAddCommGroup (Lp 𝕜 p μ) := inferInstance
    have hc : @CompleteSpace (Lp 𝕜 p μ) original.toUniformSpace := inferInstance
    have hm : (lpNormedGroup (V := 𝕜) p hp μ).toMetricSpace = original.toMetricSpace :=
      lpMetric_eq_native μ p hp
    change @CompleteSpace (Lp 𝕜 p μ) (lpNormedGroup p hp μ).toUniformSpace
    have hu := congrArg (fun m : MetricSpace (Lp 𝕜 p μ) => m.toUniformSpace) hm
    rw [hu]
    exact hc

lemma lpMass_smul {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (c : 𝕜) (f : Lp 𝕜 p μ) :
    (lpMass p μ (c • f)).toReal = ‖c‖ ^ metricExponent p * (lpMass p μ f).toReal := by
  unfold lpMass
  rw [eLpNorm_congr_ae (Lp.coeFn_smul c f), eLpNorm_const_smul,
    ENNReal.mul_rpow_of_nonneg _ _ (metricExponent_pos hp).le, ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, toReal_enorm]

lemma tendsto_zero_iff_lpMass {X 𝕜 ι : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) (f : ι → Lp 𝕜 p μ) (l : Filter ι) :
    letI := lpNormedGroup (V := 𝕜) p hp μ
    Tendsto f l (𝓝 0) ↔ Tendsto (fun i => (lpMass p μ (f i)).toReal) l (𝓝 0) :=
  @tendsto_zero_iff_norm_tendsto_zero ι (Lp 𝕜 p μ)
    (@NormedAddGroup.toSeminormedAddGroup _
      (@NormedAddCommGroup.toNormedAddGroup _ (lpNormedGroup (V := 𝕜) p hp μ))) f l

lemma positiveLp_continuousSMul {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (hp : 0 < p) :
    letI := lpNormedGroup (V := 𝕜) p hp μ
    ContinuousSMul 𝕜 (Lp 𝕜 p μ) := by
  letI := lpNormedGroup (V := 𝕜) p hp μ
  have hs : Continuous (fun f : Lp 𝕜 p μ => (lpMass p μ f).toReal) :=
    @continuous_norm (Lp 𝕜 p μ) (@NormedAddGroup.toSeminormedAddGroup _
      (@NormedAddCommGroup.toNormedAddGroup _ (lpNormedGroup (V := 𝕜) p hp μ)))
  have hc : Continuous (fun c : 𝕜 => ‖c‖ ^ metricExponent p) :=
    (Real.continuous_rpow_const (metricExponent_pos hp).le).comp continuous_norm
  have hs0 : (lpMass p μ (0 : Lp 𝕜 p μ)).toReal = 0 := (map_zero (lpGroupNorm (V := 𝕜) p hp μ))
  have hc0 : ‖(0 : 𝕜)‖ ^ metricExponent p = 0 := by
    rw [norm_zero, Real.zero_rpow (metricExponent_pos hp).ne']
  letI : IsTopologicalAddGroup (Lp 𝕜 p μ) :=
    @SeminormedAddCommGroup.toIsTopologicalAddGroup _
      (lpNormedGroup (V := 𝕜) p hp μ).toSeminormedAddCommGroup
  apply ContinuousSMul.of_nhds_zero
  · rw [tendsto_zero_iff_lpMass]
    simp_rw [lpMass_smul μ p hp]
    simpa only [hc0, hs0, mul_zero, Function.comp_def] using
      ((hc.tendsto 0).comp tendsto_fst).mul ((hs.tendsto 0).comp tendsto_snd)
  · intro f
    rw [tendsto_zero_iff_lpMass]
    simp_rw [lpMass_smul μ p hp]
    convert (hc.tendsto 0).mul_const (lpMass p μ f).toReal using 1
    rw [hc0, zero_mul]
  · intro c
    rw [tendsto_zero_iff_lpMass]
    simp_rw [lpMass_smul μ p hp]
    convert (hs.tendsto 0).const_mul (‖c‖ ^ metricExponent p) using 1
    rw [hs0, mul_zero]

/-- Joint scalar continuity, metrizability and completeness for the canonical
translation uniformity. No local convexity is used. -/
theorem positiveLp_fspace : Spec.PositiveLpFSpace.{u} := by
  intro X _ 𝕜 _ μ p hp
  letI := lpNormedGroup (V := 𝕜) p hp μ
  letI : IsTopologicalAddGroup (Lp 𝕜 p μ) :=
    @SeminormedAddCommGroup.toIsTopologicalAddGroup _
      (lpNormedGroup (V := 𝕜) p hp μ).toSeminormedAddCommGroup
  letI := positiveLp_continuousSMul (𝕜 := 𝕜) μ p hp
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  change @CompleteSpace (Lp 𝕜 p μ) (IsTopologicalAddGroup.rightUniformSpace _)
  letI : IsUniformAddGroup (Lp 𝕜 p μ) :=
    @SeminormedAddCommGroup.to_isUniformAddGroup _
      (lpNormedGroup (V := 𝕜) p hp μ).toSeminormedAddCommGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact positiveLp_complete X 𝕜 μ p hp

/-- The finite-measure inclusion of a.e. classes is an actual scalar-linear map. -/
def infinityToLp {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) : Lp 𝕜 ∞ μ →ₗ[𝕜] Lp 𝕜 p μ where
  toFun f := ⟨f.val, Lp.antitone le_top f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma infinityToLp_injective {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    Function.Injective (infinityToLp (𝕜 := 𝕜) μ p) := by
  intro f g h
  exact Subtype.ext (congrArg (fun z : Lp 𝕜 p μ => z.val) h)

lemma infinityToLp_continuous {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hp : 0 < p) :
    letI := lpNormedGroup (V := 𝕜) ∞ (by simp) μ
    letI := lpNormedGroup (V := 𝕜) p hp μ
    Continuous (infinityToLp (𝕜 := 𝕜) μ p) := by
  letI := lpNormedGroup (V := 𝕜) ∞ (by simp) μ
  letI := lpNormedGroup (V := 𝕜) p hp μ
  letI : IsTopologicalAddGroup (Lp 𝕜 ∞ μ) :=
    @SeminormedAddCommGroup.toIsTopologicalAddGroup _
      (lpNormedGroup (V := 𝕜) ∞ (by simp) μ).toSeminormedAddCommGroup
  letI : ContinuousAdd (Lp 𝕜 p μ) :=
    (@SeminormedAddCommGroup.toIsTopologicalAddGroup _
      (lpNormedGroup (V := 𝕜) p hp μ).toSeminormedAddCommGroup).toContinuousAdd
  apply continuous_of_continuousAt_zero (infinityToLp (𝕜 := 𝕜) μ p)
  change Tendsto _ (𝓝 0) (𝓝 0)
  rw [tendsto_zero_iff_lpMass]
  have hq : Tendsto (fun f : Lp 𝕜 ∞ μ => (eLpNorm f ∞ μ).toReal) (𝓝 0) (𝓝 0) := by
    have h := (tendsto_zero_iff_lpMass (𝕜 := 𝕜) μ ∞ (by simp) id (𝓝 0)).mp tendsto_id
    simpa [lpMass, metricExponent] using h
  let M : ℝ≥0∞ := μ Set.univ ^ (1 / p.toReal)
  have hM : M ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top μ _)
  have hbound (f : Lp 𝕜 ∞ μ) :
      (lpMass p μ (infinityToLp μ p f)).toReal ≤
        ((eLpNorm f ∞ μ).toReal * M.toReal) ^ metricExponent p := by
    rw [lpMass, ← ENNReal.toReal_rpow]
    apply Real.rpow_le_rpow ENNReal.toReal_nonneg _ (metricExponent_pos hp).le
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := ⇑f) (p := p) le_top
      (Lp.aestronglyMeasurable f)
    simp only [ENNReal.toReal_top, div_zero, sub_zero] at h
    exact (ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hM) h).trans_eq
      ENNReal.toReal_mul
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) hbound
  have h := (Real.continuous_rpow_const (metricExponent_pos hp).le).tendsto 0
  simpa only [Real.zero_rpow (metricExponent_pos hp).ne', zero_mul, Function.comp_def] using
    h.comp (by simpa only [zero_mul] using hq.mul_const M.toReal)

/-- Reinterpret each essentially bounded a.e. class at exponent infinity. -/
def liftToInfinity {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (E : Submodule 𝕜 (Lp 𝕜 p μ))
    (hInf : ∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ) : E →ₗ[𝕜] Lp 𝕜 ∞ μ where
  toFun f := ⟨f.val.val, hInf f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma liftToInfinity_continuous {X : Type u} {𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hp : 0 < p) :
    letI := lpNormedGroup (V := 𝕜) ∞ (by simp) μ
    letI := lpNormedGroup (V := 𝕜) p hp μ
    ∀ (E : Submodule 𝕜 (Lp 𝕜 p μ)), IsClosed (E : Set (Lp 𝕜 p μ)) →
      ∀ hInf : ∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ,
        Continuous (liftToInfinity μ p E hInf) := by
  letI := lpNormedGroup (V := 𝕜) ∞ (by simp) μ
  letI := lpNormedGroup (V := 𝕜) p hp μ
  letI : IsTopologicalAddGroup (Lp 𝕜 p μ) :=
    @SeminormedAddCommGroup.toIsTopologicalAddGroup _
      (lpNormedGroup (V := 𝕜) p hp μ).toSeminormedAddCommGroup
  letI : IsUniformAddGroup (Lp 𝕜 p μ) :=
    @SeminormedAddCommGroup.to_isUniformAddGroup _
      (lpNormedGroup (V := 𝕜) p hp μ).toSeminormedAddCommGroup
  letI := positiveLp_continuousSMul (𝕜 := 𝕜) μ p hp
  letI := positiveLp_complete X 𝕜 μ p hp
  intro E hE hInf
  letI : IsUniformAddGroup E := inferInstanceAs (IsUniformAddGroup E.toAddSubgroup)
  have hEF : ExpandedFA.P1.FSpace 𝕜 E := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    change @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact hE.isComplete.completeSpace_coe
  apply ExpandedFA.P1.FspaceOpenGraph.closed_graph 𝕜 E (Lp 𝕜 ∞ μ) hEF
    (positiveLp_fspace X 𝕜 μ ∞ (by simp)) (liftToInfinity μ p E hInf)
  have hg : IsClosed {z : E × Lp 𝕜 ∞ μ | infinityToLp μ p z.2 = z.1.val} :=
    isClosed_eq ((infinityToLp_continuous μ p hp).comp continuous_snd)
      (continuous_subtype_val.comp continuous_fst)
  convert hg using 1
  ext z
  change z.2 = liftToInfinity μ p E hInf z.1 ↔ infinityToLp μ p z.2 = z.1.val
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply infinityToLp_injective μ p
    exact h

lemma lpMass_toReal {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (μ : Measure X) (p : ℝ≥0∞) (f : Lp V p μ) :
    (lpMass p μ f).toReal = (eLpNorm f p μ).toReal ^ metricExponent p :=
  (ENNReal.toReal_rpow _ _).symm

/-- A continuous linear inclusion is bounded in the homogeneous Lp quasi-norm,
including when the translation metric has degree p rather than one. -/
lemma infinity_bound {X : Type u} {𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] (p : ℝ≥0∞) (hp : 0 < p) :
    letI := lpNormedGroup (V := 𝕜) p hp μ
    ∀ (E : Submodule 𝕜 (Lp 𝕜 p μ)), IsClosed (E : Set (Lp 𝕜 p μ)) →
      ∀ hInf : ∀ f : E, MemLp (f : Lp 𝕜 p μ) ∞ μ,
      ∃ C : ℝ, 0 < C ∧ ∀ f : E,
        (eLpNorm (f : Lp 𝕜 p μ) ∞ μ).toReal ≤
        C * (eLpNorm (f : Lp 𝕜 p μ) p μ).toReal := by
  letI := lpNormedGroup (V := 𝕜) ∞ (by simp) μ
  letI := lpNormedGroup (V := 𝕜) p hp μ
  intro E hE hInf
  let T := liftToInfinity μ p E hInf
  have hT : Continuous T := liftToInfinity_continuous μ p hp E hE hInf
  have hS : Continuous (fun f : E => (eLpNorm (T f) ∞ μ).toReal) := by
    have hc := @continuous_norm (Lp 𝕜 ∞ μ)
      (@NormedAddGroup.toSeminormedAddGroup _
        (@NormedAddCommGroup.toNormedAddGroup _ (lpNormedGroup (V := 𝕜) ∞ (by simp) μ)))
    have hc' : Continuous (fun f : Lp 𝕜 ∞ μ => (eLpNorm f ∞ μ).toReal) := by
      change Continuous (fun f : Lp 𝕜 ∞ μ => (lpMass ∞ μ f).toReal) at hc
      simpa [lpMass, metricExponent] using hc
    exact hc'.comp hT
  have hn : {f : E | (eLpNorm (T f) ∞ μ).toReal < 1} ∈ 𝓝 (0 : E) := by
    apply (isOpen_Iio.preimage hS).mem_nhds
    change (eLpNorm (T 0) ∞ μ).toReal < 1
    rw [map_zero, eLpNorm_congr_ae (Lp.coeFn_zero 𝕜 ∞ μ), eLpNorm_zero]
    norm_num
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hn
  let s : ℝ := (δ / 2) ^ (metricExponent p)⁻¹
  have hs : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  have hspow : s ^ metricExponent p = δ / 2 := by
    exact Real.rpow_inv_rpow (by positivity) (metricExponent_pos hp).ne'
  refine ⟨s⁻¹, inv_pos.mpr hs, ?_⟩
  intro f
  let q : ℝ := (eLpNorm (f : Lp 𝕜 p μ) p μ).toReal
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  by_cases hq : q = 0
  · have hfp : eLpNorm (f : Lp 𝕜 p μ) p μ = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mp hq |>.resolve_right (Lp.eLpNorm_ne_top f.val)
    have hf : f = 0 := by
      apply Subtype.ext
      exact Lp.eq_zero_iff_ae_eq_zero.mpr ((eLpNorm_eq_zero_iff hp.ne').mp hfp)
    subst f
    change (eLpNorm (0 : Lp 𝕜 p μ) ∞ μ).toReal ≤ s⁻¹ * (eLpNorm (0 : Lp 𝕜 p μ) p μ).toReal
    rw [eLpNorm_congr_ae (Lp.coeFn_zero 𝕜 p μ), eLpNorm_zero,
      eLpNorm_congr_ae (Lp.coeFn_zero 𝕜 p μ), eLpNorm_zero]
    simp
  have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
  let c : 𝕜 := RCLike.ofReal (s / q)
  have hc : ‖c‖ = s / q := by
    simp only [c, RCLike.norm_ofReal, abs_of_pos (div_pos hs hqpos)]
  have hd (g : E) : dist g 0 = (lpMass p μ (g : Lp 𝕜 p μ)).toReal := by
    change (lpMass p μ (-g.val + 0)).toReal = _
    simp only [add_zero, lpMass, eLpNorm_congr_ae (Lp.coeFn_neg g.val), eLpNorm_neg]
  have hnorm : (lpMass p μ ((c • f : E) : Lp 𝕜 p μ)).toReal = δ / 2 := by
    rw [lpMass_toReal]
    have hscale : (eLpNorm ((c • f : E) : Lp 𝕜 p μ) p μ).toReal = s := by
      change (eLpNorm (c • f.val) p μ).toReal = s
      rw [eLpNorm_congr_ae (Lp.coeFn_smul c f.val), eLpNorm_const_smul,
        ENNReal.toReal_mul, toReal_enorm, hc]
      exact div_mul_cancel₀ s hq
    rw [hscale, hspow]
  have hb := hδ (show c • f ∈ Metric.ball (0 : E) δ by
    rw [Metric.mem_ball, hd, hnorm]
    linarith)
  change (eLpNorm (T (c • f)) ∞ μ).toReal < 1 at hb
  rw [map_smul] at hb
  rw [eLpNorm_congr_ae (Lp.coeFn_smul c (T f)), eLpNorm_const_smul,
    ENNReal.toReal_mul, toReal_enorm, hc] at hb
  have hi : (eLpNorm (T f) ∞ μ).toReal ≤ s⁻¹ * q := by
    rw [mul_comm s⁻¹ q, ← div_eq_mul_inv]
    apply le_of_lt
    apply (lt_div_iff₀ hs).mpr
    have hb' : s * (eLpNorm (T f) ∞ μ).toReal / q < 1 := by
      simpa only [div_mul_eq_mul_div] using hb
    have := (div_lt_iff₀ hqpos).mp hb'
    nlinarith
  exact hi

/-- The elementary interpolation estimate, with all norms kept as finite real
values only after essential boundedness has supplied finiteness. -/
lemma lpNorm_power_le_infinity_mul_two {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] (μ : Measure X) (p : ℝ≥0∞) (hp : 2 < p) (hpt : p < ∞)
    (f : X → V) (hInf : MemLp f ∞ μ) (h₂ : MemLp f 2 μ) :
    (eLpNorm f p μ).toReal ^ p.toReal ≤
      (eLpNorm f ∞ μ).toReal ^ (p.toReal - 2) * (eLpNorm f 2 μ).toReal ^ (2 : ℕ) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp)
  have hpr : 2 < p.toReal := by
    have := ENNReal.toReal_lt_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hpt.ne
    simpa only [ENNReal.toReal_ofNat] using this.mpr hp
  have hpow (q : ℝ≥0∞) (hq : 0 < q) (hqt : q < ∞) :
      eLpNorm f q μ ^ q.toReal = ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ := by
    rw [eLpNorm_eq_eLpNorm' hq.ne' hqt.ne hInf.aestronglyMeasurable,
      lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hq.ne' hqt.ne)]
  have hbound : eLpNorm f p μ ^ p.toReal ≤
      eLpNorm f ∞ μ ^ (p.toReal - 2) * eLpNorm f 2 μ ^ (2 : ℝ) := by
    rw [hpow p (by positivity) hpt]
    have hpow₂ := hpow 2 (by norm_num) (by norm_num)
    simp only [ENNReal.toReal_ofNat] at hpow₂
    rw [hpow₂]
    calc
      (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≤
          ∫⁻ x, eLpNorm f ∞ μ ^ (p.toReal - 2) * ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
        apply lintegral_mono_ae
        have ha : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ eLpNorm f ∞ μ := by
          rw [eLpNorm_exponent_top hInf.aestronglyMeasurable]
          exact ae_le_eLpNormEssSup
        filter_upwards [ha] with x hx
        have he : p.toReal = (p.toReal - 2) + 2 := by ring
        nth_rw 1 [he]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)]
        exact mul_le_mul_left (ENNReal.rpow_le_rpow hx (by linarith)) _
      _ = _ := lintegral_const_mul' _ _
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) hInf.eLpNorm_ne_top)
  have hfin : eLpNorm f ∞ μ ^ (p.toReal - 2) * eLpNorm f 2 μ ^ (2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hInf.eLpNorm_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) h₂.eLpNorm_ne_top)
  have h := ENNReal.toReal_mono hfin hbound
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.rpow_two] using h

private lemma real_interpolation {i q n C r : ℝ} (hi : 0 ≤ i) (hq : 0 ≤ q)
    (hn : 0 ≤ n) (hC : 0 < C) (hr : 2 < r) (hb : i ≤ C * q)
    (hp : q ^ r ≤ i ^ (r - 2) * n ^ 2) : i ≤ C ^ (r / 2) * n := by
  by_cases hi0 : i = 0
  · rw [hi0]
    positivity
  have hip : 0 < i := lt_of_le_of_ne hi (Ne.symm hi0)
  have hpow : i ^ r ≤ C ^ r * (i ^ (r - 2) * n ^ 2) := calc
    i ^ r ≤ (C * q) ^ r := Real.rpow_le_rpow hi hb (by linarith)
    _ = C ^ r * q ^ r := Real.mul_rpow hC.le hq
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hC.le _)
  have hsq : i ^ 2 ≤ C ^ r * n ^ 2 := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hip (r - 2))).mp
    calc
      i ^ (r - 2) * i ^ (2 : ℕ) = i ^ r := by
        rw [← Real.rpow_two, ← Real.rpow_add hip]
        congr 1
        ring
      _ ≤ _ := hpow
      _ = _ := by ring
  have hA : (C ^ (r / 2)) ^ (2 : ℕ) = C ^ r := by
    rw [← Real.rpow_two, ← Real.rpow_mul hC.le]
    congr 1
    ring
  have hAn : 0 ≤ C ^ (r / 2) * n := by positivity
  nlinarith [sq_nonneg (i - C ^ (r / 2) * n)]

/-- Both uniform norm comparisons on the original closed subspace. -/
theorem norm_bounds : Spec.NormBounds.{u} := by
  intro X _ 𝕜 _ μ _ p hp hpt
  letI := lpNormedGroup (V := 𝕜) p hp μ
  intro E hE hInf
  obtain ⟨C, hC, hbound⟩ := infinity_bound μ p hp E hE hInf
  have h₂ (f : E) : MemLp (f : Lp 𝕜 p μ) 2 μ := (hInf f).mono_exponent le_top
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp.ne' hpt.ne
  by_cases hp2 : p ≤ 2
  · have hpr2 : p.toReal ≤ 2 := by
      simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hp2
    have hex : 0 ≤ 1 / p.toReal - 1 / 2 := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hpr hpr2)
    let M : ℝ≥0∞ := μ Set.univ ^ (1 / p.toReal - 1 / 2)
    have hM : M ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hex (measure_ne_top μ _)
    refine ⟨C, C * M.toReal + 1, hC, by positivity, hbound, ?_⟩
    intro f
    refine ⟨h₂ f, (hbound f).trans ?_⟩
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp2 (Lp.aestronglyMeasurable f.val)
    have h' : (eLpNorm (f : Lp 𝕜 p μ) p μ).toReal ≤
        (eLpNorm (f : Lp 𝕜 p μ) 2 μ).toReal * M.toReal := by
      have hfin : eLpNorm (f : Lp 𝕜 p μ) 2 μ * M ≠ ∞ :=
        ENNReal.mul_ne_top (h₂ f).eLpNorm_ne_top hM
      have hh := ENNReal.toReal_mono hfin (by
        simpa only [ENNReal.toReal_ofNat] using h)
      simpa only [ENNReal.toReal_mul] using hh
    calc
      C * (eLpNorm (f : Lp 𝕜 p μ) p μ).toReal ≤
          C * ((eLpNorm (f : Lp 𝕜 p μ) 2 μ).toReal * M.toReal) :=
        mul_le_mul_of_nonneg_left h' hC.le
      _ = (C * M.toReal) * (eLpNorm (f : Lp 𝕜 p μ) 2 μ).toReal := by ring
      _ ≤ _ := by nlinarith [ENNReal.toReal_nonneg (a := eLpNorm (f : Lp 𝕜 p μ) 2 μ)]
  · have hp2' : 2 < p := lt_of_not_ge hp2
    have hpr2 : 2 < p.toReal := by
      simpa only [ENNReal.toReal_ofNat] using
        (ENNReal.toReal_lt_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hpt.ne).mpr hp2'
    refine ⟨C, C ^ (p.toReal / 2), hC, Real.rpow_pos_of_pos hC _, hbound, ?_⟩
    intro f
    refine ⟨h₂ f, ?_⟩
    exact real_interpolation ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg hC hpr2 (hbound f)
      (lpNorm_power_le_infinity_mul_two μ p hp2' hpt f.val (hInf f) (h₂ f))

end ExpandedFA.PartIV.GrothendieckBound
