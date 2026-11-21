import MathGenome.Internal.RealAnalysis.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.InclusionFailure
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch10.InclusionFailure
open Specs.D11.Ch10.InclusionFailure

/-- Measurability is for the given representatives, not merely a.e. -/
theorem measurable_cutoffPower (𝕂 : Type*) [RCLike 𝕂]
    (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ) :
    Measurable (cutoffPower 𝕂 s a) := by
  exact ((RCLike.measurable_ofReal.comp (measurable_id.pow_const (-a))).indicator hs).comp
    measurable_subtype_coe

/-- Completing the measure does not change membership of a Borel measurable
representative. This explicitly relates the power tests to completed Lebesgue
measure rather than identifying the two sigma-algebras. -/
theorem mem_lebesgueLp_iff (𝕂 : Type*) [RCLike 𝕂] (p : ℝ) (hp : 1 ≤ p)
    (f : PositiveHalfLine → 𝕂) (hf : Measurable f) :
    f ∈ lebesgueLp 𝕂 p ↔
      f ∈ Specs.D11.Ch10.LpDefinition.rawLp_value halfLineVolume p := by
  have hm : (inferInstance : MeasurableSpace PositiveHalfLine) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace PositiveHalfLine halfLineVolume)) :=
    fun _ hs => hs.nullMeasurableSet
  have htrim : halfLineVolume.completion.trim hm = halfLineVolume := by
    refine @Measure.ext PositiveHalfLine (inferInstance : MeasurableSpace PositiveHalfLine)
      _ _ ?_
    intro s hs
    exact (trim_measurableSet_eq hm hs).trans (Measure.completion_apply halfLineVolume s)
  have hf' : @Measurable (NullMeasurableSpace PositiveHalfLine halfLineVolume) 𝕂 _ _ f :=
    hf.nullMeasurable.measurable'
  have hc : f ∈ lebesgueLp 𝕂 p ↔
      MemLp (fun x : NullMeasurableSpace PositiveHalfLine halfLineVolume => f x)
        (ENNReal.ofReal p) halfLineVolume.completion :=
    (LpDefinition.rawLp_iff_memLp halfLineVolume.completion p _ hp).trans (and_iff_right hf')
  have hb : f ∈ Specs.D11.Ch10.LpDefinition.rawLp_value halfLineVolume p ↔
      MemLp f (ENNReal.ofReal p) halfLineVolume :=
    (LpDefinition.rawLp_iff_memLp halfLineVolume p f hp).trans (and_iff_right hf)
  apply hc.trans
  apply Iff.trans ?_ hb.symm
  have hn := eLpNorm_trim (p := ENNReal.ofReal p) (μ := halfLineVolume.completion)
    hm hf.stronglyMeasurable
  rw [htrim] at hn
  exact iff_of_eq (congrArg (fun n : ℝ≥0∞ => n < ∞) hn).symm

/-- The finite-power integral reduces exactly to a real power on the cutoff set. -/
theorem cutoffPower_mem_rawLp_iff (𝕂 : Type*) [RCLike 𝕂]
    (s : Set ℝ) (hs : MeasurableSet s) (hpos : s ⊆ Ioi 0)
    (a p : ℝ) (hp : 1 ≤ p) :
    cutoffPower 𝕂 s a ∈ Specs.D11.Ch10.LpDefinition.rawLp_value halfLineVolume p ↔
      IntegrableOn (fun x : ℝ => x ^ (-a * p)) s := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hm := measurable_cutoffPower 𝕂 s hs a
  rw [LpDefinition.rawLp_iff_memLp _ _ _ hp, and_iff_right hm]
  rw [← integrable_norm_rpow_iff hm.stronglyMeasurable.aestronglyMeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have heq : (fun x : ℝ =>
      ‖s.indicator (fun t : ℝ => ((t ^ (-a) : ℝ) : 𝕂)) x‖ ^ p) =
      s.indicator (fun x : ℝ => x ^ (-a * p)) := by
    funext x
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (hpos hx).le _)]
      exact (Real.rpow_mul (hpos hx).le (-a) p).symm
    · simp [indicator_of_notMem hx, Real.zero_rpow hp0.ne']
  change Integrable ((fun x : ℝ =>
    ‖s.indicator (fun t : ℝ => ((t ^ (-a) : ℝ) : 𝕂)) x‖ ^ p) ∘
      (Subtype.val : PositiveHalfLine → ℝ)) ((volume : Measure ℝ).comap Subtype.val) ↔ _
  rw [← integrableOn_iff_comap_subtypeVal measurableSet_Ioi, heq,
    integrableOn_indicator_iff hs.nullMeasurableSet, inter_eq_left.mpr hpos]

/-- Exact threshold at the origin, including divergence at equality. -/
theorem nearZero_mem_rawLp_iff (𝕂 : Type*) [RCLike 𝕂] (a p : ℝ) (hp : 1 ≤ p) :
    nearZero 𝕂 a ∈ Specs.D11.Ch10.LpDefinition.rawLp_value halfLineVolume p ↔ a * p < 1 := by
  rw [nearZero, cutoffPower_mem_rawLp_iff 𝕂 _ measurableSet_Ioo Ioo_subset_Ioi_self a p hp,
    intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

/-- Exact threshold at infinity, including divergence at equality. -/
theorem atInfinity_mem_rawLp_iff (𝕂 : Type*) [RCLike 𝕂] (b p : ℝ) (hp : 1 ≤ p) :
    atInfinity 𝕂 b ∈ Specs.D11.Ch10.LpDefinition.rawLp_value halfLineVolume p ↔ 1 < b * p := by
  rw [atInfinity, cutoffPower_mem_rawLp_iff 𝕂 _ measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) b p hp, integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

theorem nearZero_separates : Specs.D11.Ch10.InclusionFailure.nearZero_separates := by
  intro 𝕂 _ p q a hp hpq haqa hap
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := hp0.trans hpq
  change _ ∈ lebesgueLp 𝕂 _ ∧ _ ∉ lebesgueLp 𝕂 _
  rw [mem_lebesgueLp_iff 𝕂 p hp _ (measurable_cutoffPower 𝕂 _ measurableSet_Ioo a),
    mem_lebesgueLp_iff 𝕂 q (hp.trans hpq.le) _
      (measurable_cutoffPower 𝕂 _ measurableSet_Ioo a)]
  constructor
  · exact (nearZero_mem_rawLp_iff 𝕂 a p hp).mpr ((lt_div_iff₀ hp0).mp hap)
  · rw [nearZero_mem_rawLp_iff 𝕂 a q (hp.trans hpq.le)]
    exact not_lt.mpr ((div_le_iff₀ hq0).mp haqa)

theorem atInfinity_separates : Specs.D11.Ch10.InclusionFailure.atInfinity_separates := by
  intro 𝕂 _ p q b hp hpq hbq hbp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := hp0.trans hpq
  change _ ∈ lebesgueLp 𝕂 _ ∧ _ ∉ lebesgueLp 𝕂 _
  rw [mem_lebesgueLp_iff 𝕂 q (hp.trans hpq.le) _
      (measurable_cutoffPower 𝕂 _ measurableSet_Ioi b),
    mem_lebesgueLp_iff 𝕂 p hp _ (measurable_cutoffPower 𝕂 _ measurableSet_Ioi b)]
  constructor
  · exact (atInfinity_mem_rawLp_iff 𝕂 b q (hp.trans hpq.le)).mpr
      ((div_lt_iff₀ hq0).mp hbq)
  · rw [atInfinity_mem_rawLp_iff 𝕂 b p hp]
    exact not_lt.mpr ((le_div_iff₀ hp0).mp hbp)

theorem neither_inclusion : Specs.D11.Ch10.InclusionFailure.neither_inclusion := by
  intro 𝕂 _ p q hp hpq
  have hrecip : 1 / q < 1 / p :=
    one_div_lt_one_div_of_lt (lt_of_lt_of_le zero_lt_one hp) hpq
  have hzero := nearZero_separates 𝕂 p q (1 / q) hp hpq le_rfl hrecip
  have hinfty := atInfinity_separates 𝕂 p q (1 / p) hp hpq hrecip le_rfl
  exact ⟨fun h => hzero.2 (h hzero.1), fun h => hinfty.2 (h hinfty.1)⟩

/-- A.e. modifications cannot turn an excluded class into an included one. -/
theorem not_mem_lebesgueLp_of_ae (𝕂 : Type*) [RCLike 𝕂] (p : ℝ) (hp : 1 ≤ p)
    (f g : PositiveHalfLine → 𝕂) (hf : Measurable f) (hnot : f ∉ lebesgueLp 𝕂 p)
    (hfg : f =ᵐ[halfLineVolume] g) : g ∉ lebesgueLp 𝕂 p := by
  intro hg
  have hgm : MemLp (fun x : NullMeasurableSpace PositiveHalfLine halfLineVolume => g x)
      (ENNReal.ofReal p) halfLineVolume.completion :=
    ((LpDefinition.rawLp_iff_memLp halfLineVolume.completion p _ hp).mp hg).2
  have hfg' : (fun x : NullMeasurableSpace PositiveHalfLine halfLineVolume => f x)
      =ᵐ[halfLineVolume.completion] (fun x => g x) := hfg
  have hfm := hgm.ae_eq hfg'.symm
  have hf' : @Measurable (NullMeasurableSpace PositiveHalfLine halfLineVolume) 𝕂 _ _ f :=
    hf.nullMeasurable.measurable'
  exact hnot ((LpDefinition.rawLp_iff_memLp halfLineVolume.completion p _ hp).mpr ⟨hf', hfm⟩)

theorem ordinary_ae_class_separation :
    Specs.D11.Ch10.InclusionFailure.ordinary_ae_class_separation := by
  intro 𝕂 _ p q a b hp hpq haq hap hbq hbp
  constructor
  · intro g hfg
    exact not_mem_lebesgueLp_of_ae 𝕂 q (hp.trans hpq.le) _ g
      (measurable_cutoffPower 𝕂 _ measurableSet_Ioo a)
      (nearZero_separates 𝕂 p q a hp hpq haq hap).2 hfg
  · intro g hfg
    exact not_mem_lebesgueLp_of_ae 𝕂 p hp _ g
      (measurable_cutoffPower 𝕂 _ measurableSet_Ioi b)
      (atInfinity_separates 𝕂 p q b hp hpq hbq hbp).2 hfg

end D11.Ch10.InclusionFailure
