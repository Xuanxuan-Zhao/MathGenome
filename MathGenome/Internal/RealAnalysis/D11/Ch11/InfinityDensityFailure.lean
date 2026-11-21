import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.InfinityDensityFailure
import MathGenome.Internal.RealAnalysis.D11.Ch04.EssentialBounds
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace D11.Ch11.InfinityDensityFailure
open D11.Ch04.EssentialBounds D11.Ch04.AeCommonException

/-- Completion preserves the ordinary a.e. filter, also after restriction
    to a Borel set. -/
private lemma ae_restrict_completion (s : Set ℝ) (hs : MeasurableSet s) :
    ae ((volume : Measure ℝ).completion.restrict s) =
      ae ((volume : Measure ℝ).restrict s) := by
  apply Filter.ext
  intro p
  have hs' : @MeasurableSet (NullMeasurableSpace ℝ volume) _ s := hs.nullMeasurableSet
  exact (ae_restrict_iff' (μ := (volume : Measure ℝ).completion)
    (p := fun x : ℝ => x ∈ p) hs').trans
      (ae_restrict_iff' (μ := (volume : Measure ℝ)) hs).symm

private lemma norm_restrict_completion (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) :
    essentialSupNorm ((volume : Measure ℝ).completion.restrict s) f =
      essentialSupNorm ((volume : Measure ℝ).restrict s) f := by
  calc
    _ = essSup (fun x : ℝ => ‖f x‖ₑ) ((volume : Measure ℝ).completion.restrict s) :=
      essentialSupNorm_eq_native ((volume : Measure ℝ).completion.restrict s) f
    _ = essSup (fun x : ℝ => ‖f x‖ₑ) ((volume : Measure ℝ).restrict s) :=
      congrArg (fun F : Filter ℝ => F.limsup (fun x => ‖f x‖ₑ))
        (ae_restrict_completion s hs)
    _ = _ := (essentialSupNorm_eq_native _ f).symm

/-- A continuous function cannot obey incompatible essential bounds on the
    two sides of the midpoint. -/
lemma midpoint_bound (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (α := ℝ) 0 1)) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (α := ℝ) (0 : ℝ) 1),
      ‖(Icc (α := ℝ) (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) x - g x‖ ≤ M) :
    1 / 2 ≤ M := by
  have hL : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (α := ℝ) (0 : ℝ) (1 / 2)),
      max (1 - g x - M) 0 = 0 := by
    have h := ae_restrict_of_ae_restrict_of_subset
      (show Icc (α := ℝ) (0 : ℝ) (1 / 2) ⊆ Icc (α := ℝ) (0 : ℝ) 1 from
        fun x hx => ⟨hx.1, by linarith [hx.2]⟩) hM
    filter_upwards [h, self_mem_ae_restrict measurableSet_Icc] with x hx hxi
    rw [indicator_of_mem hxi] at hx
    rw [Real.norm_eq_abs] at hx
    exact max_eq_right (by linarith [(abs_le.mp hx).2])
  have hR : ∀ᵐ x ∂(volume : Measure ℝ).restrict (Icc (α := ℝ) (1 / 2 : ℝ) 1),
      max (g x - M) 0 = 0 := by
    have h := ae_restrict_of_ae_restrict_of_subset
      (show Icc (α := ℝ) (1 / 2 : ℝ) 1 ⊆ Icc (α := ℝ) (0 : ℝ) 1 from
        fun x hx => ⟨by linarith [hx.1], hx.2⟩) hM
    filter_upwards [h, self_mem_ae_restrict measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (1 / 2 : ℝ))] with x hx hxi hne
    have hxnot : x ∉ Icc (α := ℝ) (0 : ℝ) (1 / 2) := by
      simp only [mem_Icc, not_and_or, not_le]
      right
      exact lt_of_le_of_ne hxi.1 (Ne.symm hne)
    rw [indicator_of_notMem hxnot, zero_sub, norm_neg, Real.norm_eq_abs] at hx
    exact max_eq_right (by linarith [(abs_le.mp hx).2])
  have hgL : ContinuousOn g (Icc (α := ℝ) (0 : ℝ) (1 / 2)) :=
    hg.mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
  have hgR : ContinuousOn g (Icc (α := ℝ) (1 / 2 : ℝ) 1) :=
    hg.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  have bL := Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ))
    (by norm_num : (0 : ℝ) ≠ 1 / 2) hL
    (((continuousOn_const.sub hgL).sub continuousOn_const).sup continuousOn_const)
    continuousOn_const (show (1 / 2 : ℝ) ∈ Icc (α := ℝ) (0 : ℝ) (1 / 2) by norm_num)
  have bR := Measure.eqOn_Icc_of_ae_eq (μ := (volume : Measure ℝ))
    (by norm_num : (1 / 2 : ℝ) ≠ 1) hR
    ((hgR.sub continuousOn_const).sup continuousOn_const)
    continuousOn_const (show (1 / 2 : ℝ) ∈ Icc (α := ℝ) (1 / 2 : ℝ) 1 by norm_num)
  have := le_max_left (1 - g (1 / 2) - M) 0
  have := le_max_left (g (1 / 2) - M) 0
  linarith

/-- Every continuous function on the subtype interval has an ambient
    representative satisfying precisely the hypothesis used below. -/
lemma interval_representative (g : Icc (0 : ℝ) 1 → ℝ) (hg : Continuous g) :
    ∃ G : ℝ → ℝ, ContinuousOn G (Icc (0 : ℝ) 1) ∧
      ∀ x : Icc (0 : ℝ) 1, G x = g x := by
  let G : ℝ → ℝ := Function.extend Subtype.val g (fun _ => 0)
  have hG (x : Icc (0 : ℝ) 1) : G x = g x :=
    Subtype.val_injective.extend_apply g (fun _ => 0) x
  refine ⟨G, ?_, hG⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun x : Icc (0 : ℝ) 1 => G x)
  have heq : (fun x : Icc (0 : ℝ) 1 => G x) = g := funext hG
  simpa only [heq] using hg

theorem continuous_approximation_lower_bound :
    Specs.D11.Ch11.InfinityDensityFailure.continuous_approximation_lower_bound := by
  intro g hg
  change (1 / 2 : ℝ≥0∞) ≤ essentialSupNorm
    ((volume : Measure ℝ).completion.restrict (Icc (α := ℝ) (0 : ℝ) 1)) _
  rw [norm_restrict_completion _ measurableSet_Icc]
  apply le_sInf
  rintro b ⟨M, hM, rfl⟩
  have hm := midpoint_bound g hg M ((almostEverywhere_iff_native _ _).mp hM)
  have hm' : (1 / 2 : ℝ≥0) ≤ M := by exact_mod_cast hm
  have hcoe := ENNReal.coe_le_coe.mpr hm'
  norm_num at hcoe ⊢
  exact hcoe

variable {𝕜 : Type} [RCLike 𝕜]

/-- A difference of scalar indicators is bounded by one everywhere. -/
lemma indicator_difference_bound (s : Set ℝ) (h x : ℝ) :
    ‖s.indicator (fun _ => (1 : 𝕜)) (x - h) -
      s.indicator (fun _ => (1 : 𝕜)) x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ s <;> by_cases ht : x - h ∈ s <;> simp [hx, ht]

/-- Each nonzero shift of size less than one leaves a positive-length
    interval on which the absolute difference is exactly one. -/
lemma translated_indicator_bound (h : ℝ) (h0 : 0 < |h|) (h1 : |h| < 1) (M : ℝ)
    (hM : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖(Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜)) (x - h) -
        (Icc (0 : ℝ) 1).indicator (fun _ => (1 : 𝕜)) x‖ ≤ M) : 1 ≤ M := by
  classical
  rcases abs_lt.mp h1 with ⟨hlo, hhi⟩
  by_cases hh : 0 < h
  · have hpos : (volume : Measure ℝ) (Ioo 0 h) ≠ 0 :=
      ((Measure.measure_Ioo_pos volume).mpr hh).ne'
    obtain ⟨x, hx, hMx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hM)
    have hxin : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, by linarith [hx.2]⟩
    have hxout : x - h ∉ Icc (0 : ℝ) 1 := by
      intro hm
      linarith [hm.1, hx.2]
    simpa [indicator_of_mem hxin, indicator_of_notMem hxout] using hMx
  · have hh' : h < 0 := by
      have : h ≠ 0 := abs_pos.mp h0
      exact lt_of_le_of_ne (le_of_not_gt hh) this
    have hpos : (volume : Measure ℝ) (Ioo h 0) ≠ 0 :=
      ((Measure.measure_Ioo_pos volume).mpr hh').ne'
    obtain ⟨x, hx, hMx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hM)
    have hxout : x ∉ Icc (0 : ℝ) 1 := by
      intro hm
      linarith [hm.1, hx.2]
    have hxin : x - h ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa [indicator_of_mem hxin, indicator_of_notMem hxout] using hMx

theorem translated_indicator_norm :
    Specs.D11.Ch11.InfinityDensityFailure.translated_indicator_norm := by
  intro 𝕜 _ h h0 h1
  change essentialSupNorm (volume : Measure ℝ).completion _ = 1
  have heq (f : ℝ → 𝕜) : essentialSupNorm (volume : Measure ℝ).completion f =
      essentialSupNorm (volume : Measure ℝ) f := by
    exact (essentialSupNorm_eq_native (volume : Measure ℝ).completion f).trans
      (essentialSupNorm_eq_native (volume : Measure ℝ) f).symm
  rw [heq]
  apply le_antisymm
  · apply (essentialSupNorm_le_iff _ _ 1).mpr
    apply (almostEverywhere_iff_native _ _).mpr
    exact ae_of_all _ (indicator_difference_bound _ h)
  · apply le_sInf
    rintro b ⟨M, hM, rfl⟩
    have hm := translated_indicator_bound h h0 h1 M ((almostEverywhere_iff_native _ _).mp hM)
    have hm' : (1 : ℝ≥0) ≤ M := by exact_mod_cast hm
    simpa only [ENNReal.coe_one] using ENNReal.coe_le_coe.mpr hm'

end D11.Ch11.InfinityDensityFailure
