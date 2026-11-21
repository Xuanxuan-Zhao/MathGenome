import MathGenome.Internal.RealAnalysis.Specs.D11.Ch16.RiemannCriterion
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.OscillationCriterion
import Mathlib.MeasureTheory.Integral.IntegrableOn

noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal

namespace D11.Ch16.RiemannCriterion

open SingleVariableAnalysis

/-- The coordinate identification with the already constructed Euclidean line. -/
def realPointEquiv : ℝ ≃ᵐ D11.Ch03.Point 1 :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans
    (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))

@[simp] theorem realPointEquiv_apply (t : ℝ) (i : Fin 1) :
    realPointEquiv t i = t := rfl

lemma realPointEquiv_preserving : MeasurePreserving realPointEquiv :=
  (PiLp.volume_preserving_toLp (Fin 1)).comp
    (volume_preserving_funUnique (Fin 1) ℝ).symm

lemma realPointEquiv_volume (S : Set ℝ) :
    volume (realPointEquiv '' S) = volume S := by
  change volume (realPointEquiv.toEquiv '' S) = volume S
  rw [realPointEquiv.toEquiv.image_eq_preimage_symm]
  exact realPointEquiv_preserving.symm.measure_preimage_equiv S

/-- Cover-nullity of the calculus foundation implies nullity for native volume. -/
lemma volume_zero_of_lengthZero {S : Set ℝ} (hS : LengthZero S) : volume S = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨a, b, _, hc, hs⟩ := hS ε hε
  calc
    volume S ≤ volume (⋃ n, Ioo (a n) (b n)) := measure_mono hc
    _ ≤ ∑' n, volume (Ioo (a n) (b n)) := measure_iUnion_le _
    _ ≤ 0 + (ε : ℝ≥0∞) := by
      simpa only [Real.volume_Ioo, nonnegativeExtendedSum,
        ENNReal.ofReal_coe_nnreal, zero_add] using hs.le

/-- Conversely extract interval covers from the already established covering
outer volume on the Euclidean line. Summable padding makes every interval
nonempty, including any empty boxes in a padded cover. -/
lemma lengthZero_of_volume_zero {S : Set ℝ} (hS : volume S = 0) : LengthZero S := by
  intro ε hε
  have houter : Specs.D11.Ch03.OuterVolume.outerVolume_value 1 (realPointEquiv '' S) = 0 := by
    rw [← D11.Ch03.LebesgueMeasures.native_outer_agreement,
      realPointEquiv_volume, hS]
  have hsmall : Specs.D11.Ch03.OuterVolume.outerVolume_value 1 (realPointEquiv '' S) <
      ENNReal.ofReal (ε / 2) := by
    rw [houter]
    exact ENNReal.ofReal_pos.mpr (half_pos hε)
  rw [D11.Ch03.OuterVolume.ordered_covering_formula] at hsmall
  simp only [iInf_lt_iff] at hsmall
  obtain ⟨a, b, hab, hc, hs⟩ := hsmall
  have hsum : (∑' n, ENNReal.ofReal (b n 0 - a n 0)) <
      ENNReal.ofReal (ε / 2) := by
    simpa only [Fin.prod_univ_one] using hs
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr (half_pos hε)).ne' ℕ
  let l : ℕ → ℝ := fun n => a n 0 - (δ n : ℝ) / 2
  let u : ℕ → ℝ := fun n => b n 0 + (δ n : ℝ) / 2
  have hlen (n) : u n - l n = (b n 0 - a n 0) + (δ n : ℝ) := by
    dsimp [u, l]
    ring
  refine ⟨l, u, ?_, ?_, ?_⟩
  · intro n
    have := hab n 0
    have := NNReal.coe_pos.mpr (hδ n)
    dsimp [l, u]
    linarith
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hc (mem_image_of_mem realPointEquiv hx))
    refine mem_iUnion.mpr ⟨n, ?_⟩
    have hn0 := hn 0
    have hd : 0 < (δ n : ℝ) := NNReal.coe_pos.mpr (hδ n)
    change a n 0 < x ∧ x < b n 0 at hn0
    dsimp [l, u]
    constructor <;> linarith [hn0.1, hn0.2]
  · change (∑' n, ENNReal.ofReal (u n - l n)) < _
    simp_rw [hlen, ENNReal.ofReal_add (sub_nonneg.mpr (hab _ 0))
      (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.tsum_add]
    calc
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add hsum hδsum
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
        congr 1
        ring

lemma lengthZero_iff_volume_zero (S : Set ℝ) : LengthZero S ↔ volume S = 0 :=
  ⟨volume_zero_of_lengthZero, lengthZero_of_volume_zero⟩

/-- Lebesgue's criterion concerns the original representative at every point. -/
theorem riemann_criterion : Specs.D11.Ch16.RiemannCriterion.riemann_criterion := by
  intro f a b hab hf
  exact (SingleVariableAnalysis.discontinuity_criterion f hab.le hf).trans
    (lengthZero_iff_volume_zero _)

/-- Remove a measurable null envelope of the discontinuities. Continuity on
its complement gives a.e. measurability; completion then gives measurability
of the original, arbitrarily modified, representative. -/
theorem representative_measurable :
    Specs.D11.Ch16.RiemannCriterion.representative_measurable := by
  intro f a b hab hI
  let D : Set ℝ := {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x}
  let N := toMeasurable volume D
  have hD : volume D = 0 :=
    (riemann_criterion f a b hab hI.choose_spec.choose).mp hI
  have hN : volume N = 0 := by
    dsimp [N]
    rw [measure_toMeasurable, hD]
  have hc : ContinuousOn f (Icc a b \ N) := by
    intro x hx
    have hcont : ContinuousWithinAt f (Icc a b) x := by
      by_contra h
      exact hx.2 (subset_toMeasurable volume D ⟨hx.1, h⟩)
    exact hcont.mono sdiff_subset
  have hm : AEMeasurable f (volume.restrict (Icc a b)) := by
    have hm := hc.aemeasurable (μ := volume)
      (measurableSet_Icc.diff (measurableSet_toMeasurable _ _))
    rwa [Measure.restrict_congr_set (sdiff_null_ae_eq_self hN)] at hm
  exact ((aemeasurable_indicator_iff measurableSet_Icc).mpr hm).nullMeasurable.measurable'

theorem restriction_measurable :
    Specs.D11.Ch16.RiemannCriterion.restriction_measurable := by
  intro f a b hab hI
  have hm := representative_measurable f a b hab hI
  intro U hU
  refine ⟨((Icc a b).indicator f) ⁻¹' U, hm hU, ?_⟩
  ext x
  simp only [mem_preimage, indicator_of_mem x.property]

/-- The literal subtype-domain version, with an explicit extension/restriction
bridge, so no choice of values outside the source interval is a premise. -/
theorem subtype_criterion : Specs.D11.Ch16.RiemannCriterion.subtype_criterion := by
  intro a b hab f hf
  let F := Function.extend Subtype.val f (fun _ : ℝ => (0 : ℝ))
  have hF (x : Icc a b) : F x = f x :=
    Subtype.val_injective.extend_apply f _ x
  have hres : (Icc a b).domRestrict F = f := funext hF
  have hrange : F '' Icc a b = Set.range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hF ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, hF x⟩
  have hbound : Riemann.BoundedOnInterval F a b := by
    change BddBelow (F '' Icc a b) ∧ BddAbove (F '' Icc a b)
    rwa [hrange]
  have hdisc : {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt F (Icc a b) x} =
      Subtype.val '' {x | ¬ ContinuousAt f x} := by
    ext x
    constructor
    · rintro ⟨hx, hdis⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rwa [continuousWithinAt_iff_continuousAt_domRestrict F hx, hres] at hdis
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, ?_⟩
      rwa [continuousWithinAt_iff_continuousAt_domRestrict F y.property, hres]
  constructor
  · have hi := riemann_criterion F a b hab hbound
    rwa [hdisc] at hi
  · intro hi
    have hm := restriction_measurable F a b hab hi
    convert hm using 1
    exact hres.symm

end D11.Ch16.RiemannCriterion
