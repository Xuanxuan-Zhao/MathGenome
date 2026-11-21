import MathGenome.Internal.RealAnalysis.D11.Ch12.BvDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.JordanFunctions
import Mathlib.Tactic.Linarith

namespace D11.Ch12
open Set
open scoped ENNReal

/-- Positive variation, normalized to vanish at the left endpoint. -/
noncomputable def jordanPositive (F : ℝ → ℝ) (a x : ℝ) : ℝ :=
  ((variationFunction F a x).toReal + F x - F a) / 2

/-- Negative variation, normalized to vanish at the left endpoint. -/
noncomputable def jordanNegative (F : ℝ → ℝ) (a x : ℝ) : ℝ :=
  ((variationFunction F a x).toReal - F x + F a) / 2

/-- Finiteness passes to every closed subinterval. -/
lemma BV.subinterval {F : ℝ → ℝ} {a b x y : ℝ} (hf : BV F a b)
    (hax : a ≤ x) (hyb : y ≤ b) : BV F x y := by
  apply (bv_iff_boundedVariationOn F x y).mpr
  exact ((bv_iff_boundedVariationOn F a b).mp hf).mono (Icc_subset_Icc hax hyb)

/-- Additivity of finite variation and the increment bound, in real arithmetic. -/
lemma variation_increment_bounds {F : ℝ → ℝ} {a b x y : ℝ} (hf : BV F a b)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    |F y - F x| ≤ (variation F a y).toReal - (variation F a x).toReal := by
  have hax : BV F a x := hf.subinterval le_rfl hx.2
  have hxy' : BV F x y := hf.subinterval hx.1 hy.2
  have hadd := congrArg ENNReal.toReal (variation_additive F hx.1 hxy)
  rw [ENNReal.toReal_add (ne_of_lt hax) (ne_of_lt hxy')] at hadd
  have hnorm := norm_sub_le_variation F hxy hxy'
  rw [Real.norm_eq_abs] at hnorm
  linarith

/-- The canonical real Jordan decomposition on a compact interval. -/
theorem jordan_decomposition (F : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hf : BV F a b) :
    EqOn F (fun x => F a + jordanPositive F a x - jordanNegative F a x) (Icc a b) ∧
    MonotoneOn (jordanPositive F a) (Icc a b) ∧
    MonotoneOn (jordanNegative F a) (Icc a b) ∧
    jordanPositive F a a = 0 ∧ jordanNegative F a a = 0 ∧
    ∀ x ∈ Icc a b,
      0 ≤ jordanPositive F a x ∧ jordanPositive F a x ≤ (variation F a b).toReal ∧
      0 ≤ jordanNegative F a x ∧ jordanNegative F a x ≤ (variation F a b).toReal := by
  have hp0 : jordanPositive F a a = 0 := by
    simp [jordanPositive, variationFunction, variation_self]
  have hn0 : jordanNegative F a a = 0 := by
    simp [jordanNegative, variationFunction, variation_self]
  have hp : MonotoneOn (jordanPositive F a) (Icc a b) := by
    intro x hx y hy hxy
    have hv := variation_increment_bounds hf hx hy hxy
    have hneg := neg_abs_le (F y - F x)
    dsimp [jordanPositive, variationFunction]
    linarith
  have hn : MonotoneOn (jordanNegative F a) (Icc a b) := by
    intro x hx y hy hxy
    have hv := variation_increment_bounds hf hx hy hxy
    have hpos := le_abs_self (F y - F x)
    dsimp [jordanNegative, variationFunction]
    linarith
  have hnorm := norm_sub_le_variation F hab hf
  rw [Real.norm_eq_abs] at hnorm
  have hpos := le_abs_self (F b - F a)
  have hneg := neg_abs_le (F b - F a)
  have hpb : jordanPositive F a b ≤ (variation F a b).toReal := by
    dsimp [jordanPositive, variationFunction]
    linarith
  have hnb : jordanNegative F a b ≤ (variation F a b).toReal := by
    dsimp [jordanNegative, variationFunction]
    linarith
  refine ⟨?_, hp, hn, hp0, hn0, ?_⟩
  · intro x hx
    dsimp [jordanPositive, jordanNegative]
    ring
  · intro x hx
    refine ⟨?_, (hp hx ⟨hab, le_rfl⟩ hx.2).trans hpb, ?_,
      (hn hx ⟨hab, le_rfl⟩ hx.2).trans hnb⟩
    · simpa only [hp0] using hp (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hx hx.1
    · simpa only [hn0] using hn (show a ∈ Icc a b from ⟨le_rfl, hab⟩) hx hx.1

/-- Jordan's characterization, with boundedness on the original interval. -/
theorem bv_iff_difference_bounded_monotone (F : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    BV F a b ↔ ∃ G H : ℝ → ℝ,
      MonotoneOn G (Icc a b) ∧ MonotoneOn H (Icc a b) ∧
      BddAbove (G '' Icc a b) ∧ BddBelow (G '' Icc a b) ∧
      BddAbove (H '' Icc a b) ∧ BddBelow (H '' Icc a b) ∧
      EqOn F (fun x => G x - H x) (Icc a b) := by
  constructor
  · intro hf
    obtain ⟨heq, hp, hn, hp0, hn0, hbounds⟩ := jordan_decomposition F hab hf
    refine ⟨fun x => F a + jordanPositive F a x, jordanNegative F a, ?_, hn,
      ?_, ?_, ?_, ?_, heq⟩
    · intro x hx y hy hxy
      exact add_le_add le_rfl (hp hx hy hxy)
    · refine ⟨F a + (variation F a b).toReal, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact add_le_add le_rfl (hbounds x hx).2.1
    · refine ⟨F a, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact le_add_of_nonneg_right (hbounds x hx).1
    · refine ⟨(variation F a b).toReal, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (hbounds x hx).2.2.2
    · refine ⟨0, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (hbounds x hx).2.2.1
  · rintro ⟨G, H, hg, hh, _, _, _, _, heq⟩
    have hgv : BV G a b := by
      apply (bv_iff_boundedVariationOn G a b).mpr
      simpa only [inter_self] using hg.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    have hhv : BV H a b := by
      apply (bv_iff_boundedVariationOn H a b).mpr
      simpa only [inter_self] using hh.locallyBoundedVariationOn a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
    dsimp [BV] at *
    rw [variation_congr heq]
    exact (variation_sub_le G H a b).trans_lt (ENNReal.add_lt_top.mpr ⟨hgv, hhv⟩)

end D11.Ch12
