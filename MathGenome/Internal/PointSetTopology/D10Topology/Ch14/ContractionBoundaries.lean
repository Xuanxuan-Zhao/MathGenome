import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.ContractionBoundaries
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricComparison
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Counterexamples to dropping the completeness, contraction, or nonemptiness
hypotheses of Banach's theorem. Source: paper.tex, d10:14:contraction-boundaries. -/
namespace D10Topology.Ch14.ContractionBoundaries
open D10Topology.Ch09
open Specs.D10Topology.Ch09.MetricComparison (OpenUnitInterval)

theorem interval_counterexample :
    Specs.D10Topology.Ch14.ContractionBoundaries.interval_counterexample := by
  refine ⟨MetricComparison.usual_interval_incomplete, ?_⟩
  let T : OpenUnitInterval → OpenUnitInterval := fun x =>
    ⟨x.val / 2, by
      have hx0 : 0 < x.val := x.property.1
      have hx1 : x.val < 1 := x.property.2
      constructor <;> linarith⟩
  refine ⟨T, fun _ => rfl, ?_, ?_⟩
  · intro x y
    change |x.val / 2 - y.val / 2| ≤ (1 / 2 : ℝ) * |x.val - y.val|
    rw [← sub_div, abs_div]
    norm_num
    exact le_of_eq (by ring)
  · rintro ⟨x, hx⟩
    have he := congrArg Subtype.val hx
    change x.val / 2 = x.val at he
    have := x.property.1
    linarith

theorem translation_counterexample :
    Specs.D10Topology.Ch14.ContractionBoundaries.translation_counterexample := by
  refine ⟨(sequentiallyComplete_iff_mathlib _).mpr inferInstance, ?_⟩
  refine ⟨fun x => x + 1, fun _ => rfl, ?_, ?_⟩
  · intro x y
    simp only [Real.dist_eq, add_sub_add_right_eq_sub, one_mul, le_refl]
  · rintro ⟨x, hx⟩
    linarith

/-- The source's factorization, with both strict inequalities on an ordered pair. -/
private theorem ray_difference {x y : ℝ} (hy : 1 ≤ y) (hxy : y < x) :
    0 < (x + 1 / x) - (y + 1 / y) ∧
      (x + 1 / x) - (y + 1 / y) < x - y := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := hy0.trans hxy
  have hprod : 1 < x * y := by nlinarith
  have hinv0 : 0 < 1 / (x * y) := one_div_pos.mpr (mul_pos hx0 hy0)
  have hinv1 : 1 / (x * y) < 1 := (div_lt_one (mul_pos hx0 hy0)).mpr hprod
  have he : (x + 1 / x) - (y + 1 / y) = (x - y) * (1 - 1 / (x * y)) := by
    field_simp
    ring
  rw [he]
  constructor <;> nlinarith

theorem strict_decrease_counterexample :
    Specs.D10Topology.Ch14.ContractionBoundaries.strict_decrease_counterexample := by
  have hc : CompleteSpace (Set.Ici (1 : ℝ)) :=
    isClosed_Ici.isComplete.completeSpace_coe
  refine ⟨(sequentiallyComplete_iff_mathlib _).mpr hc, ?_⟩
  let T : Set.Ici (1 : ℝ) → Set.Ici (1 : ℝ) := fun x =>
    ⟨x.val + 1 / x.val, by
      have hx : 1 ≤ x.val := x.property
      have hx0 : 0 < x.val := by linarith
      have := one_div_pos.mpr hx0
      change 1 ≤ x.val + 1 / x.val
      linarith⟩
  refine ⟨T, fun _ => rfl, ?_, ?_⟩
  · intro x y hne
    have hval : x.val ≠ y.val := fun h => hne (Subtype.ext h)
    change |(x.val + 1 / x.val) - (y.val + 1 / y.val)| < |x.val - y.val|
    rcases lt_or_gt_of_ne hval with hxy | hxy
    · obtain ⟨hpos, hlt⟩ := ray_difference x.property hxy
      rw [abs_of_neg (by linarith : (x.val + 1 / x.val) - (y.val + 1 / y.val) < 0),
        abs_of_neg (by linarith : x.val - y.val < 0)]
      linarith
    · obtain ⟨hpos, hlt⟩ := ray_difference y.property hxy
      rw [abs_of_pos hpos, abs_of_pos (sub_pos.mpr hxy)]
      exact hlt
  · rintro ⟨x, hx⟩
    have he := congrArg Subtype.val hx
    change x.val + 1 / x.val = x.val at he
    have hx1 : 1 ≤ x.val := x.property
    have hx0 : 0 < x.val := by linarith
    have := one_div_pos.mpr hx0
    linarith

theorem empty_counterexample :
    Specs.D10Topology.Ch14.ContractionBoundaries.empty_counterexample := by
  refine ⟨empty_complete _, ?_⟩
  refine ⟨id, ?_, ?_⟩
  · rintro ⟨x, _⟩
    exact x.elim
  · intro T _
    funext x
    exact x.elim

end D10Topology.Ch14.ContractionBoundaries
