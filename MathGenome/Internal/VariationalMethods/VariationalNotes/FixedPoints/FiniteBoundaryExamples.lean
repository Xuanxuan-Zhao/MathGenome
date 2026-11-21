import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The two finite-dimensional boundary examples from `paper.tex`,
lines 4777–4782. No fixed-point existence theorem is used. -/

namespace VariationalNotes.FixedPoints

open Set

/-- The real unit circle is a compact nonconvex nonempty set. -/
theorem circle_geometry :
    Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples.CircleGeometry := by
  refine ⟨⟨(1, 0), by norm_num [realUnitCircle]⟩, ?_, ?_⟩
  · have hclosed : IsClosed realUnitCircle :=
      isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const
    apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed
    rintro ⟨x, y⟩ hp
    change x ^ 2 + y ^ 2 = 1 at hp
    change x ∈ Icc (-1 : ℝ) 1 ∧ y ∈ Icc (-1 : ℝ) 1
    have hx := sq_nonneg x
    have hy := sq_nonneg y
    constructor <;> constructor <;> nlinarith
  · intro hc
    have hp : (1, 0) ∈ realUnitCircle := by norm_num [realUnitCircle]
    have hm : (-1, 0) ∈ realUnitCircle := by norm_num [realUnitCircle]
    have hz := hc hp hm (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    norm_num [realUnitCircle, Prod.smul_mk, smul_eq_mul] at hz

/-- The antipodal rotation preserves the circle and has no fixed point there. -/
theorem antipodal_properties :
    Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples.AntipodalProperties := by
  refine ⟨continuous_id.neg, ?_, ?_⟩
  · rintro ⟨x, y⟩ hp
    simpa [antipodal, realUnitCircle] using hp
  · rintro ⟨⟨x, y⟩, hp, he⟩
    have hx : -x = x := congrArg Prod.fst he
    have hy : -y = y := congrArg Prod.snd he
    change x ^ 2 + y ^ 2 = 1 at hp
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0] at hp

/-- The interval is bounded, open and convex. -/
theorem interval_geometry :
    Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples.IntervalGeometry := by
  exact ⟨⟨1/2, by norm_num [openUnitInterval]⟩, Metric.isBounded_Ioo 0 1,
    isOpen_Ioo, convex_Ioo 0 1⟩

/-- The only ambient fixed point is the endpoint excluded from the interval. -/
theorem interval_properties :
    Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples.IntervalProperties := by
  have hfixed (x : ℝ) : intervalAffine x = x ↔ x = 1 := by
    dsimp [intervalAffine]
    constructor <;> intro h <;> linarith
  refine ⟨(continuous_const.add continuous_id).div_const 2, ?_, hfixed, ?_⟩
  · intro x hx
    change 0 < x ∧ x < 1 at hx
    change 0 < (1 + x) / 2 ∧ (1 + x) / 2 < 1
    constructor <;> linarith [hx.1, hx.2]
  · rintro ⟨x, hx, he⟩
    have hx1 := (hfixed x).mp he
    change 0 < x ∧ x < 1 at hx
    linarith [hx.2]

end VariationalNotes.FixedPoints
