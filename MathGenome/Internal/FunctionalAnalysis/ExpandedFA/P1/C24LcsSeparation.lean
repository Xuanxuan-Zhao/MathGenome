import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24LcsSeparation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C06StrongSeparation
import Mathlib.Tactic.Linarith

/-!
Separation in the given locally convex topology, `fa2:p1:c24:lcs-separation`.

The accepted Chapter 6 locally convex theorem supplies strict separation from
a closed convex set. Its application to a singleton distinguishes points.
For a general set, subtracting the finite supremum from the value at the
external point gives a uniform positive margin. Restriction to real scalars
handles complex spaces without changing their topology.
-/
namespace ExpandedFA.P1.C24

universe u

/-- The continuous real dual separates distinct points. -/
theorem real_locally_convex_points_separated :
    Specs.ExpandedFA.P1.C24LcsSeparation.realPointsType.{u} := by
  intro E _ _ _ _ _ _ _ x y hxy
  obtain ⟨ℓ, _, hbd, hlt⟩ := C06.real_locally_convex_point_strong_separation
    {y} x (Set.singleton_nonempty y) isClosed_singleton (convex_singleton y)
    (by simpa only [Set.mem_singleton_iff] using hxy)
  have hy : ℓ y ≤ sSup (ℓ '' {y}) := le_csSup hbd ⟨y, rfl, rfl⟩
  exact ⟨ℓ, ne_of_gt (hy.trans_lt hlt)⟩

/-- The same separator witnesses the finite supremum and the positive gap. -/
theorem real_locally_convex_closed_convex_separation :
    Specs.ExpandedFA.P1.C24LcsSeparation.realClosedConvexType.{u} := by
  intro E _ _ _ _ _ _ _ C x₀ hC hclosed hconvex hx₀
  obtain ⟨ℓ, hne, hbd, hlt⟩ := C06.real_locally_convex_point_strong_separation
    C x₀ hC hclosed hconvex hx₀
  refine ⟨ℓ, hne, hbd, hlt, ℓ x₀ - sSup (ℓ '' C), sub_pos.mpr hlt, ?_⟩
  intro c hc
  have hle : ℓ c ≤ sSup (ℓ '' C) := le_csSup hbd ⟨c, hc, rfl⟩
  linarith

/-- Complex ambient spaces are regarded as real for convex geometry. -/
theorem complex_locally_convex_points_separated :
    Specs.ExpandedFA.P1.C24LcsSeparation.complexPointsType.{u} := by
  intro E _ _ _ _ _ _ _ x y hxy
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_locally_convex_points_separated x y hxy

/-- Restricting scalars preserves both the given topology and the strict gap. -/
theorem complex_locally_convex_closed_convex_separation :
    Specs.ExpandedFA.P1.C24LcsSeparation.complexClosedConvexType.{u} := by
  intro E _ _ _ _ _ _ _ C x₀ hC hclosed hconvex hx₀
  let : ContinuousSMul ℝ E := IsScalarTower.continuousSMul ℂ
  exact real_locally_convex_closed_convex_separation C x₀ hC hclosed hconvex hx₀

end ExpandedFA.P1.C24
