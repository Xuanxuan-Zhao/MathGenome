import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.NormalStructure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import Mathlib.Tactic.Module

/-! Normal structure and the uniformly convex midpoint argument from
paper.tex:13081–13085 and 13105–13113. -/

namespace ExpandedFA.Geometry.NormalStructure

universe u v

/-- Every convex subset of positive diameter has a point whose supremum
distance to the subset is strictly below its diameter. -/
def HasNormalStructure : Spec.NormalStructureType.{u} := Spec.NormalStructureValue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single midpoint has a uniform distance bound strictly below the
diameter. The uniform bound, rather than individual strict inequalities,
allows passage to the supremum. -/
lemma exists_nondiametral_point [UniformConvexSpace E] {D : Set E}
    (hbounded : Bornology.IsBounded D) (hconvex : Convex ℝ D)
    (hdiam : 0 < Metric.diam D) :
    ∃ z ∈ D, sSup ((fun y => ‖z - y‖) '' D) < Metric.diam D := by
  let d := Metric.diam D
  have hd : 0 < d := hdiam
  obtain ⟨a, ha, b, hb, hab⟩ :
      ∃ a ∈ D, ∃ b ∈ D, d / 2 < ‖a - b‖ := by
    by_contra! h
    have hle : Metric.diam D ≤ d / 2 :=
      Metric.diam_le_of_forall_dist_le (by positivity) (fun a ha b hb => by
        simpa only [dist_eq_norm] using h a ha b hb)
    change d ≤ d / 2 at hle
    linarith
  obtain ⟨δ, hδ, huc⟩ :=
    exists_forall_closed_ball_dist_add_le_two_mul_sub E (by positivity : 0 < d / 2) d
  let z := (1 / 2 : ℝ) • (a + b)
  have hz : z ∈ D := by
    simpa only [z, smul_add] using
      hconvex ha hb (by norm_num : 0 ≤ (1 / 2 : ℝ))
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hbound : ∀ y ∈ D, ‖z - y‖ ≤ d - δ / 2 := by
    intro y hy
    have hay : ‖a - y‖ ≤ d := by
      simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hbounded ha hy
    have hby : ‖b - y‖ ≤ d := by
      simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hbounded hb hy
    have hsep : d / 2 ≤ ‖(a - y) - (b - y)‖ := by
      have heq : (a - y) - (b - y) = a - b := by abel
      rw [heq]
      exact hab.le
    have hsum := huc hay hby hsep
    have heq : z - y = (1 / 2 : ℝ) • ((a - y) + (b - y)) := by
      dsimp [z]
      module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    linarith
  refine ⟨z, hz, lt_of_le_of_lt (b := d - δ / 2) ?_ ?_⟩
  · apply csSup_le
    · exact ⟨‖z - a‖, ⟨a, ha, rfl⟩⟩
    · rintro r ⟨y, hy, rfl⟩
      exact hbound y hy
  · change d - δ / 2 < d
    linarith

/-- Every bounded convex subset of a uniformly convex normed space has
normal structure; in particular this holds in a uniformly convex Banach space. -/
theorem uniformlyConvex_normalStructure : Spec.UniformlyConvexNormalStructure.{u,v} := by
  intro 𝕜 E _ _ _ huc
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : UniformConvexSpace E :=
    (ExpandedFA.P1.C14UniformConvexity.native_iff_uniformlyConvex 𝕜 E).mpr huc
  intro C hbounded _ D hDC hconvex hdiam
  exact exists_nondiametral_point (hbounded.subset hDC) hconvex hdiam

end ExpandedFA.Geometry.NormalStructure
