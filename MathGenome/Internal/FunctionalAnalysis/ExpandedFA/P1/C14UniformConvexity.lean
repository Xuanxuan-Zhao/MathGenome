import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14UniformConvexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Uniform convexity and strict convexity, paper.tex:2849–2860.
The canonical predicate value is shared in the independent specification so
later modulus and rotundity statements can use the same definition. -/
namespace ExpandedFA.P1.C14UniformConvexity

universe u v

/-- Separated pairs in the closed unit ball have uniformly interior midpoints.
This is the exact manuscript predicate shared with the independent Specs;
it includes spaces where the separated pairs do not exist. -/
def UniformlyConvex : Spec.UniformlyConvexType.{u,v} :=
  Spec.UniformlyConvexValue

variable (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The scalar midpoint has half the norm of the sum over either field. -/
lemma norm_midpoint_eq_half (x y : E) :
    ‖(2 : 𝕜)⁻¹ • (x + y)‖ = ‖x + y‖ / 2 := by
  rw [norm_smul, norm_inv]
  norm_num
  ring

/-- The unit-sphere class agrees with the manuscript's closed-ball condition.
For ε > 2 no pair of unit vectors can satisfy the separation hypothesis. -/
theorem native_iff_uniformlyConvex : UniformConvexSpace E ↔ UniformlyConvex 𝕜 E := by
  constructor
  · intro h
    letI : UniformConvexSpace E := h
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    intro ε hε _
    obtain ⟨δ, hδ, h⟩ := exists_forall_closed_ball_dist_add_le_two_sub E hε
    refine ⟨δ / 2, by linarith, fun x y hx hy hxy => ?_⟩
    rw [norm_midpoint_eq_half]
    have := h hx hy hxy
    linarith
  · intro h
    constructor
    intro ε hε
    by_cases hε₂ : ε ≤ 2
    · obtain ⟨δ, hδ, hxy⟩ := h ε hε hε₂
      refine ⟨2 * δ, by linarith, fun x hx y hy hsep => ?_⟩
      have hm := hxy x y hx.le hy.le hsep
      rw [norm_midpoint_eq_half] at hm
      linarith
    · refine ⟨1, by norm_num, fun x hx y hy hsep => ?_⟩
      have hbound := norm_sub_le x y
      exfalso
      linarith

/-- Uniform convexity implies strict convexity on the underlying real space. -/
theorem UniformlyConvex.strictConvexSpace (h : UniformlyConvex 𝕜 E) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    StrictConvexSpace ℝ E := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : UniformConvexSpace E := (native_iff_uniformlyConvex 𝕜 E).mpr h
  infer_instance

/-- Distinct points on the unit sphere have midpoint norm strictly below one. -/
theorem UniformlyConvex.strict_midpoint (h : UniformlyConvex 𝕜 E)
    (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : x ≠ y) :
    ‖(2 : 𝕜)⁻¹ • (x + y)‖ < 1 := by
  have hpos : 0 < ‖x - y‖ := norm_sub_pos_iff.mpr hne
  have hbound : ‖x - y‖ ≤ 2 := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ = 2 := by rw [hx, hy]; norm_num
  obtain ⟨δ, hδ, hδxy⟩ := h ‖x - y‖ hpos hbound
  have := hδxy x y hx.le hy.le le_rfl
  linarith

/-- The defining separated pairs do not exist in a subsingleton space. -/
theorem uniformlyConvex_of_subsingleton [Subsingleton E] : UniformlyConvex 𝕜 E := by
  intro ε hε _
  refine ⟨1, by norm_num, fun x y _ _ hxy => ?_⟩
  have heq : x = y := Subsingleton.elim _ _
  simp [heq] at hxy
  linarith

end ExpandedFA.P1.C14UniformConvexity
