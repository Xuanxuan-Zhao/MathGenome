import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14AttainmentExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Minimization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14MilmanPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import Mathlib.Topology.Order.WithTop
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Module

/-!
Norm attainment and best approximation, `fa2:p1:c14:attainment-examples`.
For norm attainment, norm the vector f in E′ by a bidual functional, then
use canonical surjectivity and the canonical isometry to pull it back to E.
For nearest points, apply the convex direct method to distance to x;
Milman–Pettis supplies reflexivity and strict convexity supplies uniqueness.
-/
namespace ExpandedFA.P1.C14AttainmentExamples
universe u v
open Set Metric
noncomputable section

theorem norm_attainment : Spec.FunctionalNormAttainment.{u, v} := by
  intro 𝕜 E _ _ _ _ h f
  change C04CanonicalMap.IsReflexive 𝕜 E at h
  obtain ⟨ξ, hξ, hξf⟩ := C05Norming.norming_functional 𝕜 (E →L[𝕜] 𝕜) f
  obtain ⟨x, hx⟩ := h ξ
  have hxn : ‖x‖ ≤ 1 := by
    calc
      ‖x‖ = ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ :=
        (C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x).symm
      _ = ‖ξ‖ := congrArg norm hx
      _ ≤ 1 := hξ
  have hfx : f x = (‖f‖ : 𝕜) := by
    change C04CanonicalMap.canonicalEvaluation 𝕜 E x f = _
    rw [hx]
    exact hξf
  refine ⟨x, hxn, ?_, ?_⟩
  · rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg f)]
  · rw [hfx, RCLike.ofReal_re]

/-- Distance to a fixed vector attains a minimum on every nonempty closed
convex set in a reflexive Banach space, even when the set is unbounded. -/
lemma reflexive_best_approximation
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (hE : C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C → ∀ x : E,
      ∃ z ∈ C, ∀ y ∈ C, ‖x - z‖ ≤ ‖x - y‖ := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hCne hCclosed hCconv x
  let Φ : E → WithTop ℝ := fun z => (dist z x : WithTop ℝ)
  have hconv : Convex ℝ {p : E × ℝ | Φ p.1 ≤ (p.2 : WithTop ℝ)} := by
    simpa [Φ] using (convexOn_univ_dist x).convex_epigraph
  have hlsc : LowerSemicontinuous Φ :=
    (WithTop.continuous_coe.comp (continuous_id.dist continuous_const)).lowerSemicontinuous
  have hproper : ∃ a : C, Φ (a : E) ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hCne
    exact ⟨⟨a, ha⟩, WithTop.coe_ne_top⟩
  have hcoercive : C14Minimization.Spec.Coercive C (fun z : C => Φ (z : E)) := by
    intro a
    refine ⟨a + ‖x‖ + 1, ?_⟩
    intro z hz
    change (a : WithTop ℝ) < (dist (z : E) x : WithTop ℝ)
    rw [WithTop.coe_lt_coe, dist_eq_norm]
    have := norm_le_norm_sub_add (z : E) x
    linarith
  obtain ⟨z, m, _, hmin⟩ := C14Minimization.convex_direct_method 𝕜 E hE C hCne hCconv hCclosed
    Φ hconv hlsc hproper (Or.inr (Or.inl hcoercive))
  refine ⟨z, z.property, ?_⟩
  intro y hy
  have hm : dist (z : E) x ≤ dist y x := WithTop.coe_le_coe.mp (hmin ⟨y, hy⟩)
  simpa only [dist_eq_norm, norm_sub_rev] using hm

/-- Strict convexity gives uniqueness only after a minimizer has been found.
The closed-ball formulation also handles radius zero without division. -/
lemma nearest_point_unique [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E] {C : Set E} (hC : Convex ℝ C)
    (x : E) {z w : E} (hz : z ∈ C) (hw : w ∈ C)
    (hzmin : ∀ y ∈ C, ‖x - z‖ ≤ ‖x - y‖)
    (hwmin : ∀ y ∈ C, ‖x - w‖ ≤ ‖x - y‖) : w = z := by
  by_contra hne
  have heq : ‖x - w‖ = ‖x - z‖ := le_antisymm (hwmin z hz) (hzmin w hw)
  have hzw : x - z ≠ x - w := by
    intro h
    exact hne (sub_right_injective h).symm
  have hstrict := norm_combo_lt_of_ne (le_refl ‖x - z‖) heq.le hzw
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hmid : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w ∈ C :=
    hC hz hw (by norm_num) (by norm_num) (by norm_num)
  have hid : (1 / 2 : ℝ) • (x - z) + (1 / 2 : ℝ) • (x - w) =
      x - ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w) := by module
  rw [hid] at hstrict
  exact (not_lt_of_ge (hzmin _ hmid)) hstrict

/-- Unique best approximation in every real or complex uniformly convex
Banach space, including zero distance, the zero space, and unbounded C. -/
theorem uniformly_convex_nearest_point :
    Spec.UniqueNearestPoint.{u, v} := by
  intro 𝕜 E _ _ _ _ huc
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro C hCne hCclosed hCconv x
  have hE := C14MilmanPettis.milman_pettis 𝕜 E huc
  obtain ⟨z, hz, hmin⟩ := reflexive_best_approximation 𝕜 E hE C hCne hCclosed hCconv x
  have hdist : ‖x - z‖ = infDist x C := by
    apply le_antisymm
    · apply (le_infDist hCne).mpr
      intro y hy
      simpa only [dist_eq_norm] using hmin y hy
    · simpa only [dist_eq_norm] using infDist_le_dist_of_mem hz
  letI : StrictConvexSpace ℝ E := C14UniformConvexity.UniformlyConvex.strictConvexSpace 𝕜 E huc
  refine ⟨z, ⟨hz, hdist, hmin⟩, ?_⟩
  intro w hw
  exact nearest_point_unique hCconv x hz hw.1 hmin hw.2.2

end
end ExpandedFA.P1.C14AttainmentExamples
