import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalLipschitz
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.DerivativeCriterion
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! The derivative criterion of paper.tex, d13:03:derivative-bound. -/

noncomputable section
open Set Metric Filter
open scoped NNReal Topology

namespace D13Unified
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The mean-value inequality on a convex state set, uniformly in the permitted
other variables. This also covers closed balls and their boundary points.
The continuity assumption on the partial derivative can be omitted. -/
theorem state_lipschitz_of_derivative_bound
    (f : ℝ → E → P → E) (D : ℝ → E → P → E →L[ℝ] E)
    (T : Set ℝ) (B : Set E) (Q : Set P) (L : ℝ)
    (hB : Convex ℝ B)
    (hD : ∀ t ∈ T, ∀ x ∈ B, ∀ p ∈ Q,
      HasFDerivWithinAt (fun y => f t y p) (D t x p) B x)
    (hbound : ∀ t ∈ T, ∀ x ∈ B, ∀ p ∈ Q, ‖D t x p‖ ≤ L) :
    ∀ p ∈ Q, StateLipschitzOn (fun t x => f t x p) T B L := by
  intro p hp t ht x hx y hy
  exact hB.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => hD t ht z hz p hp) (fun z hz => hbound t ht z hz p hp) hy hx

/-- A C¹ map on an open set admits a Lipschitz ball contained in that set.
This uses strict differentiability, so no compactness or completeness
assumptions on the spaces are necessary. -/
private theorem exists_lipschitz_ball
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X → Y} {U : Set X} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {z : X} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball z r ⊆ U ∧
      ∃ K : ℝ≥0, LipschitzOnWith K f (ball z r) := by
  obtain ⟨K, V, hV, hLip⟩ := (hf.contDiffAt (hU.mem_nhds hz)).exists_lipschitzOnWith
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (hU.mem_nhds hz))
  exact ⟨r, hr, fun x hx => (hsub hx).2, K,
    hLip.mono (fun x hx => (hsub hx).1)⟩

/-- Every jointly C¹ ODE field is locally Lipschitz in state uniformly in time,
on product neighborhoods contained in its original domain. -/
theorem ODE.locallyLipschitzInState_of_contDiffOn (F : ODE E)
    (hf : ContDiffOn ℝ 1 (fun z : ℝ × E => F.eval z.1 z.2) F.domain) :
    F.LocallyLipschitzInState := by
  intro s ξ hs
  obtain ⟨r, hr, hdom, K, hLip⟩ := exists_lipschitz_ball F.isOpen_domain hf hs
  refine ⟨r, r, K, hr, hr, K.coe_nonneg, ?_, ?_⟩
  · simpa only [ball_prod_same] using hdom
  · intro t ht x hx y hy
    have hx' : (t, x) ∈ ball (s, ξ) r := by
      rw [← ball_prod_same]; exact ⟨ht, hx⟩
    have hy' : (t, y) ∈ ball (s, ξ) r := by
      rw [← ball_prod_same]; exact ⟨ht, hy⟩
    simpa [Prod.norm_def] using
      (lipschitzOnWith_iff_norm_sub_le.mp hLip hx' hy')

/-- Nearby parameters share the radii and Lipschitz constant supplied by joint
C¹ regularity; each comparison uses one fixed parameter. -/
theorem ParameterODE.locallyLipschitzInState_of_contDiffOn (F : ParameterODE E P)
    (hf : ContDiffOn ℝ 1
      (fun z : (ℝ × E) × P => F.eval z.1.1 z.1.2 z.2) F.domain) :
    F.LocallyLipschitzInState := by
  intro s ξ p hs
  obtain ⟨r, hr, hdom, K, hLip⟩ := exists_lipschitz_ball F.isOpen_domain hf hs
  refine ⟨r, r, r, K, hr, hr, hr, K.coe_nonneg, ?_, ?_⟩
  · simpa only [ball_prod_same] using hdom
  · intro q hq t ht x hx y hy
    have hx' : ((t, x), q) ∈ ball ((s, ξ), p) r := by
      rw [← ball_prod_same, ← ball_prod_same]; exact ⟨⟨ht, hx⟩, hq⟩
    have hy' : ((t, y), q) ∈ ball ((s, ξ), p) r := by
      rw [← ball_prod_same, ← ball_prod_same]; exact ⟨⟨ht, hy⟩, hq⟩
    simpa [Prod.norm_def, ParameterODE.eval] using
      (lipschitzOnWith_iff_norm_sub_le.mp hLip hx' hy')

/-- Autonomous C¹ fields satisfy the common predicate after conversion. -/
theorem AutonomousODE.locallyLipschitzInState_of_contDiffOn (F : AutonomousODE E)
    (hf : ContDiffOn ℝ 1 F.eval F.domain) : F.toODE.LocallyLipschitzInState := by
  intro s ξ hs
  obtain ⟨r, hr, hdom, K, hLip⟩ := exists_lipschitz_ball F.isOpen_domain hf hs
  refine ⟨1, r, K, zero_lt_one, hr, K.coe_nonneg, ?_, ?_⟩
  · intro tx htx
    exact hdom htx.2
  · intro t ht x hx y hy
    exact lipschitzOnWith_iff_norm_sub_le.mp hLip hx hy

end D13Unified
