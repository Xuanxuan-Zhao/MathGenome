import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UcQuotients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import Mathlib.Tactic.Linarith

/-! Uniform convexity of the distance quotient, without completeness.
Approximate representatives suffice: normalize lifts in a ball of radius
`1 + d / 4`, using the original space's uniform gap at half the requested
separation. The positive gap absorbs the excess in the lifts' norms.
-/
namespace ExpandedFA.P1.UcQuotients

universe u v

/-- The quotient by a closed subspace of a uniformly convex normed space
is uniformly convex for its distance norm. -/
theorem uniformlyConvex_quotient : Spec.UniformlyConvexQuotient.{u,v} := by
  intro 𝕜 E _ _ _ M hM hE
  letI : IsClosed (M : Set E) := hM
  change C14UniformConvexity.UniformlyConvex 𝕜 (E ⧸ M)
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : UniformConvexSpace E :=
    (C14UniformConvexity.native_iff_uniformlyConvex 𝕜 E).mpr hE
  intro ε hε _
  obtain ⟨δ, hδ, hgap⟩ :=
    exists_forall_closed_ball_dist_add_le_two_sub E (show 0 < ε / 2 by linarith)
  let d := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hdδ : d ≤ δ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  let r := 1 + d / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hr2 : r ≤ 2 := by dsimp [r]; linarith
  refine ⟨d / 4, by linarith, ?_⟩
  intro u v hu hv huv
  obtain ⟨x, hx, hxn⟩ := Submodule.Quotient.norm_mk_lt u (show 0 < d / 4 by linarith)
  obtain ⟨y, hy, hyn⟩ := Submodule.Quotient.norm_mk_lt v (show 0 < d / 4 by linarith)
  change M.mkQ x = u at hx
  change M.mkQ y = v at hy
  have hxr : ‖x‖ ≤ r := by dsimp [r]; linarith
  have hyr : ‖y‖ ≤ r := by dsimp [r]; linarith
  have hsep : ε ≤ ‖x - y‖ := by
    calc
      ε ≤ ‖u - v‖ := huv
      _ = ‖M.mkQ (x - y)‖ := by rw [map_sub, hx, hy]
      _ ≤ ‖x - y‖ := Submodule.Quotient.norm_mk_le M _
  have hnx : ‖r⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (inv_mul_le_one₀ hr).mpr hxr
  have hny : ‖r⁻¹ • y‖ ≤ 1 := by
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hr.le)]
    exact (inv_mul_le_one₀ hr).mpr hyr
  have hnsep : ε / 2 ≤ ‖r⁻¹ • x - r⁻¹ • y‖ := by
    rw [← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [← div_eq_inv_mul, le_div_iff₀ hr]
    have := mul_le_mul_of_nonneg_left hr2 (show 0 ≤ ε / 2 by linarith)
    linarith
  have hsum := hgap hnx hny hnsep
  rw [← smul_add, norm_smul_of_nonneg (inv_nonneg.mpr hr.le),
    ← div_eq_inv_mul, div_le_iff₀ hr] at hsum
  have hsum' : ‖x + y‖ ≤ (2 - d) * r := by nlinarith
  have hsum'' : ‖x + y‖ ≤ 2 - d / 2 := by
    dsimp [r] at hsum'
    nlinarith [sq_nonneg d]
  rw [C14UniformConvexity.norm_midpoint_eq_half]
  have hquot : ‖u + v‖ ≤ ‖x + y‖ := by
    calc
      ‖u + v‖ = ‖M.mkQ (x + y)‖ := by rw [map_add, hx, hy]
      _ ≤ ‖x + y‖ := Submodule.Quotient.norm_mk_le M _
  linarith

end ExpandedFA.P1.UcQuotients
