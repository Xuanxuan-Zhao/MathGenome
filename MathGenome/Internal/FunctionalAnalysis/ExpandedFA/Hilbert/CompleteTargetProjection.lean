import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.CompleteTargetProjection
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Conventions
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Projection onto complete real-convex sets in possibly incomplete inner-product
spaces (`paper.tex` 7703–7740). Mathlib's existence theorem uses a minimizing
Cauchy sequence and the parallelogram identity, and requires only `IsComplete C`.
Realification preserves the given norm and uniform structure. Two variational
inequalities give the firm bound, then Cauchy–Schwarz gives nonexpansiveness.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.CompleteTargetProjection
universe u v

theorem minimizer_iff_variational : Spec.MinimizerIffVariational.{u, v} := by
  intro 𝕜 E _ _ _ C hconvex x p hp
  let := Conventions.realification 𝕜 E
  change Convex ℝ C at hconvex
  let : Nonempty C := ⟨⟨p, hp⟩⟩
  have hmin : (∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖) ↔
      ‖x - p‖ = ⨅ z : C, ‖x - z‖ := by
    constructor
    · intro h
      apply le_antisymm
      · exact le_ciInf fun z => h z z.2
      · exact ciInf_le (f := fun z : C => ‖x - z‖) ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ ⟨p, hp⟩
    · intro h z hz
      rw [h]
      exact ciInf_le (f := fun z : C => ‖x - z‖) ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ ⟨z, hz⟩
  exact hmin.trans (norm_eq_iInf_iff_real_inner_le_zero hconvex hp)

theorem existsUnique_nearestPoint : Spec.ExistsUniqueNearestPoint.{u, v} := by
  intro 𝕜 E _ _ _ C hne hcomplete hconvex x
  let := Conventions.realification 𝕜 E
  have hconv : Convex ℝ C := hconvex
  obtain ⟨p, hp, hdist⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcomplete hconv x
  have hmin : ∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖ := by
    intro z hz
    rw [hdist]
    exact ciInf_le (f := fun z : C => ‖x - z‖) ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ ⟨z, hz⟩
  refine ⟨p, ⟨hp, hmin⟩, ?_⟩
  rintro q ⟨hq, hqmin⟩
  have hpn := (minimizer_iff_variational 𝕜 E C hconvex x p hp).mp hmin q hq
  have hqn := (minimizer_iff_variational 𝕜 E C hconvex x q hq).mp hqmin p hp
  change ⟪x - p, q - p⟫_ℝ ≤ 0 at hpn
  change ⟪x - q, p - q⟫_ℝ ≤ 0 at hqn
  have hneg : 0 ≤ ⟪x - p, p - q⟫_ℝ := by
    simpa only [show q - p = -(p - q) by abel, inner_neg_right, neg_nonpos] using hpn
  have hself : ⟪p - q, p - q⟫_ℝ ≤ 0 := calc
    ⟪p - q, p - q⟫_ℝ = ⟪(x - q) - (x - p), p - q⟫_ℝ := by
      congr 1; abel
    _ = ⟪x - q, p - q⟫_ℝ - ⟪x - p, p - q⟫_ℝ := inner_sub_left _ _ _
    _ ≤ 0 := sub_nonpos.mpr (hqn.trans hneg)
  exact (sub_eq_zero.mp (real_inner_self_nonpos.mp hself)).symm

/-- The unique nearest point, chosen in the original ambient space. -/
def convexProjection : Spec.ConvexProjectionType.{u, v} := Spec.ConvexProjectionValue

theorem convexProjection_spec : Spec.ConvexProjectionSpec.{u, v} := by
  intro 𝕜 E _ _ _ C hne hc hv x
  exact Classical.epsilon_spec (existsUnique_nearestPoint 𝕜 E C hne hc hv x).exists

theorem eq_convexProjection_iff_variational :
    Spec.EqConvexProjectionIffVariational.{u, v} := by
  intro 𝕜 E _ _ _ C hne hc hv x p
  have hproj := convexProjection_spec 𝕜 E C hne hc hv x
  constructor
  · rintro rfl
    exact ⟨hproj.1, (minimizer_iff_variational 𝕜 E C hv x _ hproj.1).mp hproj.2⟩
  · rintro ⟨hp, hvar⟩
    exact (existsUnique_nearestPoint 𝕜 E C hne hc hv x).unique
      ⟨hp, (minimizer_iff_variational 𝕜 E C hv x p hp).mpr hvar⟩ hproj

theorem convexProjection_firm_nonexpansive :
    Spec.ConvexProjectionFirmNonexpansive.{u, v} := by
  intro 𝕜 E _ _ _ C hne hc hv x y
  let := Conventions.realification 𝕜 E
  let p := convexProjection 𝕜 E C hne hc hv x
  let q := convexProjection 𝕜 E C hne hc hv y
  have hp := (convexProjection_spec 𝕜 E C hne hc hv x).1
  have hq := (convexProjection_spec 𝕜 E C hne hc hv y).1
  have hpx := ((eq_convexProjection_iff_variational 𝕜 E C hne hc hv x p).mp rfl).2 q hq
  have hqy := ((eq_convexProjection_iff_variational 𝕜 E C hne hc hv y q).mp rfl).2 p hp
  change ⟪x - p, q - p⟫_ℝ ≤ 0 at hpx
  have hpos : 0 ≤ ⟪x - p, p - q⟫_ℝ := by
    simpa only [show q - p = -(p - q) by abel, inner_neg_right, neg_nonpos] using hpx
  have hneg : ⟪y - q, p - q⟫_ℝ ≤ 0 := hqy
  have hid : ⟪x - y, p - q⟫_ℝ =
      ⟪x - p, p - q⟫_ℝ - ⟪y - q, p - q⟫_ℝ + ‖p - q‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← inner_sub_left, ← inner_add_left]
    congr 1
    abel
  change ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ
  linarith

theorem convexProjection_nonexpansive : Spec.ConvexProjectionNonexpansive.{u, v} := by
  intro 𝕜 E _ _ _ C hne hc hv x y
  let P := convexProjection 𝕜 E C hne hc hv
  have hfirm := convexProjection_firm_nonexpansive 𝕜 E C hne hc hv x y
  have hcs : RCLike.re ⟪x - y, P x - P y⟫_𝕜 ≤ ‖x - y‖ * ‖P x - P y‖ :=
    re_inner_le_norm _ _
  have hsq : ‖P x - P y‖ ^ 2 ≤ ‖x - y‖ * ‖P x - P y‖ := hfirm.trans hcs
  change ‖P x - P y‖ ≤ ‖x - y‖
  nlinarith [norm_nonneg (P x - P y), norm_nonneg (x - y)]

end ExpandedFA.Hilbert.CompleteTargetProjection
