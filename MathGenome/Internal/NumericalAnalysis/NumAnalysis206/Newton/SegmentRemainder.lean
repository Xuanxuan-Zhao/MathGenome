import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.SegmentRemainder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

open Set

namespace NumAnalysis206.Newton

/-- The quadratic remainder bound on a convex subset of the open differentiability
 domain. A real segment is used even when the scalar field is complex. -/
theorem segment_remainder :
    Specs.NumAnalysis206.Newton.SegmentRemainderStatement := by
  intro 𝕜 _ X Y _ _ _ _ _ _
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  let : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  intro F U D L hU hF hDU hD hL hLip x hx y hy
  let p : ℝ → X := AffineMap.lineMap x y
  let d := y - x
  let A := fderiv 𝕜 F x
  let r : ℝ → Y := fun t => F (p t) - F x - t • A d
  let r' : ℝ → Y := fun t => (fderiv 𝕜 F (p t) - A) d
  have hp : MapsTo p (Icc 0 1) D := hD.mapsTo_lineMap hx hy
  have hr : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt r (r' t) t := by
    intro t ht
    have hf := (hF (p t) (hDU (hp ht))).differentiableAt (hU.mem_nhds (hDU (hp ht)))
    have hfpath := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := x) (b := y))
    convert (hfpath.sub_const (F x)).sub ((hasDerivAt_id t).smul_const (A d)) using 1 <;>
      simp [r, r', A, d, p] <;> rfl
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖r' t‖ ≤ L * ‖d‖ ^ 2 * t := by
    intro t ht
    have hnorm : ‖p t - x‖ = t * ‖d‖ := by
      simp [p, AffineMap.lineMap_apply_module', d, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
    calc
      ‖r' t‖ ≤ ‖fderiv 𝕜 F (p t) - A‖ * ‖d‖ :=
        (fderiv 𝕜 F (p t) - A).le_opNorm d
      _ ≤ (L * ‖p t - x‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hLip (p t) (hp (Ico_subset_Icc_self ht)) x hx) (norm_nonneg d)
      _ = L * ‖d‖ ^ 2 * t := by rw [hnorm]; ring
  have hB : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (L / 2) * ‖d‖ ^ 2 * s ^ 2)
      (L * ‖d‖ ^ 2 * t) t := by
    intro t
    convert ((hasDerivAt_id t).pow 2).const_mul ((L / 2) * ‖d‖ ^ 2) using 1 <;> dsimp <;> ring
  have H := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t ht => (hr t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hr t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (B := fun t : ℝ => (L / 2) * ‖d‖ ^ 2 * t ^ 2)
    (by simp [r, p]) hB hbound (x := 1) (by constructor <;> norm_num)
  simpa [r, p, d] using H

end NumAnalysis206.Newton
