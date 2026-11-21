import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.AuxiliaryDerivativeBound
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.QuantitativeBloch
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.AuxiliaryExcludedDisks
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Auxiliary estimates in the Schottky proof, paper.tex:4231–4237.
Bloch supplies a disk of radius (1 - |a|)|g'(a)|/64 in the auxiliary
image. The excluded-disk theorem makes that radius less than two.
On a proper closed subdisk the resulting derivative bound is uniform,
so the mean-value inequality gives the estimate from the center.
-/

namespace D12Complex.AuxiliaryDerivativeBound
open Set Metric

lemma centered_disk_subset_unit_disk (a : ℂ) :
    ball a (1 - ‖a‖) ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  rw [mem_ball_zero_iff]
  have hz' : ‖z - a‖ < 1 - ‖a‖ := by
    simpa [mem_ball, dist_eq_norm] using hz
  have htri := norm_le_norm_sub_add z a
  linarith

/-- The estimate holds for every given auxiliary transform, including at
points where its derivative vanishes. -/
theorem derivative_bound :
    Specs.D12Complex.Ch23.AuxiliaryDerivativeBound.derivative_bound_type := by
  intro f g _hf _hzero hone hg hidentity a ha
  have ha' : ‖a‖ < 1 := by simpa using ha
  have hR : 0 < 1 - ‖a‖ := sub_pos.mpr ha'
  by_cases hd : deriv g a = 0
  · simp only [hd, norm_zero]
    positivity
  have hg' : HolomorphicOn (ball a (1 - ‖a‖)) g :=
    ⟨isOpen_ball, fun z hz => hg.2 z (centered_disk_subset_unit_disk a hz)⟩
  obtain ⟨b, s, c, inv, _hs, hsub, _hi, hcover, _hrest⟩ :=
    QuantitativeBloch.scaled a (1 - ‖a‖) g hR hg' hd
  have hn := AuxiliaryExcludedDisks.no_disk_of_transform
    (ball 0 1) f g hone hidentity c
  have hlt : (1 - ‖a‖) * ‖deriv g a‖ / 64 < 2 := by
    by_contra h
    apply hn
    exact (ball_subset_ball (le_of_not_gt h)).trans
      (hcover.trans (image_mono (hsub.trans (centered_disk_subset_unit_disk a))))
  apply (le_div_iff₀ hR).2
  nlinarith

/-- A pointwise derivative estimate gives a bound on each proper closed
subdisk, using only differentiability on the open unit disk. -/
lemma radial_bound_of_derivative_bound {g : ℂ → ℂ}
    (hg : HolomorphicOn (ball 0 1) g)
    (hder : ∀ a ∈ ball (0 : ℂ) 1, ‖deriv g a‖ ≤ 128 / (1 - ‖a‖))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖g z‖ ≤ ‖g 0‖ + 128 * r / (1 - r) := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball 0 1 := by
    intro a ha
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp ha).trans_lt hr1)
  have hd : ∀ a ∈ closedBall (0 : ℂ) r, ‖deriv g a‖ ≤ 128 / (1 - r) := by
    intro a ha
    apply (hder a (hsub ha)).trans
    apply div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hr1)
    linarith [mem_closedBall_zero_iff.mp ha]
  have hmean := (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_deriv_le
    (fun a ha => hg.2 a (hsub ha)) hd (mem_closedBall_self hr)
    (mem_closedBall_zero_iff.mpr hz)
  have hC : 0 ≤ 128 / (1 - r) := by positivity
  calc
    ‖g z‖ ≤ ‖g z - g 0‖ + ‖g 0‖ := norm_le_norm_sub_add _ _
    _ ≤ 128 / (1 - r) * ‖z‖ + ‖g 0‖ := by
      simpa using add_le_add_right hmean ‖g 0‖
    _ ≤ 128 / (1 - r) * r + ‖g 0‖ := by
      linarith [mul_le_mul_of_nonneg_left hz hC]
    _ = ‖g 0‖ + 128 * r / (1 - r) := by ring

/-- The required bound for the chosen auxiliary function on |z| ≤ r < 1. -/
theorem radial_bound :
    Specs.D12Complex.Ch23.AuxiliaryDerivativeBound.radial_bound_type := by
  intro f g hf hzero hone hg hidentity r hr hr1 z hz
  exact radial_bound_of_derivative_bound hg
    (derivative_bound f g hf hzero hone hg hidentity) hr hr1 hz

end D12Complex.AuxiliaryDerivativeBound
