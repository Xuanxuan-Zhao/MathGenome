import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.FirmProjectionAndOrbitGaps
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Projection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
Firm nonexpansiveness and comparison of alternating projection orbits.
The two-point variational bound is supplied by the accepted complete-target
projection theorem. Expanding the residual square gives the firm estimate.
Its stepwise energy decrease telescopes; bounded sums of nonnegative squared
increments imply summability and hence convergence of the increments to zero.
-/

noncomputable section
open Filter
open scoped InnerProductSpace

namespace ExpandedFA.Geometry.FirmProjectionAndOrbitGaps
universe u v

theorem firm_projection_estimate : Spec.FirmProjectionEstimate.{u, v} := by
  intro 𝕜 H _ _ _ _ C hne hc hv x y
  let P := Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C hne hc hv
  have hfirm := Hilbert.CompleteTargetProjection.convexProjection_firm_nonexpansive
    𝕜 H C hne hc.isComplete hv x y
  change ‖P x - P y‖ ^ 2 ≤ RCLike.re ⟪x - y, P x - P y⟫_𝕜 at hfirm
  change ‖P x - P y‖ ^ 2 + ‖(x - P x) - (y - P y)‖ ^ 2 ≤ ‖x - y‖ ^ 2
  have hid : (x - P x) - (y - P y) = (x - y) - (P x - P y) := by abel
  rw [hid, norm_sub_sq (𝕜 := 𝕜) (x-y) (P x-P y)]
  linarith

/-- Telescoping energy loss for any sequence satisfying the firm step bound. -/
theorem sum_sq_increments_le {H : Type v} [NormedAddCommGroup H]
    (a : ℕ → H)
    (hstep : ∀ n, ‖a (n+1)‖ ^ 2 + ‖a (n+1) - a n‖ ^ 2 ≤ ‖a n‖ ^ 2)
    (N : ℕ) :
    (∑ j ∈ Finset.range N, ‖a (j+1) - a j‖ ^ 2) ≤ ‖a 0‖ ^ 2 - ‖a N‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs := hstep N
    linarith

/-- The same projection is applied to both orbits at every step. -/
theorem alternating_orbit_step (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
    (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
    (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
    (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂)
    (u v : ℕ → H)
    (hu : Spec.IsAlternatingOrbit
      (Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁)
      (Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂) u)
    (hv : Spec.IsAlternatingOrbit
      (Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁)
      (Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂) v)
    (n : ℕ) :
    ‖u (n+1) - v (n+1)‖ ^ 2 +
      ‖(u (n+1) - v (n+1)) - (u n - v n)‖ ^ 2 ≤ ‖u n - v n‖ ^ 2 := by
  have hres : ∀ (P : H → H),
      (P (u n) - P (v n)) - (u n - v n) =
        -((u n - P (u n)) - (v n - P (v n))) := by
    intro P
    abel
  rw [hu n, hv n]
  by_cases h : n % 2 = 0
  · simp only [ite_eq_left h, hres, norm_neg]
    exact firm_projection_estimate 𝕜 H C₁ hne₁ hc₁ hv₁ (u n) (v n)
  · simp only [ite_eq_right h, hres, norm_neg]
    exact firm_projection_estimate 𝕜 H C₂ hne₂ hc₂ hv₂ (u n) (v n)

theorem alternating_orbit_comparison : Spec.AlternatingOrbitComparison.{u, v} := by
  intro 𝕜 H _ _ _ _ C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ P₁ P₂ u v hu hv N
  have hstep := alternating_orbit_step 𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ u v hu hv
  have hs := sum_sq_increments_le (fun n => u n - v n) hstep N
  exact ⟨hs, hs.trans (sub_le_self _ (sq_nonneg _))⟩

theorem even_gap_difference_tendsto_zero : Spec.EvenGapDifferenceTendstoZero.{u, v} := by
  intro 𝕜 H _ _ _ _ C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ P₁ P₂ u v hu hv
  let d : ℕ → H := fun n => (u (n+1) - v (n+1)) - (u n - v n)
  have hsum : Summable (fun n => ‖d n‖ ^ 2) := by
    apply summable_of_sum_range_le (fun n => sq_nonneg _) (c := ‖u 0 - v 0‖ ^ 2)
    intro N
    exact (alternating_orbit_comparison
      𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ u v hu hv N).2
  have hd : Tendsto d atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsum.tendsto_atTop_zero
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  have hidx : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2*n+1; omega) tendsto_id
  have heq : (fun n => (u (2*n+2) - u (2*n+1)) -
      (v (2*n+2) - v (2*n+1))) = (fun n => d (2*n+1)) := by
    funext n
    dsimp [d]
    have hi : 2*n+1+1 = 2*n+2 := by omega
    rw [hi]
    abel
  rw [heq]
  exact hd.comp hidx

end ExpandedFA.Geometry.FirmProjectionAndOrbitGaps
