import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.MinimumDisplacement
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Geometry.FirmProjectionAndOrbitGaps
import Mathlib.Analysis.Convex.Topology

/-!
Minimum displacement without intersection or distance attainment.
Start a comparison orbit at b ∈ C₂ from a pair with ‖b-a‖ close to the
infimum. Nearest-point minimality bounds all its gaps by ‖b-a‖, and the
accepted firm-orbit comparison transfers this bound asymptotically to any
orbit. All even gaps already have norm at least the infimum. Finally the
projection inequality on closure (C₂-C₁) bounds the squared distance from
the minimum vector by the excess squared norm, which tends to zero.
-/
noncomputable section
open Filter
open scoped Pointwise InnerProductSpace
namespace ExpandedFA.Geometry.MinimumDisplacement
universe u v

abbrev IsAlternatingOrbit := @FirmProjectionAndOrbitGaps.Spec.IsAlternatingOrbit

/-- An alternating orbit with any prescribed initial point. -/
def orbit {H : Type v} (P₁ P₂ : H → H) (x : H) : ℕ → H
  | 0 => x
  | n+1 => if n % 2 = 0 then P₁ (orbit P₁ P₂ x n) else P₂ (orbit P₁ P₂ x n)

theorem orbit_isAlternating {H : Type v} (P₁ P₂ : H → H) (x : H) :
    IsAlternatingOrbit P₁ P₂ (orbit P₁ P₂ x) := fun _ => rfl

theorem odd_step {H : Type v} {P₁ P₂ : H → H} {u : ℕ → H}
    (hu : IsAlternatingOrbit P₁ P₂ u) (n : ℕ) :
    u (2*n+1) = P₁ (u (2*n)) := by simpa using hu (2*n)

theorem even_step {H : Type v} {P₁ P₂ : H → H} {u : ℕ → H}
    (hu : IsAlternatingOrbit P₁ P₂ u) (n : ℕ) :
    u (2*n+2) = P₂ (u (2*n+1)) := by
  simpa [show 2*n+1+1 = 2*n+2 by omega] using hu (2*n+1)

section Geometry
variable (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  (C₁ C₂ : Set H) (hne₁ : C₁.Nonempty) (hne₂ : C₂.Nonempty)
  (hc₁ : IsClosed C₁) (hc₂ : IsClosed C₂)
  (hv₁ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₁)
  (hv₂ : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C₂)

local notation "P₁" => Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₁ hne₁ hc₁ hv₁
local notation "P₂" => Hilbert.Projection.Spec.ConvexProjectionValue 𝕜 H C₂ hne₂ hc₂ hv₂

include hv₁ hv₂ hc₁ hc₂

theorem gap_mem (u : ℕ → H) (hu : IsAlternatingOrbit P₁ P₂ u) (n : ℕ) :
    u (2*n+2) - u (2*n+1) ∈ C₂ - C₁ := by
  apply Set.sub_mem_sub
  · rw [even_step hu]
    exact (Hilbert.Projection.convexProjection_spec 𝕜 H C₂ hne₂ hc₂ hv₂ _).1
  · rw [odd_step hu]
    exact (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁ _).1

/-- A comparison orbit started at b ∈ C₂ has every even gap bounded
by the length of any pair a ∈ C₁, b ∈ C₂. -/
theorem comparison_gap_bound (a b : H) (ha : a ∈ C₁) (hb : b ∈ C₂) :
    ∀ n, ‖orbit P₁ P₂ b (2*n+2) - orbit P₁ P₂ b (2*n+1)‖ ≤ ‖b-a‖ := by
  let v := orbit P₁ P₂ b
  have hv : IsAlternatingOrbit P₁ P₂ v := orbit_isAlternating P₁ P₂ b
  have hm₁ (n : ℕ) : v (2*n+1) ∈ C₁ := by
    rw [odd_step hv]
    exact (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁ _).1
  have hm₂ (n : ℕ) : v (2*n) ∈ C₂ := by
    cases n with
    | zero => exact hb
    | succ n =>
      rw [show 2*(n+1) = 2*n+2 by omega, even_step hv]
      exact (Hilbert.Projection.convexProjection_spec 𝕜 H C₂ hne₂ hc₂ hv₂ _).1
  have hfirst : ‖v 1 - v 0‖ ≤ ‖b-a‖ := by
    have hh := (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁ b).2 a ha
    simpa [v, orbit, norm_sub_rev] using hh
  have hhalf (n : ℕ) : ‖v (2*n+2) - v (2*n+1)‖ ≤ ‖v (2*n+1) - v (2*n)‖ := by
    rw [even_step hv]
    simpa only [norm_sub_rev] using
      (Hilbert.Projection.convexProjection_spec 𝕜 H C₂ hne₂ hc₂ hv₂
        (v (2*n+1))).2 (v (2*n)) (hm₂ n)
  have hnext (n : ℕ) : ‖v (2*(n+1)+1) - v (2*(n+1))‖ ≤
      ‖v (2*n+2) - v (2*n+1)‖ := by
    rw [odd_step hv, show 2*(n+1) = 2*n+2 by omega]
    simpa only [norm_sub_rev] using
      (Hilbert.Projection.convexProjection_spec 𝕜 H C₁ hne₁ hc₁ hv₁
        (v (2*n+2))).2 (v (2*n+1)) (hm₁ n)
  intro n
  change ‖v (2*n+2) - v (2*n+1)‖ ≤ ‖b-a‖
  induction n with
  | zero => exact (hhalf 0).trans hfirst
  | succ n ih => exact (hhalf (n+1)).trans ((hnext n).trans ih)

/-- The infimum is approached by every orbit, using the accepted vanishing
comparison of two orbits. No compactness of the orbit is used. -/
theorem gap_norm_tendsto (u : ℕ → H) (hu : IsAlternatingOrbit P₁ P₂ u) :
    Tendsto (fun n => ‖u (2*n+2) - u (2*n+1)‖) atTop
      (nhds (Spec.setDistance C₁ C₂)) := by
  have hdiff : (C₂ - C₁).Nonempty := by
    obtain ⟨a, ha⟩ := hne₁
    obtain ⟨b, hb⟩ := hne₂
    exact ⟨b-a, Set.sub_mem_sub hb ha⟩
  apply tendsto_order.2
  constructor
  · intro r hr
    apply Eventually.of_forall
    intro n
    have hlow := Metric.infDist_le_dist_of_mem
      (x := (0 : H)) (gap_mem 𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ u hu n)
    exact hr.trans_le (by simpa only [Spec.setDistance, dist_zero_left] using hlow)
  · intro r hr
    let t := (Spec.setDistance C₁ C₂ + r) / 2
    have hδt : Spec.setDistance C₁ C₂ < t := by dsimp [t]; linarith
    have htr : t < r := by dsimp [t]; linarith
    obtain ⟨w, hw, hwt⟩ := (Metric.infDist_lt_iff hdiff).mp hδt
    obtain ⟨b, hb, a, ha, rfl⟩ := Set.mem_sub.mp hw
    have hbat : ‖b-a‖ < t := by simpa only [dist_zero_left] using hwt
    let v := orbit P₁ P₂ b
    have hv : IsAlternatingOrbit P₁ P₂ v := orbit_isAlternating P₁ P₂ b
    have hcompare := FirmProjectionAndOrbitGaps.even_gap_difference_tendsto_zero
      𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ u v hu hv
    have hsmall : ∀ᶠ n in atTop,
        ‖(u (2*n+2) - u (2*n+1)) - (v (2*n+2) - v (2*n+1))‖ < r-t := by
      have hh := (tendsto_order.1 hcompare.norm).2 (r-t) (by simpa using sub_pos.mpr htr)
      exact hh
    filter_upwards [hsmall] with n hn
    have hbound := comparison_gap_bound 𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ a b ha hb n
    change ‖v (2*n+2) - v (2*n+1)‖ ≤ ‖b-a‖ at hbound
    have htriangle := norm_le_norm_sub_add
      (u (2*n+2) - u (2*n+1)) (v (2*n+2) - v (2*n+1))
    linarith

end Geometry

/-- Full minimum-displacement theorem for real and complex Hilbert spaces. -/
theorem minimum_displacement : Spec.MinimumDisplacement.{u, v} := by
  intro 𝕜 H _ _ _ _ C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂
  let := Hilbert.Conventions.realification 𝕜 H
  let D := closure (C₂ - C₁)
  have hdiff : (C₂ - C₁).Nonempty := by
    obtain ⟨a, ha⟩ := hne₁
    obtain ⟨b, hb⟩ := hne₂
    exact ⟨b-a, Set.sub_mem_sub hb ha⟩
  have hDne : D.Nonempty := hdiff.closure
  have hDconv : Hilbert.Conventions.Spec.RealConvexValue 𝕜 H D := by
    change Convex ℝ D
    exact ((show Convex ℝ C₂ from hv₂).sub (show Convex ℝ C₁ from hv₁)).closure
  let p := Spec.minimumVector C₁ C₂
  have hp : p ∈ D ∧ ∀ w ∈ D, ‖p‖ ≤ ‖w‖ := by
    have hh := Hilbert.Projection.convexProjection_spec 𝕜 H D hDne isClosed_closure hDconv 0
    change p ∈ D ∧ ∀ w ∈ D, ‖(0:H)-p‖ ≤ ‖(0:H)-w‖ at hh
    simpa only [zero_sub, norm_neg] using hh
  have hnorm : ‖p‖ = Spec.setDistance C₁ C₂ := by
    apply le_antisymm
    · apply (Metric.le_infDist hdiff).2
      intro w hw
      simpa using hp.2 w (subset_closure hw)
    · have hh := Metric.infDist_le_dist_of_mem (x := (0:H)) hp.1
      simpa only [D, Spec.setDistance, Metric.infDist_closure, dist_zero_left] using hh
  refine ⟨hp, hnorm, ?_⟩
  intro u hu
  have hnorms := gap_norm_tendsto 𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ u hu
  refine ⟨hnorms, ?_⟩
  have hvar := (Hilbert.Projection.minimizer_iff_variational 𝕜 H D hDconv 0 p hp.1).mp
    (by simpa only [zero_sub, norm_neg] using hp.2)
  have hbound (w : H) (hw : w ∈ D) : ‖w-p‖ ^ 2 ≤ ‖w‖ ^ 2 - ‖p‖ ^ 2 := by
    have hh := hvar w hw
    change ⟪(0:H)-p, w-p⟫_ℝ ≤ 0 at hh
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      ← real_inner_comm p w] at hh
    rw [norm_sub_sq (𝕜 := ℝ), RCLike.re_to_real]
    linarith
  have hsq : Tendsto (fun n => ‖u (2*n+2) - u (2*n+1)‖ ^ 2 - ‖p‖ ^ 2)
      atTop (nhds 0) := by
    have hh := (hnorms.pow 2).sub_const (‖p‖ ^ 2)
    simpa only [← hnorm, sub_self] using hh
  have hzero : Tendsto (fun n => ‖(u (2*n+2) - u (2*n+1))-p‖ ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => ?_) hsq
    exact hbound _ (subset_closure
      (gap_mem 𝕜 H C₁ C₂ hne₁ hne₂ hc₁ hc₂ hv₁ hv₂ u hu n))
  have hnormzero : Tendsto (fun n => ‖(u (2*n+2) - u (2*n+1))-p‖)
      atTop (nhds 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hzero
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnormzero

end ExpandedFA.Geometry.MinimumDisplacement
