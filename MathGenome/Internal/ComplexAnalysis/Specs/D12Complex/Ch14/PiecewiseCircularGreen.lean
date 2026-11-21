import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularCornerRounding
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.ComplexGreenBridge

/-! The independent full statement of paper.tex:2669–2678, first rounding limit.
Only geometric hypotheses are imposed on the supplied circular arc arrays.
The full theorem is stated independently of its proper analytic components. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff Topology Interval

namespace Specs.D12Complex.Ch14.PiecewiseCircularGreen
open _root_.D12Complex
open _root_.D12Complex.CircularExhaustion
open _root_.D12Complex.CircularCornerRounding
open _root_.D12Complex.ComplexGreenBridge
open Specs.D04.C12.ClassicalRegularDomains.Model

/-- The full zero-flux theorem, on exactly the supplied finite arrays. Empty and
 disconnected domains, full circles, and artificial arc endpoints are allowed. -/
def piecewise_circular_green_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
    ∀ (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ),
    (∀ i, 0 < radius i ∧ start i < stop i ∧ stop i - start i ≤ 2 * Real.pi) →
    (∀ i, sign i = 1 ∨ sign i = -1) →
    frontier U = ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i) →
    (∀ i j, i ≠ j → Disjoint
      (arcParam (center i) (radius i) '' Ioo (start i) (stop i))
      (arcParam (center j) (radius j) '' Ioo (start j) (stop j))) →
    (∀ i, InjOn (arcParam (center i) (radius i)) (Ioo (start i) (stop i))) →
    (∀ i t, t ∈ Ioo (start i) (stop i) →
      ∃ W : Set ℂ, IsOpen W ∧ arcParam (center i) (radius i) t ∈ W ∧
        ∀ z ∈ W, z ∈ U ↔ sign i * (‖z - center i‖ ^ 2 - radius i ^ 2) < 0) →
    ∀ (O : Set ℂ), IsOpen O → closure U ⊆ O →
    ∀ (u v : ℂ → ℝ), ContDiffOn ℝ 2 u O → ContDiffOn ℝ 2 v O →
    (∀ z ∈ U, coordinateLaplacian u z = 0) →
    (∀ z ∈ U, coordinateLaplacian v z = 0) →
    (∀ i, IntervalIntegrable (fun t =>
      (u (arcParam (center i) (radius i) t) *
        inner ℝ (gradient v (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam (center i) (radius i) t) *
        inner ℝ (gradient u (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i)
      volume (start i) (stop i)) ∧
    (∑ i, ∫ t in (start i)..(stop i),
      (u (arcParam (center i) (radius i) t) *
        inner ℝ (gradient v (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam (center i) (radius i) t) *
        inner ℝ (gradient u (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i) = 0

/-- Proper analytic part: integrability needs just the closed boundary cover and
 C2 on an open neighborhood of its closure; no harmonicity or Green identity. -/
def circular_flux_integrable_type : Prop :=
  ∀ (U O : Set ℂ), IsOpen O → closure U ⊆ O →
    ∀ (u v : ℂ → ℝ), ContDiffOn ℝ 2 u O → ContDiffOn ℝ 2 v O →
    ∀ (n : ℕ) (center : Fin n → ℂ) (radius start stop sign : Fin n → ℝ),
    (∀ i, start i ≤ stop i) →
    frontier U = ⋃ i, arcParam (center i) (radius i) '' Icc (start i) (stop i) →
    ∀ i, IntervalIntegrable (fun t =>
      (u (arcParam (center i) (radius i) t) *
        inner ℝ (gradient v (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I)) -
       v (arcParam (center i) (radius i) t) *
        inner ℝ (gradient u (arcParam (center i) (radius i) t))
          (sign i • Complex.exp ((t : ℂ) * Complex.I))) * radius i)
      volume (start i) (stop i)

/-- Uniform compact normal-flux bound, including all normals of norm at most one. -/
def compact_scalar_flux_bound_type : Prop :=
  ∀ (K O : Set ℂ), IsCompact K → IsOpen O → K ⊆ O →
    ∀ (u v : ℂ → ℝ), ContDiffOn ℝ 2 u O → ContDiffOn ℝ 2 v O →
    ∃ M > 0, ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M

/-- The genuine D04 density Green identity on actual rounded domains. This is a
 proper part: conversion to supplied scalar circle intervals is not asserted. -/
def rounded_harmonic_green_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
    ∀ (O : Set ℂ), IsOpen O → closure U ⊆ O →
    ∀ (u v : ℂ → ℝ), ContDiffOn ℝ 2 u O → ContDiffOn ℝ 2 v O →
    (∀ z ∈ U, coordinateLaplacian u z = 0) →
    (∀ z ∈ U, coordinateLaplacian v z = 0) →
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ V : Set ℂ, ∃ hV : IsRoundingAt U V J C ε,
          Specs.D04.C12.GaussDivergenceTheorem.Model.HasDensityIntegral (d := 1)
            (_root_.D12Complex.ComplexGreenBridge.boundaryFlux hV.2.2.1 u v) 0 ∧
          Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model.boundaryIntegral
            (_root_.D12Complex.ComplexGreenBridge.boundaryFlux hV.2.2.1 u v) = 0

/-- A proper proved component of the unchanged full obligation. -/
def scalar_arclength_substitution_monotone_type : Prop :=
  ∀
    {a b : ℝ} {φ : ℝ → ℝ} {γ : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hφd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ φ t)
    (hm : MonotoneOn φ (Icc a b))
    (hγd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ (φ t))
    (hint : IntervalIntegrable (fun s => w s * ‖deriv γ s‖) volume (φ a) (φ b)),
    IntervalIntegrable (fun t => w (φ t) * ‖deriv (γ ∘ φ) t‖) volume a b ∧
      (∫ t in a..b, w (φ t) * ‖deriv (γ ∘ φ) t‖) =
        ∫ s in φ a..φ b, w s * ‖deriv γ s‖

/-- A proper proved component of the unchanged full obligation. -/
def scalar_arclength_substitution_antitone_type : Prop :=
  ∀
    {a b : ℝ} {φ : ℝ → ℝ} {γ : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hφd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ φ t)
    (hm : AntitoneOn φ (Icc a b))
    (hγd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ (φ t))
    (hint : IntervalIntegrable (fun s => w s * ‖deriv γ s‖) volume (φ b) (φ a)),
    IntervalIntegrable (fun t => w (φ t) * ‖deriv (γ ∘ φ) t‖) volume a b ∧
      (∫ t in a..b, w (φ t) * ‖deriv (γ ∘ φ) t‖) =
        ∫ s in φ b..φ a, w s * ‖deriv γ s‖

/-- A proper proved component of the unchanged full obligation. -/
def scalar_arclength_density_congr_type : Prop :=
  ∀
    {a b : ℝ} {γ η : ℝ → ℂ} {w : ℝ → ℝ}
    (hab : a ≤ b) (heq : EqOn η γ (Icc a b)),
    (IntervalIntegrable (fun t => w t * ‖deriv γ t‖) volume a b ↔
      IntervalIntegrable (fun t => w t * ‖deriv η t‖) volume a b) ∧
      (∫ t in a..b, w t * ‖deriv η t‖) = ∫ t in a..b, w t * ‖deriv γ t‖

/-- A proper proved component of the unchanged full obligation. -/
def pullback_roundingArc_length_type : Prop :=
  ∀ (g : ℂ → ℂ) {R ε θ : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R))
    (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ),
    IntervalIntegrable (fun t => ‖deriv (g ∘ roundingArc ε θ) t‖) MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ roundingArc ε θ) t‖) ≤
      (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε

/-- A proper proved component of the unchanged full obligation. -/
def pullback_shortRay_length_type : Prop :=
  ∀ (g : ℂ → ℂ) {R ε : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R))
    (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1),
    IntervalIntegrable (fun t => ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖)
      MeasureTheory.volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖) ≤ (L : ℝ) * ε

/-- A proper proved component of the unchanged full obligation. -/
def deleted_subinterval_sum_bound_type : Prop :=
  ∀ (n : ℕ) (node : ℕ → ℝ) (hm : Monotone node)
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (node 0) (node n))
    (M : ℝ) (hM : ∀ t ∈ Icc (node 0) (node n), |f t| ≤ M)
    (keep : ℕ → Prop) [DecidablePred keep],
    (∫ t in (node 0)..(node n), f t) =
      (∑ k ∈ (Finset.range n).filter keep, ∫ t in (node k)..(node (k+1)), f t) +
      (∑ k ∈ (Finset.range n).filter (fun k => ¬ keep k),
        ∫ t in (node k)..(node (k+1)), f t) ∧
    |(∫ t in (node 0)..(node n), f t) -
      (∑ k ∈ (Finset.range n).filter keep, ∫ t in (node k)..(node (k+1)), f t)| ≤
      M * ∑ k ∈ (Finset.range n).filter (fun k => ¬ keep k), (node (k+1) - node k)

/-- A proper proved component of the unchanged full obligation. -/
def outwardNormal_signed_circle_of_local_side_type : Prop :=
  ∀ {D W : Set ℂ}
    (hD : IsClassicalRegularDomain (planeIsometry '' D))
    (c : ℂ) (r s t : ℝ) (hr : 0 < r) (hs : s = 1 ∨ s = -1)
    (p : frontier (planeIsometry '' D))
    (hp : (p : Specs.D04.C01.EuclideanInterfaces.Model.E 2) = planeIsometry (D12Complex.CircularExhaustion.arcParam c r t))
    (hW : IsOpen W) (hpW : D12Complex.CircularExhaustion.arcParam c r t ∈ W)
    (hside : ∀ z ∈ W, z ∈ D ↔ s * (‖z - c‖ ^ 2 - r ^ 2) < 0),
    planeIsometry.symm (outwardNormal hD p) = s • Complex.exp ((t : ℂ) * Complex.I)

/-- A proper proved component of the unchanged full obligation. -/
def chart_surgery_harmonic_green_type : Prop :=
  ∀ {U O : Set ℂ} {J : Finset ℂ}
    (hgeom : RoundingGeometry U J)
    (e : ℂ → OpenPartialHomeomorph ℂ ℂ) (θ : ℂ → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hθ : ∀ p ∈ J, 0 < θ p ∧ θ p < 2 * Real.pi)
    (hside : ∀ p ∈ J, (e p).IsImage U (CircularExhaustion.sector (θ p)))
    (hc : ∀ p ∈ J, ContDiffOn ℝ 1 (e p) (e p).source ∧
      ContDiffOn ℝ 1 (e p).symm (e p).target)
    (hp : ∀ p ∈ J, p ∈ (e p).source ∧ e p p = 0)
    (hdisj : ∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (e p).source (e q).source)
    (htip : ∀ p ∈ J, sectorTip ε (θ p) ⊆ (e p).target)
    (hO : IsOpen O) (hUO : closure U ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (hLu : ∀ z ∈ U, coordinateLaplacian u z = 0)
    (hLv : ∀ z ∈ U, coordinateLaplacian v z = 0),
    let V := U \ ⋃ p ∈ J, (e p).symm '' sectorTip ε (θ p)
    ∃ hV : Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
        (ComplexGreenBridge.planeIsometry '' V),
      HasC1DefiningFunctions V ∧ HasRegularBoundaryParametrizations V ∧ closure V ⊆ O ∧
      Specs.D04.C12.GaussDivergenceTheorem.Model.HasDensityIntegral (d := 1)
        (ComplexGreenBridge.boundaryFlux hV u v) 0 ∧
      Specs.D04.C12.IntegrationByPartsAndGreenIdentities.Model.boundaryIntegral
        (ComplexGreenBridge.boundaryFlux hV u v) = 0

/-- A proper proved component of the unchanged full obligation. -/
def pullback_roundingArc_flux_bound_type : Prop :=
  ∀ {K O : Set ℂ} (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (g : ℂ → ℂ) {R ε θ : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (hθ : 0 < θ)
    (N : ℝ → ℂ) (hN : ContinuousOn N (Icc (0 : ℝ) 1))
    (hNnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖N t‖ ≤ 1)
    (htrace : MapsTo (g ∘ roundingArc ε θ) (Icc (0 : ℝ) 1) K),
    IntervalIntegrable (fun t =>
      (u (g (roundingArc ε θ t)) * inner ℝ (gradient v (g (roundingArc ε θ t))) (N t) -
       v (g (roundingArc ε θ t)) * inner ℝ (gradient u (g (roundingArc ε θ t))) (N t)) *
        ‖deriv (g ∘ roundingArc ε θ) t‖) volume 0 1 ∧
    |∫ t in (0 : ℝ)..1,
      (u (g (roundingArc ε θ t)) * inner ℝ (gradient v (g (roundingArc ε θ t))) (N t) -
       v (g (roundingArc ε θ t)) * inner ℝ (gradient u (g (roundingArc ε θ t))) (N t)) *
        ‖deriv (g ∘ roundingArc ε θ) t‖| ≤
      M * (L : ℝ) * (Real.pi / 2 + 6 * θ) * ε

/-- A proper proved component of the unchanged full obligation. -/
def pullback_roundingArc_flux_tendsto_zero_type : Prop :=
  ∀ {K O : Set ℂ}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (g : ℂ → ℂ) {R θ : ℝ} {L : NNReal} (hR : 0 < R) (hθ : 0 < θ)
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (N : ℝ → ℝ → ℂ)
    (hN : ∀ ε ∈ Ioo (0 : ℝ) R, ContinuousOn (N ε) (Icc (0 : ℝ) 1))
    (hNnorm : ∀ ε ∈ Ioo (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) 1, ‖N ε t‖ ≤ 1)
    (htrace : ∀ ε ∈ Ioo (0 : ℝ) R,
      MapsTo (g ∘ roundingArc ε θ) (Icc (0 : ℝ) 1) K),
    Tendsto (fun ε => ∫ t in (0 : ℝ)..1,
      (u (g (roundingArc ε θ t)) * inner ℝ (gradient v (g (roundingArc ε θ t))) (N ε t) -
       v (g (roundingArc ε θ t)) * inner ℝ (gradient u (g (roundingArc ε θ t))) (N ε t)) *
        ‖deriv (g ∘ roundingArc ε θ) t‖) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))

/-- A proper proved component of the unchanged full obligation. -/
def pullback_shortRay_flux_bound_type : Prop :=
  ∀ {K O : Set ℂ} (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ K, ∀ ν : ℂ, ‖ν‖ ≤ 1 →
      |u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν| ≤ M)
    (g : ℂ → ℂ) {R ε : ℝ} {L : NNReal}
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (hε : 0 < ε) (hεR : ε < R) (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1)
    (N : ℝ → ℂ) (hN : ContinuousOn N (Icc (0 : ℝ) 1))
    (hNnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖N t‖ ≤ 1)
    (htrace : MapsTo (g ∘ (fun t : ℝ => (ε * t) • ξ)) (Icc (0 : ℝ) 1) K),
    IntervalIntegrable (fun t =>
      (u (g ((ε * t) • ξ)) * inner ℝ (gradient v (g ((ε * t) • ξ))) (N t) -
       v (g ((ε * t) • ξ)) * inner ℝ (gradient u (g ((ε * t) • ξ))) (N t)) *
        ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖) volume 0 1 ∧
    |∫ t in (0 : ℝ)..1,
      (u (g ((ε * t) • ξ)) * inner ℝ (gradient v (g ((ε * t) • ξ))) (N t) -
       v (g ((ε * t) • ξ)) * inner ℝ (gradient u (g ((ε * t) • ξ))) (N t)) *
        ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖| ≤ M * (L : ℝ) * ε

/-- A proper proved component of the unchanged full obligation. -/
def pullback_shortRay_flux_tendsto_zero_type : Prop :=
  ∀ {K O : Set ℂ}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (u v : ℂ → ℝ) (hu : ContDiffOn ℝ 2 u O) (hv : ContDiffOn ℝ 2 v O)
    (g : ℂ → ℂ) {R : ℝ} {L : NNReal} (hR : 0 < R)
    (hg : ContDiffOn ℝ 1 g (ball 0 R)) (hLip : LipschitzOnWith L g (closedBall 0 R))
    (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) (N : ℝ → ℝ → ℂ)
    (hN : ∀ ε ∈ Ioo (0 : ℝ) R, ContinuousOn (N ε) (Icc (0 : ℝ) 1))
    (hNnorm : ∀ ε ∈ Ioo (0 : ℝ) R, ∀ t ∈ Icc (0 : ℝ) 1, ‖N ε t‖ ≤ 1)
    (htrace : ∀ ε ∈ Ioo (0 : ℝ) R,
      MapsTo (g ∘ (fun t : ℝ => (ε * t) • ξ)) (Icc (0 : ℝ) 1) K),
    Tendsto (fun ε => ∫ t in (0 : ℝ)..1,
      (u (g ((ε * t) • ξ)) * inner ℝ (gradient v (g ((ε * t) • ξ))) (N ε t) -
       v (g ((ε * t) • ξ)) * inner ℝ (gradient u (g ((ε * t) • ξ))) (N ε t)) *
        ‖deriv (g ∘ (fun t : ℝ => (ε * t) • ξ)) t‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))

end Specs.D12Complex.Ch14.PiecewiseCircularGreen
