import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CornerDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The outward normal on every deleted circle points into its deleted disk.
Circle fluxes are integrated over the part inside the original domain; original
boundary arcs have zero flux because both functions have zero boundary values.
All integrals below are actual scalar interval integrals, with arclength speed r.
No smoothness at an untrimmed corner or Green identity is a hypothesis. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

namespace D12Complex.TruncatedGreenIdentity
open CircularExhaustion

/-- The full normalized logarithmic-pole and zero-boundary hypotheses. -/
def NormalizedPole (D : Set ℂ) (a : ℂ) (u : ℂ → ℝ) : Prop :=
  HarmonicOn (D \ {a}) u ∧ ContinuousOn u (closure D \ {a}) ∧
  (∀ z ∈ frontier D, u z = 0) ∧
  ∃ R : ℝ, 0 < R ∧ ball a R ⊆ D ∧ ∃ h : ℂ → ℝ,
    HarmonicOn (ball a R) h ∧
    ∀ z ∈ ball a R \ {a}, h z = u z + Real.log ‖z - a‖

/-- The actual antisymmetric normal flux density in the real complex plane. -/
def normalFlux (u v : ℂ → ℝ) (z ν : ℂ) : ℝ :=
  u z * inner ℝ (gradient v z) ν - v z * inner ℝ (gradient u z) ν

/-- Radial normal directed toward the removed disk, for r>0. -/
def inwardCircleNormal (t : ℝ) : ℂ := -Complex.exp (t * Complex.I)

/-- The zero extension in angle of the arclength flux on the circle's interior
arcs. Endpoint values do not affect the interval integral. -/
def circleFluxIntegrand (D : Set ℂ) (u v : ℂ → ℝ) (c : ℂ) (r t : ℝ) : ℝ :=
  if arcParam c r t ∈ D then
    normalFlux u v (arcParam c r t) (inwardCircleNormal t) * r else 0

def circleFlux (D : Set ℂ) (u v : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(2 * Real.pi), circleFluxIntegrand D u v c r t

/-- The actual open domain after closed disks at the poles and corners are cut. -/
def cutDomain (D : Set ℂ) (a b : ℂ) (ra rb : ℝ)
    (corners : Finset ℂ) (ρ : ℂ → ℝ) : Set ℂ :=
  D \ (closedBall a ra ∪ closedBall b rb ∪ ⋃ c ∈ corners, closedBall c (ρ c))

/-- The hypotheses on the finite corner set are purely geometric. -/
def CornerSet (D : Set ℂ) (corners : Finset ℂ) : Prop :=
  (↑corners : Set ℂ) ⊆ frontier D ∧
  (∀ c ∈ frontier D, c ∉ corners → SectorChart D c Real.pi) ∧
  ∀ c ∈ corners, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧ SectorChart D c θ

end D12Complex.TruncatedGreenIdentity

namespace Specs.D12Complex.Ch14.TruncatedGreenIdentity
open _root_.D12Complex _root_.D12Complex.CircularExhaustion
open _root_.D12Complex.TruncatedGreenIdentity

/-- The analytic corner estimate, including the actual arc integral and its
integrability. It allows every positive conformal angle, including reentrant
corners with negative gradient exponent. -/
def corner_circle_flux_type : Prop :=
  ∀ (D : Set ℂ) (c : ℂ) (θ R : ℝ) (u v : ℂ → ℝ),
    IsOpen D → 0 < θ → θ < 2 * Real.pi → SectorChart D c θ → 0 < R →
    HarmonicOn (D ∩ ball c R) u → HarmonicOn (D ∩ ball c R) v →
    ContinuousOn u (closure D ∩ ball c R) →
    ContinuousOn v (closure D ∩ ball c R) →
    (∀ z ∈ frontier D ∩ ball c R, u z = 0) →
    (∀ z ∈ frontier D ∩ ball c R, v z = 0) →
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ R ∧
      (∀ r : ℝ, 0 < r → r < δ →
        IntervalIntegrable (circleFluxIntegrand D u v c r) volume 0 (2 * Real.pi) ∧
        |circleFlux D u v c r| ≤ C * r ^ (2 * (Real.pi / θ))) ∧
      Tendsto (circleFlux D u v c) (𝓝[>] 0) (𝓝 0)

/-- The complete fixed-cut identity. Smallness and disjointness of pole and
corner disks are established, not assumed. The original arc fluxes are zero;
the displayed sum is the full outward boundary flux of the cut domain. -/
def truncated_green_identity_type : Prop :=
  ∀ (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
    IsCircularExhaustion Ω s r → ∀ j : ℕ,
    let D := diskUnion (s j) (r j)
    ∀ (corners : Finset ℂ), CornerSet D corners →
    ∀ (a b : ℂ) (u v : ℂ → ℝ), a ∈ D → b ∈ D → a ≠ b →
    NormalizedPole D a u → NormalizedPole D b v →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ra rb : ℝ) (ρ : ℂ → ℝ),
      0 < ra → ra < δ → 0 < rb → rb < δ →
      (∀ c ∈ corners, 0 < ρ c ∧ ρ c < δ) →
      closedBall a ra ⊆ D ∧ closedBall b rb ⊆ D ∧
      Disjoint (closedBall a ra) (closedBall b rb) ∧
      (∀ c ∈ corners,
        Disjoint (closedBall c (ρ c)) (closedBall a ra) ∧
        Disjoint (closedBall c (ρ c)) (closedBall b rb)) ∧
      (∀ c ∈ corners, ∀ d ∈ corners, c ≠ d →
        Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) u ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) v ∧
      IntervalIntegrable (circleFluxIntegrand D u v a ra) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (circleFluxIntegrand D u v b rb) volume 0 (2 * Real.pi) ∧
      (∀ c ∈ corners,
        IntervalIntegrable (circleFluxIntegrand D u v c (ρ c)) volume 0 (2 * Real.pi)) ∧
      circleFlux D u v a ra + circleFlux D u v b rb +
        ∑ c ∈ corners, circleFlux D u v c (ρ c) = 0

/-- Each original corner term tends to zero for the normalized-pole functions.
Fixing the pole cuts has no effect on this local assertion. -/
def normalized_pole_corner_flux_type : Prop :=
  ∀ (D : Set ℂ) (corners : Finset ℂ), IsOpen D → CornerSet D corners →
    ∀ (a b : ℂ) (u v : ℂ → ℝ), a ∈ D → b ∈ D →
    NormalizedPole D a u → NormalizedPole D b v →
    ∀ c ∈ corners, Tendsto (circleFlux D u v c) (𝓝[>] 0) (𝓝 0)

/-- All corner radii may shrink independently. The finite total corner flux
then tends to zero, in particular with the pole cuts held fixed. -/
def normalized_pole_corner_flux_sum_type : Prop :=
  ∀ (D : Set ℂ) (corners : Finset ℂ), IsOpen D → CornerSet D corners →
    ∀ (a b : ℂ) (u v : ℂ → ℝ), a ∈ D → b ∈ D →
    NormalizedPole D a u → NormalizedPole D b v →
    ∀ ρ : ℂ → ℝ → ℝ,
    (∀ c ∈ corners, Tendsto (ρ c) (𝓝[>] 0) (𝓝[>] 0)) →
    Tendsto (fun t => ∑ c ∈ corners, circleFlux D u v c (ρ c t))
      (𝓝[>] 0) (𝓝 0)

/-- All fixed-cut geometric and analytic preconditions, a proper part of the
full identity. The zero-flux equation is still the separate target above. -/
def fixed_cut_preconditions_type : Prop :=
∀ (Ω : Set ℂ) (s : ℕ → Finset ℂ) (r : ℕ → ℂ → ℝ),
    IsCircularExhaustion Ω s r → ∀ j : ℕ,
    let D := diskUnion (s j) (r j)
    ∀ (corners : Finset ℂ), CornerSet D corners →
    ∀ (a b : ℂ) (u v : ℂ → ℝ), a ∈ D → b ∈ D → a ≠ b →
    NormalizedPole D a u → NormalizedPole D b v →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ra rb : ℝ) (ρ : ℂ → ℝ),
      0 < ra → ra < δ → 0 < rb → rb < δ →
      (∀ c ∈ corners, 0 < ρ c ∧ ρ c < δ) →
      closedBall a ra ⊆ D ∧ closedBall b rb ⊆ D ∧
      Disjoint (closedBall a ra) (closedBall b rb) ∧
      (∀ c ∈ corners,
        Disjoint (closedBall c (ρ c)) (closedBall a ra) ∧
        Disjoint (closedBall c (ρ c)) (closedBall b rb)) ∧
      (∀ c ∈ corners, ∀ d ∈ corners, c ≠ d →
        Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) u ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) v ∧
      IntervalIntegrable (circleFluxIntegrand D u v a ra) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (circleFluxIntegrand D u v b rb) volume 0 (2 * Real.pi) ∧
      (∀ c ∈ corners,
        IntervalIntegrable (circleFluxIntegrand D u v c (ρ c)) volume 0 (2 * Real.pi))

/-- The original functions admit actual globally smooth extensions agreeing
on the entire fixed cut closure. Thus C² near the closure is a conclusion,
without regularity at any untrimmed original corner. -/
def smooth_cut_extensions_type : Prop :=
  ∀ (D : Set ℂ) (corners : Finset ℂ), IsOpen D → CornerSet D corners →
    ∀ (a b : ℂ) (u v : ℂ → ℝ),
    NormalizedPole D a u → NormalizedPole D b v →
    ∀ (ra rb : ℝ) (ρ : ℂ → ℝ), 0 < ra → 0 < rb →
    (∀ c ∈ corners, 0 < ρ c) →
    ∃ u₀ v₀ : ℂ → ℝ, ContDiff ℝ ∞ u₀ ∧ ContDiff ℝ ∞ v₀ ∧
      EqOn u₀ u (closure (cutDomain D a b ra rb corners ρ)) ∧
      EqOn v₀ v (closure (cutDomain D a b ra rb corners ρ)) ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) u₀ ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) v₀

/-- Smooth extensions preserve the actual deleted-circle fluxes for every
disjoint fixed cut, and have zero flux on the retained original boundary.
This is an analytic transfer statement, not a zero-total-flux assumption. -/
def smooth_cut_flux_transfer_type : Prop :=
  ∀ (D : Set ℂ) (corners : Finset ℂ), IsOpen D → CornerSet D corners →
    ∀ (a b : ℂ) (u v : ℂ → ℝ),
    NormalizedPole D a u → NormalizedPole D b v →
    ∀ (ra rb : ℝ) (ρ : ℂ → ℝ), 0 < ra → 0 < rb →
    (∀ c ∈ corners, 0 < ρ c) →
    Disjoint (closedBall a ra) (closedBall b rb) →
    (∀ c ∈ corners,
      Disjoint (closedBall c (ρ c)) (closedBall a ra) ∧
      Disjoint (closedBall c (ρ c)) (closedBall b rb)) →
    (∀ c ∈ corners, ∀ d ∈ corners, c ≠ d →
      Disjoint (closedBall c (ρ c)) (closedBall d (ρ d))) →
    ∃ u₀ v₀ : ℂ → ℝ, ContDiff ℝ ∞ u₀ ∧ ContDiff ℝ ∞ v₀ ∧
      EqOn u₀ u (closure (cutDomain D a b ra rb corners ρ)) ∧
      EqOn v₀ v (closure (cutDomain D a b ra rb corners ρ)) ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) u₀ ∧
      HarmonicOn (cutDomain D a b ra rb corners ρ) v₀ ∧
      circleFlux D u₀ v₀ a ra = circleFlux D u v a ra ∧
      circleFlux D u₀ v₀ b rb = circleFlux D u v b rb ∧
      (∀ c ∈ corners, circleFlux D u₀ v₀ c (ρ c) = circleFlux D u v c (ρ c)) ∧
      ∀ z ∈ frontier D ∩ closure (cutDomain D a b ra rb corners ρ),
        ∀ ν : ℂ, normalFlux u₀ v₀ z ν = 0

end Specs.D12Complex.Ch14.TruncatedGreenIdentity
