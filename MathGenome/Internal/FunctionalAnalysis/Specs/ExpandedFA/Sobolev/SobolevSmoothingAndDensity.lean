import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.SmoothApproximateIdentities

/-! Independent statements for the smoothing/density clauses of
`fa2:p4:sobolev-calculus`, paper.tex:17621–17666. No boundary regularity,
nonempty-domain, or positive-dimension assumption is imposed. Local convergence
at infinity means convergence on every compact interior set. -/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace ExpandedFA.Sobolev.Smoothing
open ExpandedFA.Distributions
open SmoothApproximateIdentitiesSpec

/-- Extension of an Lp representative by zero, used only to define interior
convolution. This does not assert Sobolev regularity across the boundary. -/
def zeroExtend {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p) : Domain d → 𝕜 :=
  (Ω : Set (Domain d)).indicator u

/-- A smooth whole-space function; its derivatives are compared to the original
weak derivatives only on compact subsets of Ω and at sufficiently small scales. -/
def regularize {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (ρ : Domain d → ℝ) (ε : ℝ)
    (u : DomainLp 𝕜 Ω p) : Domain d → 𝕜 :=
  MollifyValue ρ ε (zeroExtend u)

/-- Coordinate derivatives in the order matching the transpose convention of
the accepted distributional derivative. For smooth functions these are the
usual multi-index derivatives. -/
def classicalDerivative {𝕜 : Type} [RCLike 𝕜] {d m : ℕ}
    (α : DerivativeIndex d m) (f : Domain d → 𝕜) : Domain d → 𝕜 :=
  partialFunction (multiIndexWord (natIndex α)).reverse f

end ExpandedFA.Sobolev.Smoothing

namespace Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.Sobolev.Smoothing SmoothApproximateIdentitiesSpec
open WeakDerivativeSpaces

/-- Smooth on Ω, with no compact-support or boundary-extension requirement. -/
def SmoothMembers (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (SpaceValue 𝕜 d Ω m p) :=
  {u | ∃ f : Domain d → 𝕜, ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
    u.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))] f}

def SmoothDensity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  p ≠ ∞ → Dense (SmoothMembers 𝕜 d Ω m p)

def SmoothRegularization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ), IsMollifier ρ → ∀ ε : ℝ, 0 < ε →
    ∀ u : DomainLp 𝕜 Ω p, ContDiff ℝ (⊤ : ℕ∞) (regularize ρ ε u)

/-- One eventually-small scale works for all x in K and all derivatives of
order at most m. There is no assertion at boundary points of Ω. -/
def InteriorDerivativeIdentity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ρ : Domain d → ℝ), IsMollifier ρ → ∀ u : SpaceValue 𝕜 d Ω m p,
    ∀ K : Set (Domain d), IsCompact K → K ⊆ Ω →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ α : DerivativeIndex d m, ∀ x ∈ K,
      classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) x =
        regularize ρ ε (u.val α) x

def FinitePConvergence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ∞ → ∀ (ρ : Domain d → ℝ), IsMollifier ρ →
    ∀ u : SpaceValue 𝕜 d Ω m p, ∀ K : Set (Domain d),
    IsCompact K → K ⊆ Ω → ∀ α : DerivativeIndex d m,
      Tendsto (fun ε => eLpNorm
        (classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) - (u.val α : Domain d → 𝕜))
        p (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Sharp componentwise uniform derivative bound, valid pointwise on K. -/
def UniformDerivativeBounds : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (ρ : Domain d → ℝ), IsMollifier ρ →
    ∀ u : SpaceValue 𝕜 d Ω m ∞, ∀ K : Set (Domain d),
    IsCompact K → K ⊆ Ω →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ α : DerivativeIndex d m, ∀ x ∈ K,
      ‖classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) x‖ ≤ ‖u.val α‖

def LocalFiniteRConvergence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (ρ : Domain d → ℝ), IsMollifier ρ →
    ∀ u : SpaceValue 𝕜 d Ω m ∞, ∀ K : Set (Domain d),
    IsCompact K → K ⊆ Ω → ∀ r : ℝ≥0∞, 1 ≤ r → r ≠ ∞ →
    ∀ α : DerivativeIndex d m, Tendsto (fun ε => eLpNorm
      (classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) - (u.val α : Domain d → 𝕜))
      r (volume.restrict K)) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- Weak-star convergence on compact interior sets, against every L1 test,
using the manuscript's bilinear (not conjugate-linear) scalar pairing. -/
def WeakStarDerivativeConvergence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (m : ℕ) (ρ : Domain d → ℝ), IsMollifier ρ →
    ∀ u : SpaceValue 𝕜 d Ω m ∞, ∀ K : Set (Domain d),
    IsCompact K → K ⊆ Ω → ∀ α : DerivativeIndex d m,
    ∀ g : Domain d → 𝕜, MemLp g 1 (volume.restrict K) →
      Tendsto (fun ε => ∫ x in K, g x *
        classicalDerivative α (regularize ρ ε (u.val (zeroIndex d m))) x)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in K, g x * u.val α x))

end Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
