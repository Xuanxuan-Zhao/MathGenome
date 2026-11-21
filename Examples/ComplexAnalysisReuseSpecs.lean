import MathGenome.ComplexAnalysis.Topics.D12Complex.Ch01
import MathGenome.ComplexAnalysis.Topics.D12Complex.Ch03
import MathGenome.ComplexAnalysis.Topics.D12Complex.Ch06
import MathGenome.ComplexAnalysis.Topics.D12Complex.Ch20
import MathGenome.ComplexAnalysis.Topics.D12Complex.Ch23

/-! Independent expected conclusions for downstream complex-analysis applications.
These statements import the delivered library, never their application proofs.
They are integration checks, not additional source obligations. -/

noncomputable section
open Set

namespace Examples.GenomeComplexProbeSpecs

/-- A nonzero complex derivative preserves real orientation, both intrinsically
and in the standard real-coordinate matrix. -/
def realJacobianPositive : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ),
    D12Complex.HasComplexDerivativeAt f c a → c ≠ 0 →
    0 < LinearMap.det (fderiv ℝ f a).toLinearMap ∧
      0 < (D12Complex.realDifferentialMatrix f a).det

/-- Omitting two distinct finite values forces every derivative to vanish. -/
def omittedValuesDerivativesVanish : Prop :=
  ∀ (f : ℂ → ℂ) (a b : ℂ),
    D12Complex.HolomorphicOn univ f → a ≠ b →
    (∀ z : ℂ, f z ≠ a) → (∀ z : ℂ, f z ≠ b) →
    ∀ z : ℂ, deriv f z = 0

/-- An equality case in Schwarz's derivative estimate preserves all disk
distances, a property of the supplied map rather than a chosen coefficient. -/
def schwarzEqualityPreservesDistances : Prop :=
  ∀ (f : ℂ → ℂ), D12Complex.HolomorphicOn (Metric.ball 0 1) f →
    MapsTo f (Metric.ball 0 1) (Metric.ball 0 1) → f 0 = 0 →
    ‖deriv f 0‖ = 1 →
    ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      dist (f z) (f w) = dist z w

/-- Vanishing piecewise-C1 periods gives one primitive whose endpoint formula
works for every canonical rectifiable path on its actual compact interval. -/
def zeroPeriodsRectifiablePrimitive : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), D12Complex.IsDomain Ω →
    ContinuousOn f Ω → D12Complex.Primitives.ZeroPeriods Ω f →
    ∃ F : ℂ → ℂ, D12Complex.Primitives.IsPrimitive Ω f F ∧
      ∀ γ : D12Complex.ComplexPath,
        D12Complex.Stieltjes.Rectifiable γ → γ.trace ⊆ Ω →
        D12Complex.Stieltjes.contourIntegral γ f = F γ.target - F γ.source

/-- Equal normalization at a single point removes the additive constant
between two primitives on the same domain. -/
def normalizedPrimitiveUnique : Prop :=
  ∀ (Ω : Set ℂ) (f F G : ℂ → ℂ) (a : ℂ),
    D12Complex.IsDomain Ω → a ∈ Ω →
    D12Complex.Primitives.IsPrimitive Ω f F →
    D12Complex.Primitives.IsPrimitive Ω f G → F a = G a → EqOn F G Ω

/-- A reachable continuation component is second countable even though the
full holomorphic germ space over the plane is not. The two types stay distinct. -/
def componentAndFullGermCountability : Prop :=
  ∀ (Ω : Set ℂ), D12Complex.IsDomain Ω →
    ∀ p : D12Complex.GermTopology.Space Ω,
      SecondCountableTopology (D12Complex.ContinuationSurface.Component Ω p) ∧
      ¬ SecondCountableTopology (D12Complex.GermTopology.Space (univ : Set ℂ))

end Examples.GenomeComplexProbeSpecs
