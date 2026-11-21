import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.NormalSemigroups
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.ResolventDecayObstruction

/-!
Self-adjoint spectral gaps, paper.tex `fa2:p3:spectral-gap-decay-obstruction`.
Self-adjointness includes density and equality of the complete adjoint domain.
Boundedness above is the quadratic-form upper bound on the original domain.
The gaps are open real intervals; their endpoints may belong to the spectrum.
The divergent integral is a nonnegative Lebesgue integral, including the zero
Hilbert space and arbitrary real residual constants k < d.
-/
noncomputable section
open MeasureTheory Filter Topology

namespace ExpandedFA.Semigroups.SpectralGapDecay.Spec
open Unbounded Unbounded.UnboundedNormalSpectralTheorem

/-- All generation and resolvent conclusions, with the original domain. -/
def GenerationAndLines : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (G : Operator ℂ H H), Dense (G.domain : Set H) →
  HilbertAdjointSpec.adjointValue G = G →
  (∃ ω : ℝ, ∀ x : G.domain,
    (inner ℂ (x : H) (G x)).re ≤ ω * ‖(x : H)‖ ^ 2) →
  ∀ (ξ : ℕ → ℝ), Tendsto ξ atTop atBot →
  ∀ (d : ℝ), 0 < d →
  (∀ n (s : ℝ), s ∈ Set.Ioo (ξ n - d) (ξ n + d) →
    (s : ℂ) ∉ operatorSpectrum G) →
  (∃ T : C0Semigroup ℂ H, C0SemigroupSpec.generatesValue G T) ∧
    ∀ n, WeightedResolvent.LineBound G (ξ n) d

/-- The complete lower-decay alternative, on the closed positive half-line. -/
def DecayObstruction : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (G : Operator ℂ H H), Dense (G.domain : Set H) →
  HilbertAdjointSpec.adjointValue G = G →
  (∃ ω : ℝ, ∀ x : G.domain,
    (inner ℂ (x : H) (G x)).re ≤ ω * ‖(x : H)‖ ^ 2) →
  ∀ (ξ : ℕ → ℝ), Tendsto ξ atTop atBot →
  ∀ (d : ℝ), 0 < d →
  (∀ n (s : ℝ), s ∈ Set.Ioo (ξ n - d) (ξ n + d) →
    (s : ℂ) ∉ operatorSpectrum G) →
  ∀ (u du : ℝ → H),
  ContinuousOn u (Set.Ici 0) → ContinuousOn du (Set.Ici 0) →
  (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt u (du t) (Set.Ici 0) t) →
  ∀ (hD : ∀ t ∈ Set.Ici (0 : ℝ), u t ∈ G.domain),
  Continuous (fun t : Set.Ici (0 : ℝ) => G ⟨u t, hD t t.property⟩) →
  ∀ (k : ℝ), k < d →
  (∀ t (ht : t ∈ Set.Ici (0 : ℝ)),
    ‖du t - G ⟨u t, hD t ht⟩‖ ≤ k * ‖u t‖) →
  (∀ t ∈ Set.Ici (0 : ℝ), u t = 0) ∨
    ∃ b : ℝ, 0 < b ∧
      (∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal (‖u t‖ ^ 2 * Real.exp (b * t))) = ⊤

end ExpandedFA.Semigroups.SpectralGapDecay.Spec
