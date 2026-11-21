import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.WeightedResolventEstimate
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Independent statement of paper.tex, fa2:p3:resolvent-decay-obstruction,
14486–14542. The derivative at zero is the right derivative. Continuity
of both graph coordinates expresses continuity into D(G) with its graph
norm. No separability assumption is made.

The divergent nonnegative integral is expressed by the Lebesgue integral
with values in ℝ≥0∞, so divergence cannot be confused with the default
value of a nonintegrable Bochner integral.
-/

noncomputable section
open MeasureTheory Filter Topology

namespace ExpandedFA.Semigroups.ResolventDecay.Spec

def DecayObstruction : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
  ∀ (G : Unbounded.Operator ℂ H H) (T : C0Semigroup ℂ H),
  C0SemigroupSpec.generatesValue G T →
  ∀ (ξ : ℕ → ℝ), Tendsto ξ atTop atBot →
  ∀ (d : ℝ), 0 < d → (∀ n, WeightedResolvent.LineBound G (ξ n) d) →
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

end ExpandedFA.Semigroups.ResolventDecay.Spec
