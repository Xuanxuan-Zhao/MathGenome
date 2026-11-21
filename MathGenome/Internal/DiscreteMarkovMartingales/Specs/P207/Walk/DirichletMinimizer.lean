import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.BoundaryHarmonic

universe u
namespace P207.Markov.DirichletMinimizerSpec
noncomputable section

/-- The hitting-expectation solution is harmonic, uniquely determined by the
boundary equations, and uniquely minimizes energy among all boundary extensions.
There is no restriction on the size of the interior or on the number of states. -/
def dirichlet_principle : Prop :=
  ∀ {S : Type u} [Fintype S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (P : StochasticMatrix S) (π : ProbabilityLaw S)
    (hπ : ∀ x, 0 < π x), Irreducible P → IsReversible P π →
    ∀ (B : Set S), B.Nonempty → ∀ (g : B → ℝ),
      IsBoundaryHarmonic P B g (boundaryHarmonic P B g) ∧
      (∀ f, IsBoundaryHarmonic P B g f → f = boundaryHarmonic P B g) ∧
      (∀ (c : ℝ) (x : S), boundaryHarmonic P B g x =
        stateExpectation P x (boundaryPayoff B g c)) ∧
      ∀ f : S → ℝ, (∀ x : B, f x = g x) →
        WeightedSpace.dirichletForm π hπ P (boundaryHarmonic P B g)
            (boundaryHarmonic P B g) ≤ WeightedSpace.dirichletForm π hπ P f f ∧
        (WeightedSpace.dirichletForm π hπ P f f =
          WeightedSpace.dirichletForm π hπ P (boundaryHarmonic P B g)
            (boundaryHarmonic P B g) ↔ f = boundaryHarmonic P B g)

end
end P207.Markov.DirichletMinimizerSpec
