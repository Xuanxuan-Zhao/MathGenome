import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TotalVariation

/-! The coupling assertions of paper.tex, §3.3 (W15).
The state space is countable and discrete. Marginals in the first assertion
are distributional equalities on the stated arbitrary probability space.
The second assertion constructs a law on the product, including distance zero. -/

open MeasureTheory
open scoped ENNReal
universe u v
namespace P207.Markov.MaximalCouplingSpec

noncomputable def coupling_bound : Prop :=
  ∀ {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {Ω : Type v} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ ν : ProbabilityLaw S) (U V : Ω → S),
    Measurable U → Measurable V →
    P.map U = μ.toMeasure → P.map V = ν.toMeasure →
    totalVariation μ ν ≤ (P {ω | U ω ≠ V ω}).toReal

noncomputable def exists_maximal_coupling : Prop :=
  ∀ {S : Type u} [Countable S] (μ ν : ProbabilityLaw S),
    ∃ ρ : ProbabilityLaw (S × S),
      ρ.map Prod.fst = μ ∧ ρ.map Prod.snd = ν ∧
      (lawEvent ρ {p | p.1 ≠ p.2}).toReal = totalVariation μ ν

end P207.Markov.MaximalCouplingSpec
