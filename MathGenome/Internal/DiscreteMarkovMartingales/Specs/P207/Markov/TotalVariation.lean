import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.Interfaces
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Paper §3.3 (W15): the event-supremum normalization of total variation.
The coupling statements are allocated separately. No support restriction is imposed. -/

open Filter
open scoped Topology ENNReal

universe u
namespace P207.Markov
noncomputable section

/-- Paper-normalized total variation, with event probabilities in real numbers. -/
def totalVariation {S : Type u} (μ ν : ProbabilityLaw S) : ℝ :=
  sSup (Set.range (fun A : Set S => |(lawEvent μ A).toReal - (lawEvent ν A).toReal|))

namespace TotalVariationSpec

def totalVariationType := {S : Type u} → ProbabilityLaw S → ProbabilityLaw S → ℝ

noncomputable def totalVariationValue : totalVariationType.{u} :=
  fun {_} μ ν => sSup (Set.range (fun A : Set _ =>
    |(lawEvent μ A).toReal - (lawEvent ν A).toReal|))

def eq_half_tsum : Prop :=
  ∀ {S : Type u} [Countable S] (μ ν : ProbabilityLaw S),
    totalVariation μ ν = (1 / 2 : ℝ) * ∑' i, |(μ i).toReal - (ν i).toReal|

def eq_one_sub_overlap : Prop :=
  ∀ {S : Type u} [Countable S] (μ ν : ProbabilityLaw S),
    totalVariation μ ν = 1 - ∑' i, min (μ i).toReal (ν i).toReal

def bind_le : Prop :=
  ∀ {S : Type u} [Countable S] (μ ν : ProbabilityLaw S) (P : StochasticMatrix S),
    totalVariation (μ.bind P) (ν.bind P) ≤ totalVariation μ ν

def tendsto_of_pointwise : Prop :=
  ∀ {S : Type u} [Countable S] (μn : ℕ → ProbabilityLaw S) (μ : ProbabilityLaw S),
    (∀ i, Tendsto (fun n => (μn n i).toReal) atTop (𝓝 (μ i).toReal)) →
    Tendsto (fun n => totalVariation (μn n) μ) atTop (𝓝 0)

end TotalVariationSpec
end
end P207.Markov
