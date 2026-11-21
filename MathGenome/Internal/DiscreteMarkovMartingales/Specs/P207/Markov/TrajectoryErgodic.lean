import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.RegenerativeExcursions
import Mathlib.Topology.Instances.Real.Lemmas

/-! The trajectory ergodic theorem of paper.tex, §3.7 (p207:W19).
The stationary probability and irreducibility imply positive recurrence (W14).
The initial distribution is arbitrary; no aperiodicity or initial integrability
assumption is imposed. The limit is along all natural times. -/

open MeasureTheory Filter
open scoped ENNReal Topology
universe u v
namespace P207.Markov.TrajectoryErgodicSpec

noncomputable def trajectory_ergodic : Prop :=
  ∀ {S : Type u} [Countable S] [Nonempty S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] {Ω : Type v} [m : MeasurableSpace Ω]
    (P : StochasticMatrix S) (π ν : ProbabilityLaw S) (X : ℕ → Ω → S)
    (ℱ : Filtration ℕ m) (μ : Measure Ω) [IsProbabilityMeasure μ],
    Irreducible P → IsStationary P π → IsMarkovChain P ν X ℱ μ →
    ∀ f : S → ℝ, Summable (fun j => (π j).toReal * |f j|) →
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.range n, f (X k ω)) / (n : ℝ))
      atTop (𝓝 (∑' j, (π j).toReal * f j))

end P207.Markov.TrajectoryErgodicSpec
