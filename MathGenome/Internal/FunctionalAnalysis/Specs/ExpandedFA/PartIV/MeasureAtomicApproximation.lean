import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.MetricSpace.Basic

/-! Statements for the atomic part of `fa2:p4:measure-approximation`.
The smooth-density assertions are allocated separately. Finite support means
that the genuine total variation vanishes off a finite set; this also allows
the zero measure and the empty compact metric space. -/

namespace ExpandedFA.PartIV.MeasureAtomicApproximationSpec

open Set MeasureTheory Filter
open scoped Topology
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec

universe u

def FiniteScalarSupport {K 𝕜 : Type*} [MeasurableSpace K] [RCLike 𝕜]
    (ν : VectorMeasure K 𝕜) : Prop :=
  ∃ s : Finset K, ν.variation (s : Set K)ᶜ = 0

def FinitePositiveSupport {K : Type*} [MeasurableSpace K] (μ : Measure K) : Prop :=
  ∃ s : Finset K, μ (s : Set K)ᶜ = 0

/-- Sequential weak-star approximation, with exact variation at every index,
for both real and complex measures, without a nonzero or nonempty assumption. -/
def ScalarApproximation : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (𝕜 : Type) [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜), FiniteScalarRadon μ →
    ∃ ν : ℕ → VectorMeasure K 𝕜,
      (∀ n, FiniteScalarRadon (ν n) ∧ FiniteScalarSupport (ν n) ∧
        (ν n).variation.real univ = μ.variation.real univ) ∧
      ∀ f : C(K, 𝕜), Tendsto (fun n => scalarIntegral (ν n) f) atTop
        (𝓝 (scalarIntegral μ f))

/-- Native positive measures ensure that every atomic mass is nonnegative.
The approximants are probabilities at every index, and convergence tests all
continuous real- or complex-valued functions. -/
def ProbabilityApproximation : Prop :=
  ∀ (K : Type u) [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ],
    ∃ ν : ℕ → Measure K,
      (∀ n, IsProbabilityMeasure (ν n) ∧ PositiveRadon (ν n) ∧
        FinitePositiveSupport (ν n)) ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (f : C(K, 𝕜)),
        Tendsto (fun n => ∫ x, f x ∂ν n) atTop
        (𝓝 (∫ x, f x ∂μ))

end ExpandedFA.PartIV.MeasureAtomicApproximationSpec
