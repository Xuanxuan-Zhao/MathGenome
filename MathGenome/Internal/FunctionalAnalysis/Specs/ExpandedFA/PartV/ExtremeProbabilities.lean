import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.PositiveRadonRepresentation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Probability.ConditionalProbability

/-! Independent statements for the probability-measure assertion of
`fa2:p5:extreme-measures`, paper.tex lines 23318–23319 and 23345–23350.
The scalars `ℝ≥0` in native convexity are precisely the nonnegative real
coefficients of real convex combinations. No countability assumption is made. -/

namespace ExpandedFA.PartV.ExtremeProbabilitiesSpec

open Set MeasureTheory
open scoped ENNReal NNReal
open ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec

universe u

/-- The source's regular Borel probabilities, as actual positive measures. -/
def regularProbabilities (K : Type u) [TopologicalSpace K] [MeasurableSpace K] :
    Set (Measure K) := {μ | IsProbabilityMeasure μ ∧ PositiveRadon μ}

def ConvexProbabilities : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K],
    Convex ℝ≥0 (regularProbabilities K)

/-- A non-Dirac regular probability has a Borel set of intermediate mass. -/
def IntermediateMass : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K),
    μ ∈ regularProbabilities K → (∀ x, μ ≠ Measure.dirac x) →
    ∃ A : Set K, MeasurableSet A ∧ 0 < μ A ∧ μ A < 1

/-- The two explicitly normalized restrictions are distinct regular
probabilities and give a strict convex decomposition with their original masses. -/
def RestrictionDecomposition : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K),
    μ ∈ regularProbabilities K →
    ∀ A : Set K, MeasurableSet A → 0 < μ A → μ A < 1 →
    ∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ a + b = 1 ∧
      (a : ℝ≥0∞) = μ A ∧ (b : ℝ≥0∞) = μ Aᶜ ∧
      ProbabilityTheory.cond μ A ∈ regularProbabilities K ∧
      ProbabilityTheory.cond μ Aᶜ ∈ regularProbabilities K ∧
      ProbabilityTheory.cond μ A ≠ ProbabilityTheory.cond μ Aᶜ ∧
      μ = a • ProbabilityTheory.cond μ A + b • ProbabilityTheory.cond μ Aᶜ

/-- Converse: every Dirac probability is extreme. -/
def DiracExtreme : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (x : K),
    Measure.dirac x ∈ (regularProbabilities K).extremePoints ℝ≥0

/-- Full characterization, with no prior probability or regularity hypothesis
on the measure on the right-hand side. -/
def ExtremeCharacterization : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [Nonempty K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K),
    μ ∈ (regularProbabilities K).extremePoints ℝ≥0 ↔
      ∃ x : K, μ = Measure.dirac x

end ExpandedFA.PartV.ExtremeProbabilitiesSpec
