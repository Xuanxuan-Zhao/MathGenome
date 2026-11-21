import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes

/-! Normalized distribution functions, paper.tex:4749–4765.
These statements use the Chapter 12 pointwise NBV and Stieltjes conventions.
The measurable space on ℝ is Borel; signed and complex measures are finite-valued
countably additive scalar measures, with no added variation hypothesis.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Specs.D11.Ch14.NormalizedMeasureFunctionBridge
open Specs.D11.Ch12
open Specs.D11.Ch12.ScalarStieltjesCorrespondence
open Specs.D11.Ch14.TotalVariation

/-- Both recovery directions and the exact classical variation, including
reconstruction of the entire positive variation measure from its generator. -/
def DistributionProperties {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (ν : VectorMeasure ℝ E) : Prop :=
  NBV_value (cumulative_value ν) ∧
  (∀ a b : ℝ, a < b → ν (Ioc a b) = cumulative_value ν b - cumulative_value ν a) ∧
  stieltjesMeasure_value (cumulative_value ν) = ν ∧
  (∀ a b : ℝ, a ≤ b → totalVariation_value ν (Ioc a b) =
    variation_value (cumulative_value ν) a b) ∧
  (∀ x : ℝ, totalVariation_value ν (Iic x) = initialVariation_value (cumulative_value ν) x) ∧
  totalVariation_value ν univ = globalVariation_value (cumulative_value ν) ∧
  ∃ h : PositiveStieltjes.positiveGenerator_value
      (fun x => (initialVariation_value (cumulative_value ν) x).toReal),
    PositiveStieltjes.stieltjesMeasure_value
      (fun x => (initialVariation_value (cumulative_value ν) x).toReal) h =
        totalVariation_value ν

/-- A representing scalar measure is recovered at every point, with the exact
initial and global variation of the original function. -/
def RepresentationProperties {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℝ → E) (ν : VectorMeasure ℝ E) : Prop :=
  cumulative_value ν = F ∧
  (∀ a b : ℝ, a < b → ν (Ioc a b) = F b - F a) ∧
  (∀ x : ℝ, totalVariation_value ν (Iic x) = initialVariation_value F x) ∧
  totalVariation_value ν univ = globalVariation_value F

def signed_distribution : Prop :=
  ∀ ν : SignedMeasure ℝ, DistributionProperties ν

def complex_distribution : Prop :=
  ∀ ν : ComplexMeasure ℝ, DistributionProperties ν

def signed_converse : Prop :=
  ∀ F : ℝ → ℝ, NBV_value F →
    ∃! ν : SignedMeasure ℝ, RepresentationProperties F ν

def complex_converse : Prop :=
  ∀ F : ℝ → ℂ, NBV_value F →
    ∃! ν : ComplexMeasure ℝ, RepresentationProperties F ν

end Specs.D11.Ch14.NormalizedMeasureFunctionBridge
