import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.HausdorffDefinitions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Independent specification of paper.tex, Lemma d13:18:mass-distribution.
Measures on `ℝ` use its Borel sigma algebra. All measure evaluations, including
on a possibly nonmeasurable `E`, are outer-measure evaluations. The first version
needs only full outer mass. The second expresses concentration on `E` by zero
outer mass of its complement; no closedness, compactness, or measurability of
`E` is required. A single positive interval-length cutoff is uniform in position.
Closed intervals, including singletons, suffice for the source hypothesis.
The Hausdorff measure is the upstream diameter-power definition, coefficient one.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D13Unified.Ch18.MassDistribution

/-- Quantitative mass-distribution estimate under full outer mass. -/
def mass_distribution_type : Prop :=
  ∀ (E : Set ℝ) (s C : ℝ), 0 < s → 0 < C →
    ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ν E = 1 →
      (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ a b : ℝ, a ≤ b → b - a < δ₀ →
        ν (Icc a b) ≤ ENNReal.ofReal C * (ENNReal.ofReal (b - a)) ^ s) →
      ENNReal.ofReal (C⁻¹) ≤
        Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffMeasure_value s E

/-- The source's supported-probability formulation, with explicit concentration. -/
def mass_distribution_supported_type : Prop :=
  ∀ (E : Set ℝ) (s C : ℝ), 0 < s → 0 < C →
    ∀ (ν : Measure ℝ), IsProbabilityMeasure ν → ν Eᶜ = 0 →
      (∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ a b : ℝ, a ≤ b → b - a < δ₀ →
        ν (Icc a b) ≤ ENNReal.ofReal C * (ENNReal.ofReal (b - a)) ^ s) →
      ENNReal.ofReal (C⁻¹) ≤
        Specs.D13Unified.Ch18.HausdorffDefinitions.hausdorffMeasure_value s E

end Specs.D13Unified.Ch18.MassDistribution
