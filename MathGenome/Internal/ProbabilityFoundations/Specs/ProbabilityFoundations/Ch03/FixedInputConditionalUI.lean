import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

/-! Proposition 3.9 (paper.tex, 1063–1083). The original probability
space need not be complete. The first statement includes every a.e. equal
representative, simultaneously for all sub-sigma-algebras. The second
statement spells out the family of canonical conditional expectations. -/

open MeasureTheory

universe u

namespace Specs.ProbabilityFoundations.Ch03.FixedInputConditionalUI

open Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
open Specs.ProbabilityFoundations.Ch03.ConditionalExpectationVersions

def allRepresentativesUIType : Prop :=
  ∀ {Ω : Type u} [F : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ), Integrable X P →
    SourceUniformIntegrableValue P
      {U | ∃ G : MeasurableSpace Ω, G ≤ F ∧
        U =ᵐ[P] realConditionalExpectationValue (F := F) G P X}

def canonicalFamilyUIType : Prop :=
  ∀ {Ω : Type u} [F : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ), Integrable X P →
    SourceUniformIntegrableValue P
      {U | ∃ G : MeasurableSpace Ω, G ≤ F ∧
        U = realConditionalExpectationValue (F := F) G P X}

end Specs.ProbabilityFoundations.Ch03.FixedInputConditionalUI
