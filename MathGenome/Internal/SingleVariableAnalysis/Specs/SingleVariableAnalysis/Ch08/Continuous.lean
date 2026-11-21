import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
Independent specification for K03.08.continuous, paper.tex:2015–2027.
Continuity is relative to the closed interval, including at its endpoints;
no extension or global continuity is required. Integrability is the shared
bounded Darboux predicate, componentwise for complex values. Both statements
include the singleton interval.
-/
namespace Specs.SingleVariableAnalysis.Ch08.Continuous

open Specs.SingleVariableAnalysis.Ch03.Continuity

def realContinuousIntegrable : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    relativeContinuousValue f (Set.Icc a b) → Integral.realIntegrableValue f a b

def complexContinuousIntegrable : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    relativeContinuousValue f (Set.Icc a b) → Integral.complexIntegrableValue f a b

end Specs.SingleVariableAnalysis.Ch08.Continuous
