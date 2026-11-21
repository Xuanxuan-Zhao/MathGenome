import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap

/-! Full product openness and continuity on the actual canonical maximal domain,
`paper.tex`, Theorem d13:05:openness. The coordinates are `(t,((s,ξ),p))`.
No product-domain assumption or parameter differentiability is imposed. -/
noncomputable section
namespace Specs.D13Unified.Ch05.OpenDomain
open _root_.D13Unified
open Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u v

def openDomainExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
      IsOpen (parameterSolutionDomainValue F)

def continuousSolutionMapExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), parameterLocallyLipschitzInStateValue F →
      Continuous (parameterSolutionMapValue F)

end Specs.D13Unified.Ch05.OpenDomain
