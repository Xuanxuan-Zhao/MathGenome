import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap

/-! Independent statements for paper.tex, Proposition d13:04:rebase.
The intervals are compared as their actual sets of times. The solution values
are compared only there; no identity of ambient representatives is required.
The parameter remains fixed, and the field may depend on absolute time. -/
noncomputable section
open Set
open D13Unified

namespace Specs.D13Unified.Ch04.Rebase
open Specs.D13Unified.Ch03.LocalLipschitz
open Specs.D13Unified.Ch04.MaximalSolutionMap
universe u v

/-- Rebasing a nonautonomous maximal solution preserves its entire actual
interval and all solution values on that interval. -/
def rebaseExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E),
    locallyLipschitzInStateValue F →
    ∀ (s : ℝ) (ξ : E), (s, ξ) ∈ F.domain →
    ∀ (r : ℝ), r ∈ (maximalIntervalValue F s ξ).carrier →
    ∀ (η : E), η = solutionValueValue F r s ξ →
      (maximalIntervalValue F r η).carrier = (maximalIntervalValue F s ξ).carrier ∧
      ∀ t ∈ (maximalIntervalValue F s ξ).carrier,
        solutionValueValue F t r η = solutionValueValue F t s ξ

/-- The same rebasing law for a continuous parameter-dependent field with
local state Lipschitz control uniform in time and nearby parameters. Every
occurrence uses the original triple domain and the same constant parameter. -/
def parameterRebaseExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] (F : ParameterODE E P),
    parameterLocallyLipschitzInStateValue F →
    ∀ (s : ℝ) (ξ : E) (p : P), ((s, ξ), p) ∈ F.domain →
    ∀ (r : ℝ), r ∈ (parameterMaximalIntervalValue F s ξ p).carrier →
    ∀ (η : E), η = parameterSolutionValueValue F r s ξ p →
      (parameterMaximalIntervalValue F r η p).carrier =
        (parameterMaximalIntervalValue F s ξ p).carrier ∧
      ∀ t ∈ (parameterMaximalIntervalValue F s ξ p).carrier,
        parameterSolutionValueValue F t r η p = parameterSolutionValueValue F t s ξ p

end Specs.D13Unified.Ch04.Rebase
