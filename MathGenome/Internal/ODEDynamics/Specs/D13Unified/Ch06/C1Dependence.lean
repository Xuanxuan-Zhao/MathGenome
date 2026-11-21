import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.Autonomization
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.StateDerivative

/-! Independent full statement of paper.tex, Theorem d13:06:c1-dependence.
The solution is the shared canonical maximal solution, with coordinates
`(t,((s,ξ),p))`. All derivatives below are ambient derivatives at points of
its actual open domain; values of the totalization outside that domain
have no mathematical role. -/
noncomputable section
open Set

namespace D13Unified.Ch06.C1Dependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def field (F : ParameterODE E P) (q : (ℝ × E) × P) : E :=
  parameterEvalValue F q.1.1 q.1.2 q.2

def solution (F : ParameterODE E P) (q : ℝ × ((ℝ × E) × P)) : E :=
  parameterSolutionValueValue F q.1 q.2.1.1 q.2.1.2 q.2.2

def stateVariation (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) (t : ℝ) :
    E →L[ℝ] E := fderiv ℝ (fun η => solution F (t,((s,η),p))) ξ

def parameterVariation (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) (t : ℝ) :
    P →L[ℝ] E := fderiv ℝ (fun q => solution F (t,((s,ξ),q))) p

def stateCoefficient (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) (t : ℝ) :
    E →L[ℝ] E := fderiv ℝ (fun x => parameterEvalValue F t x p)
      (solution F (t,((s,ξ),p)))

def parameterCoefficient (F : ParameterODE E P) (s : ℝ) (ξ : E) (p : P) (t : ℝ) :
    P →L[ℝ] E := fderiv ℝ (fun q => parameterEvalValue F t
      (solution F (t,((s,ξ),p))) q) p

end D13Unified.Ch06.C1Dependence

namespace Specs.D13Unified.Ch06.C1Dependence
open _root_.D13Unified _root_.D13Unified.Ch06.C1Dependence
open Ch04.MaximalSolutionMap
universe u v

/-- Joint regularity includes terminal time, starting time, state, and parameter. -/
def JointC1 : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ 1 (field F) F.domain →
      IsOpen (parameterSolutionDomainValue F) ∧
      ContDiffOn ℝ 1 (solution F) (parameterSolutionDomainValue F)

def TerminalDerivative : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ 1 (field F) F.domain →
    ∀ t s ξ p, (t,((s,ξ),p)) ∈ parameterSolutionDomainValue F →
      HasDerivAt (fun r => solution F (r,((s,ξ),p)))
        (Ch01.AutonomousParameters.parameterEvalValue F t (solution F (t,((s,ξ),p))) p) t

/-- Existence of the actual state derivative and its uniquely characterizing
operator equation on the entire maximal interval, with initial identity. -/
def StateVariation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ 1 (field F) F.domain →
    ∀ s ξ p, ((s,ξ),p) ∈ F.domain →
      stateVariation F s ξ p s = ContinuousLinearMap.id ℝ E ∧
      (∀ t ∈ (parameterMaximalIntervalValue F s ξ p).carrier,
        HasFDerivAt (fun η => solution F (t,((s,η),p))) (stateVariation F s ξ p t) ξ ∧
        HasDerivAt (stateVariation F s ξ p)
          ((stateCoefficient F s ξ p t).comp (stateVariation F s ξ p t)) t) ∧
      ∀ Y : ℝ → E →L[ℝ] E,
        ContinuousOn Y (parameterMaximalIntervalValue F s ξ p).carrier →
        Y s = ContinuousLinearMap.id ℝ E →
        (∀ t ∈ (parameterMaximalIntervalValue F s ξ p).carrier,
          HasDerivAt Y ((stateCoefficient F s ξ p t).comp (Y t)) t) →
        EqOn Y (stateVariation F s ξ p) (parameterMaximalIntervalValue F s ξ p).carrier

/-- The parameter derivative is constructed, rather than assumed. Parameters
are fixed along each underlying trajectory and are allowed to vary as data. -/
def ParameterVariation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ 1 (field F) F.domain →
    ∀ s ξ p, ((s,ξ),p) ∈ F.domain →
      parameterVariation F s ξ p s = 0 ∧
      (∀ t ∈ (parameterMaximalIntervalValue F s ξ p).carrier,
        HasFDerivAt (fun q => solution F (t,((s,ξ),q))) (parameterVariation F s ξ p t) p ∧
        HasDerivAt (parameterVariation F s ξ p)
          ((stateCoefficient F s ξ p t).comp (parameterVariation F s ξ p t) +
            parameterCoefficient F s ξ p t) t) ∧
      ∀ Z : ℝ → P →L[ℝ] E,
        ContinuousOn Z (parameterMaximalIntervalValue F s ξ p).carrier →
        Z s = 0 →
        (∀ t ∈ (parameterMaximalIntervalValue F s ξ p).carrier,
          HasDerivAt Z ((stateCoefficient F s ξ p t).comp (Z t) +
            parameterCoefficient F s ξ p t) t) →
        EqOn Z (parameterVariation F s ξ p) (parameterMaximalIntervalValue F s ξ p).carrier

/-- Joint continuity of the actual state and parameter derivatives, including
variation of both time coordinates, on the full maximal domain. -/
def ContinuousVariations : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (F : ParameterODE E P), ContDiffOn ℝ 1 (field F) F.domain →
      ContinuousOn (fun q : ℝ × ((ℝ × E) × P) =>
        stateVariation F q.2.1.1 q.2.1.2 q.2.2 q.1) (parameterSolutionDomainValue F) ∧
      ContinuousOn (fun q : ℝ × ((ℝ × E) × P) =>
        parameterVariation F q.2.1.1 q.2.1.2 q.2.2 q.1) (parameterSolutionDomainValue F)

end Specs.D13Unified.Ch06.C1Dependence
