import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.DerivativeCriterion
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.LinearVolterra
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Independent specification of the autonomous initial-state stage of
paper.tex, d13:06:c1-dependence. All times belong to the actual maximal
interval through (0, ξ). Compact intervals may extend to either side of zero
and may be singletons. The variational equation is an operator equation,
with composition, in the same fixed norm as the state space. -/
noncomputable section
open Set

namespace D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch04.MaximalSolutionMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical maximal curve, with its recorded actual time interval. -/
def flow (F : AutonomousODE E) (t : ℝ) (ξ : E) : E :=
  solutionCurveValue (autonomousToODEValue F) 0 ξ t

def flowInterval (F : AutonomousODE E) (ξ : E) : OpenTimeInterval :=
  maximalIntervalValue (autonomousToODEValue F) 0 ξ

def flowDomain (F : AutonomousODE E) : Set (ℝ × E) :=
  {q | q.2 ∈ F.domain ∧ q.1 ∈ (flowInterval F q.2).carrier}

/-- The coefficient is defined from the field derivative, independently of
any differentiability assertion for `flow`. -/
def coefficient (F : AutonomousODE E) (ξ : E) (t : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (autonomousEvalValue F) (flow F t ξ)

/-- The full continuous operator-valued integral equation, on [a,b]. -/
def IsVariation (F : AutonomousODE E) (ξ : E) (a b : ℝ)
    (Y : ℝ → E →L[ℝ] E) : Prop :=
  ContinuousOn Y (Icc a b) ∧
    ∀ t ∈ Icc a b,
      Y t = ContinuousLinearMap.id ℝ E +
        ∫ r in (0 : ℝ)..t, (coefficient F ξ r).comp (Y r)

end D13Unified.Ch06.StateDerivative

namespace Specs.D13Unified.Ch06.StateDerivative
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters

universe u

/-- Independent construction and uniqueness of the variational solution,
including endpoint derivatives. No flow derivative is an input. -/
def VariationalExistence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ ξ ∈ F.domain, ∀ a b : ℝ, 0 ∈ Icc a b →
      Icc a b ⊆ (flowInterval F ξ).carrier →
      ∃ Y : ℝ → E →L[ℝ] E, IsVariation F ξ a b Y ∧
        Y 0 = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc a b, HasDerivWithinAt Y
          ((coefficient F ξ t).comp (Y t)) (Icc a b) t) ∧
        ∀ Z, IsVariation F ξ a b Z → EqOn Z Y (Icc a b)

/-- The same independently constructed solution is the initial-state
Fréchet derivative at every allowed terminal time. -/
def StateDerivativeExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ ξ ∈ F.domain, ∀ a b : ℝ, 0 ∈ Icc a b →
      Icc a b ⊆ (flowInterval F ξ).carrier →
      ∀ Y, IsVariation F ξ a b Y →
        ∀ t ∈ Icc a b, HasFDerivAt (fun η => flow F t η) (Y t) ξ

/-- Local joint continuity of independently constructed variations, with a
common compact existence interval for all states in an open neighborhood.
This formulation gives local joint continuity in (t,ξ); uniqueness identifies
these families on overlapping compact intervals. -/
def LocalJointVariation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ ξ ∈ F.domain, ∀ a b : ℝ, 0 ∈ Icc a b →
      Icc a b ⊆ (flowInterval F ξ).carrier →
      ∃ V : Set E, IsOpen V ∧ ξ ∈ V ∧ V ⊆ F.domain ∧
        (∀ η ∈ V, Icc a b ⊆ (flowInterval F η).carrier) ∧
        ∃ Y : E → ℝ → E →L[ℝ] E,
          (∀ η ∈ V, IsVariation F η a b (Y η)) ∧
          ContinuousOn (fun q : ℝ × E => Y q.2 q.1) (Icc a b ×ˢ V)

/-- The assembled assertion on the actual open maximal domain. The state
variation is the ambient Fréchet derivative there; its time equation has
ordinary derivatives on the actual open interval, and it is unique among
classical operator-valued solutions on that whole interval. -/
def MaximalDomainDerivative : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    (∀ q ∈ flowDomain F,
      HasFDerivAt (fun η => flow F q.1 η) (fderiv ℝ (fun η => flow F q.1 η) q.2) q.2) ∧
    ContinuousOn (fun q : ℝ × E => fderiv ℝ (fun η => flow F q.1 η) q.2) (flowDomain F) ∧
    ∀ ξ ∈ F.domain,
      (fderiv ℝ (fun η => flow F 0 η) ξ = ContinuousLinearMap.id ℝ E) ∧
      (∀ t ∈ (flowInterval F ξ).carrier,
        HasDerivAt (fun r => fderiv ℝ (fun η => flow F r η) ξ)
          ((coefficient F ξ t).comp (fderiv ℝ (fun η => flow F t η) ξ)) t) ∧
      ∀ Z : ℝ → E →L[ℝ] E,
        ContinuousOn Z (flowInterval F ξ).carrier → Z 0 = ContinuousLinearMap.id ℝ E →
        (∀ t ∈ (flowInterval F ξ).carrier,
          HasDerivAt Z ((coefficient F ξ t).comp (Z t)) t) →
        EqOn Z (fun t => fderiv ℝ (fun η => flow F t η) ξ) (flowInterval F ξ).carrier

end Specs.D13Unified.Ch06.StateDerivative
