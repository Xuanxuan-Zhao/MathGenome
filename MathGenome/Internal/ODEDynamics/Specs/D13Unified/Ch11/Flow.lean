import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.CkDependence
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! Independent statements for paper.tex, Theorem d13:11:flow.
The flow, maximal intervals and domain are the shared canonical objects from
Chapter 6, built from the Chapter 4 maximal solution. All assertions retain
the actual open state domain and allow incomplete solutions. -/
noncomputable section
open Set
open scoped ContDiff

namespace Specs.D13Unified.Ch11.Flow
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual domain of the time-t map, including admissibility of the state. -/
def timeDomainValue (F : AutonomousODE E) (t : ℝ) : Set E :=
  {x | (t,x) ∈ flowDomain F}

def Regularity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
      IsOpen (flowDomain F) ∧
      ContDiffOn ℝ k (fun q : ℝ × E => flow F q.1 q.2) (flowDomain F) ∧
      ∀ q ∈ flowDomain F, flow F q.1 q.2 ∈ F.domain

def InitialValue : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, (0,x) ∈ flowDomain F ∧ flow F 0 x = x

/-- Equality of entire lifespans, not merely an identity on an overlap. -/
def Translation : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ s ∈ (flowInterval F x).carrier,
      (flowInterval F (flow F s x)).carrier =
        {t : ℝ | t+s ∈ (flowInterval F x).carrier} ∧
      ∀ t : ℝ, t+s ∈ (flowInterval F x).carrier →
        flow F t (flow F s x) = flow F (t+s) x

/-- Both directions are Cᵏ on their full open survival domains. -/
def TimeDiffeomorphism : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ), 1 ≤ k → ∀ (F : AutonomousODE E),
    ContDiffOn ℝ k (autonomousEvalValue F) F.domain → ∀ t : ℝ,
      IsOpen (timeDomainValue F t) ∧ IsOpen (timeDomainValue F (-t)) ∧
      (flow F t) '' timeDomainValue F t = timeDomainValue F (-t) ∧
      ∃ e : OpenPartialHomeomorph E E,
        e.source = timeDomainValue F t ∧ e.target = timeDomainValue F (-t) ∧
        (e : E → E) = flow F t ∧ (e.symm : E → E) = flow F (-t) ∧
        ContDiffOn ℝ k e e.source ∧ ContDiffOn ℝ k e.symm e.target

def Pushforward : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ q ∈ flowDomain F,
      (fderiv ℝ (flow F q.1) q.2) (autonomousEvalValue F q.2) =
        autonomousEvalValue F (flow F q.1 q.2)

end Specs.D13Unified.Ch11.Flow
