import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow
import Mathlib.Algebra.Ring.Periodic

/-! Independent statements for paper.tex, Proposition d13:11:orbits.
All orbit sets and injectivity assertions use the actual canonical maximal
interval. Periods on all of ℝ are asserted only together with completeness. -/
noncomputable section
open Set

namespace D13Unified.Ch11.Orbits
open Ch06.StateDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The image of the actual maximal trajectory through time zero. -/
def orbit (F : AutonomousODE E) (x : E) : Set E :=
  (fun t => flow F t x) '' (flowInterval F x).carrier

/-- Constant on its actual interval, with value its initial point. -/
def IsConstant (F : AutonomousODE E) (x : E) : Prop :=
  ∀ t ∈ (flowInterval F x).carrier, flow F t x = x

/-- Completeness concerns the recorded domain, not the total representative. -/
def IsComplete (F : AutonomousODE E) (x : E) : Prop :=
  (flowInterval F x).carrier = univ

/-- A complete trajectory with a least positive period and exactly its integer
multiples as periods, including zero and negative periods. -/
def HasLeastPeriod (F : AutonomousODE E) (x : E) : Prop :=
  IsComplete F x ∧ ∃ T : ℝ, 0 < T ∧
    Function.Periodic (fun t => flow F t x) T ∧
    (∀ S : ℝ, 0 < S → Function.Periodic (fun t => flow F t x) S → T ≤ S) ∧
    ∀ S : ℝ, Function.Periodic (fun t => flow F t x) S ↔
      ∃ k : ℤ, S = (k : ℝ) * T
end D13Unified.Ch11.Orbits

namespace Specs.D13Unified.Ch11.Orbits
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open _root_.D13Unified.Ch11.Orbits
open Ch01.AutonomousParameters
universe u

def EquilibriumCharacterization : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, autonomousEvalValue F p = 0 ↔ IsConstant F p

def EquilibriumComplete : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ p ∈ F.domain, autonomousEvalValue F p = 0 → IsComplete F p

def OrbitPartition : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ y ∈ F.domain,
      Disjoint (orbit F x) (orbit F y) ∨ orbit F x = orbit F y

/-- A self-intersection at two distinct allowed times forces completeness and
periodicity with their actual time difference. Constants are allowed here. -/
def SelfIntersection : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ t₁ ∈ (flowInterval F x).carrier,
    ∀ t₂ ∈ (flowInterval F x).carrier, t₁ ≠ t₂ →
      flow F t₁ x = flow F t₂ x →
      IsComplete F x ∧ Function.Periodic (fun t => flow F t x) (t₂-t₁)

def OrbitAlternatives : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ¬ IsConstant F x →
      Set.InjOn (fun t => flow F t x) (flowInterval F x).carrier ∨ HasLeastPeriod F x

/-- The least-period conclusion applies directly to any self-intersection of a
nonconstant maximal trajectory, at arbitrary distinct times in its interval. -/
def SelfIntersectionLeastPeriod : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ¬ IsConstant F x →
    ∀ t₁ ∈ (flowInterval F x).carrier, ∀ t₂ ∈ (flowInterval F x).carrier,
      t₁ ≠ t₂ → flow F t₁ x = flow F t₂ x → HasLeastPeriod F x
end Specs.D13Unified.Ch11.Orbits
