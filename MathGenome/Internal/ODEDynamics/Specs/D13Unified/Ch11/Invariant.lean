import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.StateDerivative

/-! Independent statements for paper.tex, d13:11:invariant. Invariance is
relative to the original open state domain and the actual maximal lifespan.
Completeness is a conclusion of compactness, never part of invariance. -/
noncomputable section
open Set

namespace Specs.D13Unified.Ch11.Invariant
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Stay in S at every nonnegative time at which the maximal solution exists. -/
def positiveInvariantValue (F : AutonomousODE E) (S : Set E) : Prop :=
  S ⊆ F.domain ∧ ∀ x ∈ S, ∀ t ∈ (flowInterval F x).carrier,
    0 ≤ t → flow F t x ∈ S

/-- Stay in S at every time of either sign in the actual maximal interval. -/
def invariantValue (F : AutonomousODE E) (S : Set E) : Prop :=
  S ⊆ F.domain ∧ ∀ x ∈ S, ∀ t ∈ (flowInterval F x).carrier, flow F t x ∈ S

def positiveInvariantType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    AutonomousODE E → Set E → Prop

def invariantType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    AutonomousODE E → Set E → Prop

/-- Compact containment in Ω rules out a finite forward endpoint. -/
def CompactForwardCompleteness : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ S : Set E, IsCompact S → positiveInvariantValue F S →
      ∀ x ∈ S, Ici 0 ⊆ (flowInterval F x).carrier ∧
        ∀ t : ℝ, 0 ≤ t → flow F t x ∈ S

/-- Both finite endpoints are excluded for a compact invariant set. -/
def CompactCompleteness : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ S : Set E, IsCompact S → invariantValue F S →
      ∀ x ∈ S, (flowInterval F x).carrier = univ ∧ ∀ t : ℝ, flow F t x ∈ S

end Specs.D13Unified.Ch11.Invariant
