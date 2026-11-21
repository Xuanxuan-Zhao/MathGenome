import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Invariant
import Mathlib.Topology.Order.Real

/-! Independent statements for the topological part of paper.tex d13:11:omega.
All closures are in the ambient state space. Tails use only actual maximal
times, even for orbits that are not relatively compact or forward complete. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch11.OmegaTopology
open _root_.D13Unified _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def orbitTail (F : AutonomousODE E) (x : E) (s : ℝ) : Set E :=
  (fun t => flow F t x) '' {t | t ∈ (flowInterval F x).carrier ∧ s ≤ t}

def positiveOrbit (F : AutonomousODE E) (x : E) : Set E := orbitTail F x 0

/-- Defined without a compactness or completeness assumption. -/
def omegaValue (F : AutonomousODE E) (x : E) : Set E :=
  ⋂ s : ℝ, ⋂ (_ : 0 ≤ s), closure (orbitTail F x s)

def omegaType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    AutonomousODE E → E → Set E

def CompactOmegaTopology : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, IsCompact (closure (positiveOrbit F x)) →
    closure (positiveOrbit F x) ⊆ F.domain →
      Ici 0 ⊆ (flowInterval F x).carrier ∧
      (omegaValue F x).Nonempty ∧ IsCompact (omegaValue F x) ∧
      IsConnected (omegaValue F x) ∧ omegaValue F x ⊆ closure (positiveOrbit F x)

/-- The sequence takes values only at recorded maximal times. The equivalence
holds without compactness, and thus in particular under the theorem's hypotheses. -/
def SequenceCharacterization : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E) (x y : E),
    y ∈ omegaValue F x ↔ ∃ t : ℕ → ℝ,
      (∀ j, t j ∈ (flowInterval F x).carrier ∧ 0 ≤ t j) ∧
      Tendsto t atTop atTop ∧ Tendsto (fun j => flow F (t j) x) atTop (𝓝 y)

end Specs.D13Unified.Ch11.OmegaTopology
