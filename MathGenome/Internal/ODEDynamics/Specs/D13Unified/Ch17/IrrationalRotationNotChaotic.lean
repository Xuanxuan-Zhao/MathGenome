import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.RigidRotation
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ChaosDefinitions

/-!
Independent specification of the Chapter 17 example “Ergodic rotation is not
sensitive”. The circle, rotation, forward orbit, and chaos predicates are the
canonical objects from Chapters 15 and 17. Ergodicity is a separate Chapter 19
obligation. The metric assertions below hold for every real rotation parameter.
-/
namespace Specs.D13Unified.Ch17.IrrationalRotationNotChaotic

open Ch15.CircleLift Ch15.DiscreteDefinitions Ch15.RigidRotation ChaosDefinitions
open scoped Topology

def rotation_isometryStatement : Prop :=
  ∀ α : ℝ, Isometry (rotation α)

/-- An open neighborhood at every point keeps all paired forward iterates
strictly closer than any prescribed positive separation constant. -/
def rotation_small_neighborhoodStatement : Prop :=
  ∀ (α δ : ℝ), 0 < δ → ∀ x : Circle,
    ∃ U : Set Circle, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, ∀ n : ℕ, dist ((rotation α)^[n] x) ((rotation α)^[n] y) < δ

def rotation_not_sensitiveStatement : Prop :=
  ∀ α : ℝ, ¬ SensitiveDependence (rotation α)

def irrational_periodicPoints_eq_emptyStatement : Prop :=
  ∀ (α : ℝ), Irrational α → periodicPoints (rotation α) = ∅

/-- The full topological counterexample, with natural-number forward iterates
and the agreed three-part definition of chaos. -/
def irrational_rotation_not_chaoticStatement : Prop :=
  ∀ (α : ℝ), Irrational α →
    (∀ x : Circle, Dense (orbitSet (rotation α) x)) ∧
    periodicPoints (rotation α) = ∅ ∧
    Isometry (rotation α) ∧
    (∀ (δ : ℝ), 0 < δ → ∀ x : Circle, ∃ U ∈ 𝓝 x,
      ∀ y ∈ U, ∀ n : ℕ, dist ((rotation α)^[n] x) ((rotation α)^[n] y) < δ) ∧
    ¬ SensitiveDependence (rotation α) ∧ ¬ Chaotic (rotation α)

end Specs.D13Unified.Ch17.IrrationalRotationNotChaotic
