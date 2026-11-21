import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.CircleLift
import Mathlib.NumberTheory.Real.Irrational

/-!
Independent specification of `paper.tex`, Theorem `d13:15:rigid-rotation`.
The circle and the least-period and forward-orbit predicates are the shared
Chapter 15 objects. Density is explicitly for natural-number iterates.
-/
namespace Specs.D13Unified.Ch15.RigidRotation

open CircleLift DiscreteDefinitions

noncomputable section

def rotationType := ℝ → Circle → Circle

/-- Translation by the class of α on the circle ℝ/ℤ. -/
def rotation : rotationType := fun α x => x + quotientMap α

def rotation_quotientStatement : Prop :=
  ∀ α x : ℝ, rotation α (quotientMap x) = quotientMap (x + α)

def rotation_iterateStatement : Prop :=
  ∀ (α : ℝ) (x : Circle) (n : ℕ),
    (rotation α)^[n] x = x + n • quotientMap α

/-- Integer numerators include negative rotations; the denominator is positive. -/
def rational_leastPeriodStatement : Prop :=
  ∀ (p : ℤ) (q : ℕ), 0 < q → p.natAbs.Coprime q →
    ∀ x : Circle, HasLeastPeriod (rotation ((p : ℝ) / (q : ℝ))) x q

def irrational_dense_forwardOrbitStatement : Prop :=
  ∀ (α : ℝ), Irrational α → ∀ x : Circle, Dense (orbitSet (rotation α) x)

def irrational_not_periodicStatement : Prop :=
  ∀ (α : ℝ), Irrational α → ∀ (x : Circle) (n : ℕ),
    0 < n → (rotation α)^[n] x ≠ x

/-- This holds for every real rotation parameter, including rational ones. -/
def iterate_distStatement : Prop :=
  ∀ (α : ℝ) (x y : Circle) (n : ℕ),
    dist ((rotation α)^[n] x) ((rotation α)^[n] y) = dist x y

end
end Specs.D13Unified.Ch15.RigidRotation
