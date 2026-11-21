import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Finite towers of actual real subfields, for paper.tex:4495--4505.
A successor is any finite extension of degree at most two, not merely a
specified square-root extension. Restricting scalars retains the same subset
of ℝ and the canonical rational embedding. The base case permits zero steps.
-/
namespace D07.Ch15.StraightedgeCompass

inductive QuadraticTower (K : IntermediateField ℚ ℝ) :
    IntermediateField ℚ ℝ → Prop where
  | base : QuadraticTower K K
  | step {M : IntermediateField ℚ ℝ} (previous : QuadraticTower K M)
      (E : IntermediateField M ℝ) (finite : FiniteDimensional M E)
      (degree : Module.finrank M E ≤ 2) : QuadraticTower K (E.restrictScalars ℚ)

end D07.Ch15.StraightedgeCompass

namespace Specs.D07.Ch15.QuadraticTowerIff
open D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

/-- Both coordinates must lie in the same finite real tower. -/
def PointCriterion : Prop := ∀ (P : InitialData) (p : Point),
  isConstructibleValue P p ↔
    ∃ M : IntermediateField ℚ ℝ,
      QuadraticTower (coordinateFieldValue P) M ∧ p.1 ∈ M ∧ p.2 ∈ M

/-- Constructibility of a signed real number means construction on the axis. -/
def RealCriterion : Prop := ∀ (P : InitialData) (a : ℝ),
  isConstructibleRealValue P a ↔
    ∃ M : IntermediateField ℚ ℝ,
      QuadraticTower (coordinateFieldValue P) M ∧ a ∈ M

/-- Separately constructible coordinates admit a common quadratic tower. -/
def CommonTowerCriterion : Prop := ∀ (P : InitialData) (a b : ℝ),
  (isConstructibleRealValue P a ∧ isConstructibleRealValue P b) ↔
    ∃ M : IntermediateField ℚ ℝ,
      QuadraticTower (coordinateFieldValue P) M ∧ a ∈ M ∧ b ∈ M

end Specs.D07.Ch15.QuadraticTowerIff
