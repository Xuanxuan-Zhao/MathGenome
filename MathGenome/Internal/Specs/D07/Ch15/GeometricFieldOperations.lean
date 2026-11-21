import MathGenome.Internal.Specs.D07.Ch15.ConstructibleDefinition
import Mathlib.Analysis.Real.Sqrt

/-! The full geometric field-operations obligation of paper.tex:4484--4504.
These propositions refer to the finite-history definition, with no arithmetic
or projection closure assumed. Initial coordinates may be arbitrary real numbers.
-/
namespace Specs.D07.Ch15.GeometricFieldOperations
open D07.Ch15.StraightedgeCompass
open Specs.D07.Ch15.ConstructibleDefinition

def negType : Prop := ∀ (P : InitialData) (a : ℝ),
  isConstructibleRealValue P a → isConstructibleRealValue P (-a)
def addType : Prop := ∀ (P : InitialData) (a b : ℝ),
  isConstructibleRealValue P a → isConstructibleRealValue P b →
    isConstructibleRealValue P (a + b)
def mulType : Prop := ∀ (P : InitialData) (a b : ℝ),
  isConstructibleRealValue P a → isConstructibleRealValue P b →
    isConstructibleRealValue P (a * b)
def divType : Prop := ∀ (P : InitialData) (a b : ℝ),
  isConstructibleRealValue P a → isConstructibleRealValue P b → b ≠ 0 →
    isConstructibleRealValue P (a / b)
def sqrtType : Prop := ∀ (P : InitialData) (a : ℝ),
  isConstructibleRealValue P a → 0 ≤ a →
    isConstructibleRealValue P (Real.sqrt a)
def projectFstType : Prop := ∀ (P : InitialData) (p : Point),
  isConstructibleValue P p → isConstructibleValue P (p.1, 0)
def projectSndType : Prop := ∀ (P : InitialData) (p : Point),
  isConstructibleValue P p → isConstructibleValue P (0, p.2)
/-- Coordinates produced separately can be used together in a point. -/
def combineType : Prop := ∀ (P : InitialData) (a b : ℝ),
  isConstructibleRealValue P a → isConstructibleRealValue P b →
    isConstructibleValue P (a, b)
end Specs.D07.Ch15.GeometricFieldOperations
