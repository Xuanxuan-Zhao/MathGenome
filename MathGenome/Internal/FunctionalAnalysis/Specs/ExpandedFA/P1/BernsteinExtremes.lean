import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
The normalized compact-extreme stage of `fa2:p1:bernstein`, paper.tex:5534–5567.
Time is the nonnegative real half-line. The function space has its ordinary
product topology and real pointwise vector operations. Differences are written
with the alternating sign built in. Allowing a zero increment is equivalent to
requiring positive increments: any difference containing a zero increment is zero.
No continuity at the origin is part of the definition.
-/
noncomputable section

open scoped NNReal

namespace ExpandedFA.P1.Bernstein

abbrev FunctionSpace := ℝ≥0 → ℝ

/-- The signed iterated forward difference, with independently chosen increments. -/
def alternatingDifference : List ℝ≥0 → FunctionSpace → FunctionSpace
  | [], f => f
  | h :: hs, f => fun t => alternatingDifference hs f t - alternatingDifference hs f (t + h)

/-- The redundant interval bounds make the ambient compact product explicit. -/
def normalizedFunctions : Set FunctionSpace :=
  {f | f 0 = 1 ∧ (∀ t, f t ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ hs t, 0 ≤ alternatingDifference hs f t}

/-- Finite parameters, including the constant one function at parameter zero. -/
def finiteExponential (rate : ℝ≥0) : FunctionSpace := fun t => Real.exp (-(rate : ℝ) * t)

/-- The compactification endpoint, with its essential value one at zero. -/
def infinityExponential : FunctionSpace := fun t => if t = 0 then 1 else 0

def exponentials : Set FunctionSpace :=
  {f | f = infinityExponential ∨ ∃ rate : ℝ≥0, f = finiteExponential rate}

end ExpandedFA.P1.Bernstein

namespace Specs.ExpandedFA.P1.BernsteinExtremes
open ExpandedFA.P1.Bernstein

def differenceCharacterizationType : Prop :=
  ∀ f : FunctionSpace, f ∈ normalizedFunctions ↔
    f 0 = 1 ∧ ∀ hs t, 0 ≤ alternatingDifference hs f t

/-- This uses exactly the strictly positive increments in the manuscript. -/
def positiveIncrementCharacterizationType : Prop :=
  ∀ f : FunctionSpace, f ∈ normalizedFunctions ↔
    f 0 = 1 ∧ ∀ hs : List ℝ≥0, (∀ h ∈ hs, 0 < h) →
      ∀ t, 0 ≤ alternatingDifference hs f t

def constantOneType : Prop := finiteExponential 0 = fun _ => 1

def compactConvexType : Prop :=
  normalizedFunctions.Nonempty ∧ IsCompact normalizedFunctions ∧ Convex ℝ normalizedFunctions

def extremeClassificationType : Prop :=
  ExpandedFA.P1.C24FacesSpec.extremePoints normalizedFunctions ⊆ exponentials

def exponentialMembershipType : Prop := exponentials ⊆ normalizedFunctions

def compactExponentialsType : Prop := IsCompact exponentials

def closedConvexHullType : Prop :=
  normalizedFunctions = closure (convexHull ℝ exponentials)

end Specs.ExpandedFA.P1.BernsteinExtremes
