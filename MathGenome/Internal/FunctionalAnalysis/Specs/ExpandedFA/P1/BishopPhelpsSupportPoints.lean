import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! Independent specification of the boundary clause of Bishop--Phelps,
`paper.tex:3436–3487`. Convexity is over the real field in both cases.
A support functional must be nonzero. No boundedness of the set, no
nonempty interior, and no initial support functional at the boundary point
are assumed. -/
namespace ExpandedFA.P1.BishopPhelpsSupportPoints.Spec

universe u

def IsRealSupportPoint {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (x : E) : Prop :=
  x ∈ C ∧ ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ C, f y ≤ f x

def IsComplexSupportPoint {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (C : Set E) (x : E) : Prop :=
  x ∈ C ∧ ∃ f : E →L[ℂ] ℂ, f ≠ 0 ∧ ∀ y ∈ C, (f y).re ≤ (f x).re

def RealBoundaryDensity : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    frontier C ⊆ closure {x | IsRealSupportPoint C x}

def ComplexBoundaryDensity : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    frontier C ⊆ closure {x | IsComplexSupportPoint C x}

end ExpandedFA.P1.BishopPhelpsSupportPoints.Spec
