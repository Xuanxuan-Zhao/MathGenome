import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BishopPhelpsSupportPoints
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent statements of Bishop--Phelps, paper.tex:3436–3445.
The closed unit ball formulation of norm attainment includes the zero space. -/
namespace ExpandedFA.P1.BishopPhelps.Spec

open Set Metric
universe u

def RealApproximation : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (f : E →L[ℝ] ℝ), BddAbove (f '' C) →
    ∀ α : ℝ, 0 < α → ∃ x ∈ C, ∃ g : E →L[ℝ] ℝ,
      ‖g - f‖ ≤ α ∧ ∀ y ∈ C, g y ≤ g x

def ComplexApproximation : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (C : Set E), C.Nonempty → IsClosed C → Convex ℝ C →
    ∀ (f : E →L[ℂ] ℂ), BddAbove ((fun x => (f x).re) '' C) →
    ∀ α : ℝ, 0 < α → ∃ x ∈ C, ∃ g : E →L[ℂ] ℂ,
      ‖g - f‖ ≤ α ∧ ∀ y ∈ C, (g y).re ≤ (g x).re

def RealBoundaryDensity : Prop :=
  BishopPhelpsSupportPoints.Spec.RealBoundaryDensity.{u}

def ComplexBoundaryDensity : Prop :=
  BishopPhelpsSupportPoints.Spec.ComplexBoundaryDensity.{u}

def RealNormAttainingDense : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    Dense {f : E →L[ℝ] ℝ | ∃ x ∈ closedBall (0 : E) 1, ‖f x‖ = ‖f‖}

def ComplexNormAttainingDense : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    Dense {f : E →L[ℂ] ℂ | ∃ x ∈ closedBall (0 : E) 1, ‖f x‖ = ‖f‖}

end ExpandedFA.P1.BishopPhelps.Spec
