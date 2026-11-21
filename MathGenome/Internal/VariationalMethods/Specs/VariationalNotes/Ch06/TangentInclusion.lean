import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Independent statements for the unconditional part of paper.tex
Proposition `prop:tangent-mfcq` and the tangent first-order necessity in §v06-04.
The statements hold in real normed spaces, hence in the finite-dimensional
spaces of the manuscript. No constraint qualification is imposed. -/
noncomputable section
universe u v w
namespace VariationalNotes.Ch06.Specs

/-- The positive-time feasible-sequence tangent satisfies all active linearizations. -/
def tangent_subset_linearized : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → x ∈ feasibleSet U g h →
    constraintTangentCone U g h x ⊆ linearizedCone g h x

/-- Closedness needs no smoothness or constraint qualification. -/
def constraintTangentCone_isClosed : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    IsClosed (constraintTangentCone U g h x)

/-- Differentiability of the objective at a constrained local minimum suffices. -/
def tangent_first_order_necessary : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    x ∈ feasibleSet U g h → DifferentiableAt ℝ f x →
    IsLocalMinOn f (feasibleSet U g h) x →
    ∀ d ∈ constraintTangentCone U g h x, 0 ≤ fderiv ℝ f x d

end VariationalNotes.Ch06.Specs
