import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.TangentInclusion
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Proposition `prop:tangent-mfcq`, paper.tex §v06-03. The data are C¹ on
an open domain in a finite-dimensional real space. All constraint index types
may be empty. The unconditional inclusion has no qualification hypothesis. -/
noncomputable section
universe u v w
namespace VariationalNotes.Ch06.Specs

/-- The reverse tangent inclusion under precisely MFCQ. -/
def linearized_subset_tangent_of_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → MFCQ U g h x →
    linearizedCone g h x ⊆ constraintTangentCone U g h x

/-- MFCQ gives exact equality of the positive-time sequential tangent and Clin. -/
def tangent_eq_linearized_of_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → MFCQ U g h x →
    constraintTangentCone U g h x = linearizedCone g h x

/-- Independence of the combined differential family implies MFCQ, including
empty active or equality families and zero-dimensional spaces. -/
def licq_implies_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    LICQ U g h x → MFCQ U g h x

/-- The full proposition, retaining its unconditional assertion independently
of the qualified equality and the implication between qualifications. -/
def tangent_mfcq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    IsOpen U → (∀ i, ContDiffOn ℝ 1 (g i) U) →
    (∀ j, ContDiffOn ℝ 1 (h j) U) → x ∈ feasibleSet U g h →
    constraintTangentCone U g h x ⊆ linearizedCone g h x ∧
      (MFCQ U g h x → constraintTangentCone U g h x = linearizedCone g h x) ∧
      (LICQ U g h x → MFCQ U g h x)

end VariationalNotes.Ch06.Specs
