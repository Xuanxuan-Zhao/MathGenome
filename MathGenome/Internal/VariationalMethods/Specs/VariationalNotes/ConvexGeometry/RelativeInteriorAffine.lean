import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeInteriorIntersections

/-! Independent statements for paper.tex, Theorem `thm:ri-calculus`.
Affine maps need not be injective or surjective. Relative interiors are taken
in the affine hull, including for lower-dimensional sets. -/

open Set
open scoped Pointwise
universe u v w
namespace VariationalNotes.ConvexGeometry.Specs

def relativeInterior_affine_image : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
    [FiniteDimensional ℝ F],
  ∀ (A : E →ᵃ[ℝ] F) (C : Set E), Convex ℝ C → C.Nonempty →
    relativeInterior (A '' C) = A '' relativeInterior C

/-- The qualification is a point in the range and the relative interior of D. -/
def relativeInterior_affine_preimage : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
    [FiniteDimensional ℝ F],
  ∀ (A : E →ᵃ[ℝ] F) (D : Set F), Convex ℝ D →
    (range A ∩ relativeInterior D).Nonempty →
    relativeInterior (A ⁻¹' D) = A ⁻¹' relativeInterior D

/-- Product formula used in the proof of the sum formula. -/
def relativeInterior_product : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {F : Type v} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [T2Space F]
    [FiniteDimensional ℝ F],
  ∀ (C : Set E) (D : Set F), Convex ℝ C → C.Nonempty →
    Convex ℝ D → D.Nonempty →
    relativeInterior (C ×ˢ D) = relativeInterior C ×ˢ relativeInterior D

/-- Minkowski sum formula in one ambient space. -/
def relativeInterior_minkowski_sum : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C D : Set E),
    Convex ℝ C → C.Nonempty → Convex ℝ D → D.Nonempty →
    relativeInterior (C + D) = relativeInterior C + relativeInterior D

/-- All clauses of the source theorem, with each clause's own hypotheses. -/
def relativeInterior_calculus : Prop :=
  closure_relativeInterior.{u} ∧ relativeInterior_closure.{u} ∧
  relativeInterior_iInter.{u,w} ∧ closure_iInter.{u,w} ∧
  relativeInterior_affine_image.{u,v} ∧ relativeInterior_affine_preimage.{u,v} ∧
  relativeInterior_product.{u,v} ∧
  relativeInterior_minkowski_sum.{u}

end VariationalNotes.ConvexGeometry.Specs
