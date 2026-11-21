import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Independent statements for paper.tex, §v01-08 (lines 618–648).
Affine constants absorb the right hand sides of the finitely many inequalities.
The predicate also makes sense algebraically in arbitrary dimension; the image
and closedness assertions below have the manuscript's finite-dimensional scope.
No nonemptiness or positive dimension is required. -/

open Set
noncomputable section
universe u v w
namespace VariationalNotes.ConvexGeometry.Specs

def IsPolyhedronType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Prop

/-- A finite intersection of affine closed halfspaces, including zero rows. -/
def IsPolyhedron {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) : Prop :=
  ∃ s : Finset (E →ᵃ[ℝ] ℝ), C = {x | ∀ a ∈ s, a x ≤ 0}

def affine_equality_two_inequalities : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (a : E →ᵃ[ℝ] ℝ) (b : ℝ),
    {x | a x = b} = {x | a x ≤ b} ∩ {x | -a x ≤ -b}

def polyhedron_empty_univ : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E],
    IsPolyhedron (∅ : Set E) ∧ IsPolyhedron (univ : Set E)

def polyhedron_affine_preimage : Prop :=
  ∀ {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E →ᵃ[ℝ] F) (C : Set F),
    IsPolyhedron C → IsPolyhedron (f ⁻¹' C)

def polyhedron_scalar_projection : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set (ℝ × E)),
    IsPolyhedron C → IsPolyhedron (Prod.snd '' C)

def polyhedron_projection : Prop :=
  ∀ {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] (C : Set (E × F)),
    IsPolyhedron C → IsPolyhedron (Prod.snd '' C)

def polyhedron_coordinate_projection : Prop :=
  ∀ {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (p : κ → ι) (C : Set (ι → ℝ)), IsPolyhedron C →
    IsPolyhedron ((fun x : ι → ℝ => x ∘ p) '' C)

def polyhedron_affine_image : Prop :=
  ∀ {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] (f : E →ᵃ[ℝ] F) (C : Set E),
    IsPolyhedron C → IsPolyhedron (f '' C)

def polyhedron_isClosed : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (C : Set E), IsPolyhedron C → IsClosed C

def polyhedron_affine_image_isClosed : Prop :=
  ∀ {E : Type u} {F : Type v} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℝ F] [T2Space F] (f : E →ᵃ[ℝ] F) (C : Set E),
    IsPolyhedron C → IsClosed (f '' C)

end VariationalNotes.ConvexGeometry.Specs
