import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

noncomputable section

open CategoryTheory CategoryTheory.Limits Geometry TopologicalSpace

universe u

namespace RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

open Analytic

variable {σ : Type u}

/-- The relative interior of the convex hull of a face. -/
def faceInterior (s : Finset (σ → ℝ)) : Set (σ → ℝ) :=
  intrinsicInterior ℝ (convexHull ℝ (s : Set (σ → ℝ)))

/-- The piece cut out by a face interior in a space mapping to the coordinate space. -/
def facePiece {X : TopCat.{u}} (f : X ⟶ TopCat.of (σ → ℝ))
    (s : Finset (σ → ℝ)) : Set X :=
  f ⁻¹' faceInterior s

/-- The polyhedron with the subspace topology of the coordinate space. -/
def complexInclusion (K : SimplicialComplex ℝ (σ → ℝ)) :
    TopCat.of K.space ⟶ TopCat.of (σ → ℝ) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- A subset of the polyhedron is a union of whole relative interiors. -/
def IsUnionOfFaceInteriors (K : SimplicialComplex ℝ (σ → ℝ)) (W : Set K.space) : Prop :=
  ∃ T : Set K.faces, W = ⋃ s ∈ T, facePiece (complexInclusion K) s.val

/-- The actual inclusion of one open subset of the polyhedron into another. -/
def stageInclusion {K : SimplicialComplex ℝ (σ → ℝ)}
    {U Y : Opens (TopCat.of K.space)} (h : U ≤ Y) : TopCat.of U ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨fun x => ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- Restriction to a piece equipped with its induced topology. -/
def pieceInclusion {X : TopCat.{u}} (A : Set X) : TopCat.of A ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The nonempty members of an indexed family give a finite locally closed partition. -/
def IsFiniteLocallyClosedPartition {X : Type u} [TopologicalSpace X] {I : Type u}
    (P : I → Set X) : Prop :=
  Finite {i : I // (P i).Nonempty} ∧
    (∀ i, IsLocallyClosed (P i)) ∧
    ∀ x : X, ∃! i : I, x ∈ P i

/-- Bounded cohomology whose restrictions to the face pieces are locally constant
of finite rank. -/
def IsConstructibleOnFaceInteriors (K : SimplicialComplex ℝ (σ → ℝ))
    {X : TopCat.{u}} (f : X ⟶ TopCat.of (σ → ℝ)) (F : BoundedBelow X) : Prop :=
  Set.Finite {q : ℤ | ¬ IsZero ((cohomology X q).obj F.obj)} ∧
    ∀ (s : K.faces) (q : ℤ), LocallyConstantFiniteRank
      ((inverseImage (pieceInclusion (facePiece f s.val))).obj ((cohomology X q).obj F.obj))

namespace Expected

/-- All faces have nonempty relative interior. These interiors partition the polyhedron
and restrict to finite locally closed partitions on its open unions of pieces. -/
def FaceInteriorsPartition : Prop :=
  ∀ (σ : Type u) [Finite σ] (K : SimplicialComplex ℝ (σ → ℝ)), K.faces.Finite →
    (∀ s : K.faces, (facePiece (complexInclusion K) s.val).Nonempty) ∧
    IsFiniteLocallyClosedPartition (fun s : K.faces => facePiece (complexInclusion K) s.val) ∧
    ∀ W : Opens (TopCat.of K.space), IsUnionOfFaceInteriors K (W : Set K.space) →
      IsFiniteLocallyClosedPartition
        (fun s : K.faces => facePiece (openInclusion W ≫ complexInclusion K) s.val)

/-- The bounded-below derived direct image along an open inclusion of unions of
face interiors preserves bounded, simplexwise locally constant finite-rank cohomology. -/
def OpenInclusionConstructibility : Prop :=
  ∀ (σ : Type u) [Finite σ] (K : SimplicialComplex ℝ (σ → ℝ)), K.faces.Finite →
    ∀ (U Y : Opens (TopCat.of K.space)) (h : U ≤ Y),
      IsUnionOfFaceInteriors K (U : Set K.space) → IsUnionOfFaceInteriors K (Y : Set K.space) →
      ∀ F : BoundedBelow (TopCat.of U),
        IsConstructibleOnFaceInteriors K (openInclusion U ≫ complexInclusion K) F →
        IsConstructibleOnFaceInteriors K (openInclusion Y ≫ complexInclusion K)
          ((derivedDirectImage (stageInclusion h)).obj F)

end Expected
end RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage
