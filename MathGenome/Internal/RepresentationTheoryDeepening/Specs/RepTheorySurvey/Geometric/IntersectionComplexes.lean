import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open TopologicalSpace Topology

universe u

namespace RepTheorySurvey.Geometric.Analytic.IntersectionComplex

/-- The rational coefficient sheaf placed in cohomological degree zero and shifted by
the complex dimension. -/
def shiftedConstant (X : TopCat.{u}) (d : ℕ) : BoundedBelow X :=
  let F := (DerivedCategory.singleFunctor (Sheaves X) 0).obj (rational X)
  ⟨F⟦(d : ℤ)⟧, ⟨-(d : ℤ),
    (DerivedCategory.TStructure.t (C := Sheaves X)).isGE_shift F 0 _ _ (add_neg_cancel _)⟩⟩

/-- Ordinary upper truncation on the bounded-below category, computed in the
ambient derived category. -/
def truncLE (X : TopCat.{u}) (a : ℤ) : BoundedBelow X ⥤ BoundedBelow X :=
  (DerivedCategory.TStructure.t (C := Sheaves X)).plus.lift
    (DerivedCategory.Plus.ι ⋙ (DerivedCategory.TStructure.t (C := Sheaves X)).truncLE a)
    (by
      intro F
      obtain ⟨b, hb⟩ := F.property
      refine ⟨b, ?_⟩
      change DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncLT (a + 1)).obj F.obj) b
      infer_instance)

/-- Adjoin the closed complement of an open inclusion, of complex dimension `s`. -/
def attachment {U X : TopCat.{u}} (j : U ⟶ X) (_hj : IsOpenEmbedding j) (s : ℕ) :
    BoundedBelow U ⥤ BoundedBelow X :=
  derivedDirectImage j ⋙ truncLE X (-(s : ℤ) - 1)

/-- The canonical ordinary truncation triangle of the actual derived direct image. -/
def attachmentTriangle {U X : TopCat.{u}} (j : U ⟶ X) (_hj : IsOpenEmbedding j) (s : ℕ)
    (F : BoundedBelow U) : Triangle (Derived X) :=
  ((DerivedCategory.TStructure.t (C := Sheaves X)).triangleLEGT (-(s : ℤ) - 1)).obj
    ((derivedDirectImage j).obj F).obj

/-- The canonical map from the attachment to the untruncated derived direct image. -/
def attachmentι {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j) (s : ℕ)
    (F : BoundedBelow U) : ((attachment j hj s).obj F).obj ⟶ ((derivedDirectImage j).obj F).obj :=
  (attachmentTriangle j hj s F).mor₁

/-- A finite filtration by open inclusions, ending at `X` with smallest
stratum dimension `s`. An attachment records the dimension of its closed
complement. Strata of the same dimension can be adjoined together. -/
inductive DimensionFiltration : TopCat.{u} → ℕ → Type (u + 1)
  | top (X : TopCat.{u}) (d : ℕ) : DimensionFiltration X d
  | attach {U X : TopCat.{u}} {d s : ℕ} (previous : DimensionFiltration U d)
      (j : U ⟶ X) (isOpen : IsOpenEmbedding j) (dimension_lt : s < d) :
      DimensionFiltration X s

/-- The normalized rational complex of the supplied dimension filtration. -/
def complex {X : TopCat.{u}} {s : ℕ} : DimensionFiltration X s → BoundedBelow X
  | .top X d => shiftedConstant X d
  | .attach previous j hj (s := s) _ => (attachment j hj s).obj (complex previous)

/-- The coefficient complex on a single point with its subspace topology. -/
def point {X : TopCat.{u}} (x : X) : BoundedBelow (TopCat.of ({x} : Set X)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (rational (TopCat.of ({x} : Set X)))

/-- The dimension filtration of a surface with open two-dimensional stratum and
one closed point. -/
def surfaceFiltration {X : TopCat.{u}} (x : X) (hx : IsClosed ({x} : Set X)) :
    DimensionFiltration X 0 :=
  let U := complementOpen {x} hx
  .attach (.top (TopCat.of U) 2) (openInclusion U) U.isOpenEmbedding (by decide)

/-- The normalized complex of the two-stratum surface. -/
def surface {X : TopCat.{u}} (x : X) (hx : IsClosed ({x} : Set X)) : BoundedBelow X :=
  complex (surfaceFiltration x hx)

/-- The rational intersection complex on a closed orbit closure, extended to the
ambient space by derived closed extension by zero. -/
def extendedComplex {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z) {s : ℕ}
    (P : DimensionFiltration (TopCat.of Z) s) : BoundedBelow X := by
  let F := complex P
  refine ⟨(closedExtension hZ).obj F.obj, ?_⟩
  obtain ⟨b, K, e, hK⟩ := F.property
  let i := directImage (closedInclusion Z)
  have := (extraordinaryAdjunction hZ).isLeftAdjoint
  refine ⟨b, (i.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    (closedExtension hZ).mapIso e ≪≫ i.mapDerivedCategoryFactors.app K, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact i.map_isZero (K.isZero_of_isStrictlyGE b n hn)

namespace Expected

def ShiftedConstantType := ∀ (X : TopCat.{u}), ℕ → BoundedBelow X

def TruncLEType := ∀ (X : TopCat.{u}), ℤ → (BoundedBelow X ⥤ BoundedBelow X)

def AttachmentType := ∀ {U X : TopCat.{u}} (j : U ⟶ X), IsOpenEmbedding j →
  ℕ → (BoundedBelow U ⥤ BoundedBelow X)

def AttachmentTriangleType := ∀ {U X : TopCat.{u}} (j : U ⟶ X), IsOpenEmbedding j →
  ℕ → BoundedBelow U → Triangle (Derived X)

def AttachmentιType := ∀ {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j)
    (s : ℕ) (F : BoundedBelow U),
  ((attachment j hj s).obj F).obj ⟶ ((derivedDirectImage j).obj F).obj

def DimensionFiltrationType := TopCat.{u} → ℕ → Type (u + 1)

abbrev dimensionFiltrationModel : DimensionFiltrationType.{u} := DimensionFiltration.{u}

def ComplexType := ∀ {X : TopCat.{u}} {s : ℕ}, DimensionFiltration X s → BoundedBelow X

def PointType := ∀ {X : TopCat.{u}} (x : X), BoundedBelow (TopCat.of ({x} : Set X))

def SurfaceFiltrationType := ∀ {X : TopCat.{u}} (x : X), IsClosed ({x} : Set X) →
  DimensionFiltration X 0

def SurfaceType := ∀ {X : TopCat.{u}} (x : X), IsClosed ({x} : Set X) → BoundedBelow X

def ExtendedComplexType := ∀ {X : TopCat.{u}} {Z : Set X}, IsClosed Z →
  ∀ {s : ℕ}, DimensionFiltration (TopCat.of Z) s → BoundedBelow X

def AttachmentDistinguished : Prop :=
  ∀ {U X : TopCat.{u}} (j : U ⟶ X) (hj : IsOpenEmbedding j)
    (s : ℕ) (F : BoundedBelow U), attachmentTriangle j hj s F ∈ distTriang (Derived X)

def SmoothNormalization : Prop :=
  ∀ (X : TopCat.{u}) (d : ℕ),
    (complex (.top X d)).obj =
      ((DerivedCategory.singleFunctor (Sheaves X) 0).obj (rational X))⟦(d : ℤ)⟧

def PointNormalization : Prop :=
  ∀ {X : TopCat.{u}} (x : X),
    Nonempty (complex (.top (TopCat.of ({x} : Set X)) 0) ≅ point x)

def SurfaceNormalization : Prop :=
  ∀ {X : TopCat.{u}} (x : X) (hx : IsClosed ({x} : Set X)),
    let U := complementOpen {x} hx
    let j := openInclusion U
    (surface x hx).obj =
      ((DerivedCategory.TStructure.t (C := Sheaves X)).truncLE (-1)).obj
        ((derivedDirectImage j).obj (shiftedConstant (TopCat.of U) 2)).obj

end Expected
end RepTheorySurvey.Geometric.Analytic.IntersectionComplex
