import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.IntersectionComplexes

noncomputable section

open CategoryTheory

universe u

namespace RepTheorySurvey.Geometric.IntersectionComplexes

open Analytic

abbrev shiftedConstant : IntersectionComplex.Expected.ShiftedConstantType.{u} :=
  @IntersectionComplex.shiftedConstant.{u}

abbrev truncLE : IntersectionComplex.Expected.TruncLEType.{u} :=
  @IntersectionComplex.truncLE.{u}

abbrev attachment : IntersectionComplex.Expected.AttachmentType.{u} :=
  @IntersectionComplex.attachment.{u}

abbrev attachmentTriangle : IntersectionComplex.Expected.AttachmentTriangleType.{u} :=
  @IntersectionComplex.attachmentTriangle.{u}

abbrev attachmentι : IntersectionComplex.Expected.AttachmentιType.{u} :=
  @IntersectionComplex.attachmentι.{u}

abbrev DimensionFiltration : IntersectionComplex.Expected.DimensionFiltrationType.{u} :=
  @IntersectionComplex.DimensionFiltration.{u}

abbrev complex : IntersectionComplex.Expected.ComplexType.{u} :=
  @IntersectionComplex.complex.{u}

abbrev point : IntersectionComplex.Expected.PointType.{u} :=
  @IntersectionComplex.point.{u}

abbrev surfaceFiltration : IntersectionComplex.Expected.SurfaceFiltrationType.{u} :=
  @IntersectionComplex.surfaceFiltration.{u}

abbrev surface : IntersectionComplex.Expected.SurfaceType.{u} :=
  @IntersectionComplex.surface.{u}

abbrev extendedComplex : IntersectionComplex.Expected.ExtendedComplexType.{u} :=
  @IntersectionComplex.extendedComplex.{u}

theorem attachmentDistinguished : IntersectionComplex.Expected.AttachmentDistinguished.{u} := by
  intro U X j hj s F
  exact (DerivedCategory.TStructure.t (C := Sheaves X)).triangleLEGT_distinguished
    (-(s : ℤ) - 1) ((derivedDirectImage j).obj F).obj

theorem smoothNormalization : IntersectionComplex.Expected.SmoothNormalization.{u} := by
  intro X d
  rfl

theorem pointNormalization : IntersectionComplex.Expected.PointNormalization.{u} := by
  intro X x
  exact ⟨ObjectProperty.isoMk _
    ((shiftFunctorZero (Derived (TopCat.of ({x} : Set X))) ℤ).app (point x).obj)⟩

theorem surfaceNormalization : IntersectionComplex.Expected.SurfaceNormalization.{u} := by
  intro X x hx
  rfl

end RepTheorySurvey.Geometric.IntersectionComplexes
