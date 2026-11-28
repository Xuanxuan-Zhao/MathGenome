import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace RepTheorySurvey.Geometric.ConvolutionUnitLocalitySpecs

open Analytic

/-- The rational constant sheaf in a single cochain degree. -/
abbrev coefficientComplex (X : TopCat.{u}) (n : ℤ) : CochainComplex.Plus (Sheaves X) :=
  ⟨(CochainComplex.singleFunctor (Sheaves X) n).obj (rational X), n, inferInstance⟩

/-- The unit with the given identification of the pulled-back coefficients. -/
def derivedConstantUnit {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ)
    (a : (inverseImage m).obj (rational X) ≅ rational Y) :
    (DerivedCategory.Plus.Q.obj (coefficientComplex X n)).obj ⟶
      ((derivedDirectImage m).obj (DerivedCategory.Plus.Q.obj (coefficientComplex Y n))).obj := by
  let D := directImage m
  let η := (inverseDirectAdjunction m).unit.app (rational X) ≫ D.map a.hom
  let f := (CochainComplex.singleFunctor (Sheaves X) n).map η
  let e := (HomologicalComplex.singleMapHomologicalComplex D (.up ℤ) n).app (rational Y)
  let g : coefficientComplex X n ⟶ D.mapCochainComplexPlus.obj (coefficientComplex Y n) :=
    ObjectProperty.homMk (f ≫ e.inv)
  exact (DerivedCategory.Plus.Q.map g ≫ D.rightDerivedFunctorPlusUnit.app
    (coefficientComplex Y n)).hom

/-- The restriction of `m` from the inverse image of an open to that open. -/
def restrictToOpen {Y X : TopCat.{u}} (m : Y ⟶ X) (U : Opens X) :
    TopCat.of ((Opens.map m).obj U) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun y => ⟨m y.1, y.2⟩,
    (m.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

namespace Expected

def DerivedConstantUnitType :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ),
    ((inverseImage m).obj (rational X) ≅ rational Y) →
    ((DerivedCategory.Plus.Q.obj (coefficientComplex X n)).obj ⟶
      ((derivedDirectImage m).obj (DerivedCategory.Plus.Q.obj (coefficientComplex Y n))).obj)

/-- The derived unit is invertible over any open where the restricted map is a homeomorphism. -/
def OpenUnit : Prop :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ)
    (a : (inverseImage m).obj (rational X) ≅ rational Y) (U : Opens X),
    IsHomeomorph (restrictToOpen m U) →
      IsIso ((derivedInverseImage (openInclusion U)).map (derivedConstantUnit m n a))

/-- The unit identifies the degree-`n` stalks when the fibre is nonempty and the
target cohomology stalk in that degree is a rational line. -/
def StalkUnit : Prop :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ)
    (a : (inverseImage m).obj (rational X) ≅ rational Y) (x : X),
    x ∈ Set.range m →
    Nonempty ((cohomology X n ⋙ stalk x).obj
      ((derivedDirectImage m).obj (DerivedCategory.Plus.Q.obj (coefficientComplex Y n))).obj ≅
      ModuleCat.of ℚ (ULift.{u} ℚ)) →
    IsIso ((cohomology X n ⋙ stalk x).map (derivedConstantUnit m n a))

end Expected
end RepTheorySurvey.Geometric.ConvolutionUnitLocalitySpecs
