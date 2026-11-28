import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe w

namespace RepTheorySurvey.Geometric.FullSupportCounitComparisonSpecs

open Analytic Analytic.IntersectionComplex
open Analytic.DerivedPullbackPasting.Expected (identityValue squareValue)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions)

/-- The direct-image mate for the square with identity on the support,
followed by the direct image of the identity pullback comparison. -/
def fullSupportComparison {X Y V : TopCat.{w}} {i : Y ⟶ X} {j : Y ⟶ V} {t : V ⟶ X}
    (h : j ≫ t = i) (a : DerivedAdjunctions.{w}) (F : BoundedBelow Y) :
    (boundedBelowInverseImage t).obj ((derivedDirectImage i).obj F) ⟶
      (derivedDirectImage j).obj F :=
  directImageComparison (h.trans (Category.id_comp i).symm) (a j) (a i) F ≫
    (derivedDirectImage j).map (ObjectProperty.homMk ((identityValue Y).hom.app F.obj))

namespace Expected

/-- Transposing the full-support comparison gives the counit for the support
inclusion, transported along the factorization through the stage. -/
def FullSupportCounit : Prop :=
  ∀ {X Y V : TopCat.{w}} {i : Y ⟶ X} {j : Y ⟶ V} {t : V ⟶ X}
    (h : j ≫ t = i) (a : DerivedAdjunctions.{w}) (F : BoundedBelow Y),
    let E := (derivedDirectImage i).obj F
    let c := fullSupportComparison h a F
    (derivedInverseImage j).map c.hom ≫ ((a j).counit.app F).hom =
      (derivedInverseImageComposition j t).inv.app E.obj ≫
        eqToHom (congrArg (fun f => (derivedInverseImage f).obj E.obj) h) ≫
        ((a i).counit.app F).hom

/-- Pulling back the full-support transpose gives the intersection transpose.
The latter is written both via the derived pullback square and via the
counit applied to the actual bounded-below intersection mate. -/
def IntersectionCounit : Prop :=
  ∀ {X Y U V : TopCat.{w}} {i : Y ⟶ X} {j : Y ⟶ V} {t : V ⟶ X}
    {v : U ⟶ Y} {u : U ⟶ V}
    (h : j ≫ t = i) (hFactor : v ≫ j = u) (hSquare : u ≫ t = v ≫ i)
    (a : DerivedAdjunctions.{w}) (F : BoundedBelow Y),
    let E := (derivedDirectImage i).obj F
    let G := (derivedInverseImage t).obj E.obj
    let c := fullSupportComparison h a F
    let pulledTranspose :=
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj G) hFactor.symm) ≫
        (derivedInverseImageComposition v j).hom.app G ≫
        (derivedInverseImage v).map
          ((derivedInverseImage j).map c.hom ≫ ((a j).counit.app F).hom)
    let squareTranspose :=
      (squareValue hSquare).hom.app E.obj ≫ (derivedInverseImage v).map ((a i).counit.app F).hom
    let d := directImageComparison hSquare (a u) (a i) F
    pulledTranspose = squareTranspose ∧
      squareTranspose = ((boundedBelowInverseImage u).map d ≫
        (a u).counit.app ((boundedBelowInverseImage v).obj F)).hom

end Expected
end RepTheorySurvey.Geometric.FullSupportCounitComparisonSpecs
