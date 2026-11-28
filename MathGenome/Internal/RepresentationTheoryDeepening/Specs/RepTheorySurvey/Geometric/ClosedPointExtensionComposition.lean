import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportBaseChange

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedPointExtensionCompositionSpecs

open Analytic Analytic.IntersectionComplex LocalSheaf
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes)

/-- Right adjoint uniqueness for the composite closed inclusion, followed by the
comparison of the derived point image with the exact closed extension. -/
def closedPointComposition {X Y : TopCat.{0}} {x : Y}
    (hx : IsClosed ({x} : Set Y)) (i : Y ⟶ X) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx) :
    derivedDirectImage (closedInclusion ({x} : Set Y) ≫ i) ≅
      closedExtensionPlus hx ⋙ derivedDirectImage i :=
  let p := closedInclusion ({x} : Set Y)
  let composite := ((a i).comp (a p)).ofNatIsoLeft (boundedBelowPullbackComposition p i).symm
  (a (p ≫ i)).rightAdjointUniq composite ≪≫
    Functor.isoWhiskerRight ((a p).rightAdjointUniq b) (derivedDirectImage i)

namespace Expected

/-- At one stage and a common jet, the canonical composite comparison intertwines
the two stage arrows. The two range equalities describe the actual surface and
point intersections, including when either intersection is empty. -/
def ClosedPointCompositionEquivariant : Prop :=
  ∀ {X Y Z U V : TopCat.{0}} {x : Y}
    (hx : IsClosed ({x} : Set Y)) {i : Y ⟶ X} (_hi : IsClosedEmbedding i)
    {t : Z ⟶ X} {j : U ⟶ Z} {m : V ⟶ Z} {l : V ⟶ U}
    {v : U ⟶ Y} {w : V ⟶ TopCat.of ({x} : Set Y)}
    (_hj : IsClosedEmbedding j) (_hm : IsClosedEmbedding m)
    (hSurface : j ≫ t = v ≫ i)
    (_rSurface : Set.range j = t ⁻¹' Set.range i)
    (hPoint : m ≫ t = w ≫ (closedInclusion ({x} : Set Y) ≫ i))
    (_rPoint : Set.range m = t ⁻¹' Set.range (closedInclusion ({x} : Set Y) ≫ i))
    (_hStage : l ≫ j = m) (hIntersection : l ≫ v = w ≫ closedInclusion ({x} : Set Y))
    {H : AnalyticGroup.{0}} (A : AnalyticAction H Z) (B : AnalyticAction H U)
    (C : AnalyticAction H V)
    (hA : parameterInclusion H j ≫ A.act = B.act ≫ j)
    (hB : parameterInclusion H m ≫ A.act = C.act ≫ m)
    (hC : parameterInclusion H l ≫ B.act = C.act ≫ l)
    (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx)
    (F : BoundedBelow (TopCat.of ({x} : Set Y))),
    let E := (derivedDirectImage (closedInclusion ({x} : Set Y) ≫ i)).obj F
    let K := (closedExtensionPlus hx).obj F
    let G := (derivedDirectImage i).obj K
    let c := ((closedPointComposition hx i a b).hom.app F).hom
    let E₀ := (derivedInverseImage t).obj E.obj
    let G₀ := (derivedInverseImage t).obj G.obj
    let K₀ := (derivedInverseImage v).obj K.obj
    let F₀ := (derivedInverseImage w).obj F.obj
    let q := AnalyticAction.projection H Z
    let r := AnalyticAction.projection H U
    let s := AnalyticAction.projection H V
    let cSurface := directImageComparison hSurface (a j) (a i) K
    let cPoint := directImageComparison hPoint (a m) (a (closedInclusion ({x} : Set Y) ≫ i)) F
    let cIntersection := adjointSquareMap (pullbackSquare hIntersection) (a l) b F
    ∀ (α : (derivedInverseImage A.act).obj E₀ ⟶ (derivedInverseImage q).obj E₀)
      (β : (derivedInverseImage A.act).obj G₀ ⟶ (derivedInverseImage q).obj G₀)
      (γ : (derivedInverseImage B.act).obj K₀ ⟶ (derivedInverseImage r).obj K₀)
      (δ : (derivedInverseImage C.act).obj F₀ ⟶ (derivedInverseImage s).obj F₀),
      MateCommutes hB (projectionSquare H m) (a (parameterInclusion H m)) (a m)
        cPoint α δ →
      MateCommutes hA (projectionSquare H j) (a (parameterInclusion H j)) (a j)
        cSurface β γ →
      MateCommutes hC (projectionSquare H l) (a (parameterInclusion H l)) (a l)
        cIntersection γ δ →
      (derivedInverseImage A.act).map ((derivedInverseImage t).map c) ≫ β =
        α ≫ (derivedInverseImage q).map ((derivedInverseImage t).map c)

end Expected
end RepTheorySurvey.Geometric.ClosedPointExtensionCompositionSpecs
