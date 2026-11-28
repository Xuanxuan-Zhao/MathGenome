import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace RepTheorySurvey.Geometric.EquivariantClosedDirectImageCompositionSpecs

open Analytic Analytic.IntersectionComplex LocalSheaf EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (above parameterInclusion projectionSquare
  ActionSquares ComparisonsAreIso MatchesComparisons)

/-- The normalized comparison for ordinary derived direct image, computed using
the two canonical mates for the action and projection squares. -/
def EquivariantDirectImageComparison {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (a : DerivedAdjunctions) (A : JetAction J X) (B : JetAction J Y)
    (f : X ⟶ Y) (h : JetMapsCommute A B f) (F : BoundedBelow X)
    (α : A.Equivariance F.obj) (G : BoundedBelow Y) (β : B.Equivariance G.obj) : Prop :=
  ∃ c : (derivedDirectImage f).obj F ≅ G,
    ∀ (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k),
      let H := J.group k
      let t := parameterInclusion H f
      let act := directImageComparison (h k hx hy) (a t) (a f) F
      let proj := directImageComparison (projectionSquare H f) (a t) (a f) F
      let γ : (boundedBelowInverseImage (A.action k hx).act).obj F ⟶
          (boundedBelowInverseImage (AnalyticAction.projection (J.group k) X)).obj F :=
        ObjectProperty.homMk (α.datum k hx).iso.hom
      IsIso act ∧ IsIso proj ∧
        (derivedInverseImage (B.action k hy).act).map c.hom.hom ≫ (β.datum k hy).iso.hom ≫
          (derivedInverseImage (AnalyticAction.projection (J.group k) Y)).map c.inv.hom ≫
          proj.hom = act.hom ≫ ((derivedDirectImage t).map γ).hom

/-- The predicate identifying the equivariance given by closed-extension
compatibility. Its mates use the exact extension as their right adjoint over
the closed inclusion, and ordinary derived direct image over the product. -/
def ClosedExtensionArrow {J : JetSystem.{0}} {W : TopCat.{0}} {Z : Set W}
    (a : DerivedAdjunctions) (hZ : IsClosed Z)
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (A : JetAction J (TopCat.of Z)) (B : JetAction J W)
    (h : JetMapsCommute A B (closedInclusion Z))
    (G : BoundedBelow (TopCat.of Z)) (β : A.Equivariance G.obj)
    (δ : (above B A.cutoff).Equivariance ((closedExtensionPlus hZ).obj G).obj) : Prop :=
  let squares : ActionSquares B A := fun k hw hz => h k hz hw
  ComparisonsAreIso hZ squares (@a) b G ∧ MatchesComparisons hZ squares (@a) b G β δ

/-- A closed extension realizes ordinary derived direct image, with the same
counit. The terminal comparison uses the equivariance produced by the exact
closed extension at all common jet levels. -/
def EquivariantClosedDirectImageComposition : Prop :=
  ∀ {J : JetSystem.{0}} (a : DerivedAdjunctions)
    (b : ∀ {W : TopCat.{0}} {Z : Set W} (hZ : IsClosed Z),
      boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ),
    ClosedExtensionCompatibility J →
    ∀ {X Y W : TopCat.{0}} {Z : Set W} (hZ : IsClosed Z)
      (f : X ≅ Y) (v : Y ≅ TopCat.of Z)
      (A_X : JetAction J X) (A_Y : JetAction J Y) (A_Z : JetAction J (TopCat.of Z))
      (B : JetAction J W),
      A_X.cutoff ≤ A_Y.cutoff → A_Y.cutoff ≤ A_Z.cutoff →
      ∀ (hf : JetMapsCommute A_X A_Y f.hom) (hv : JetMapsCommute A_Y A_Z v.hom)
        (hi : JetMapsCommute A_Z B (closedInclusion Z))
        (F : BoundedBelow X) (α : A_X.Equivariance F.obj)
        (G : BoundedBelow Y) (β : A_Y.Equivariance G.obj)
        (G_Z : BoundedBelow (TopCat.of Z)) (β_Z : A_Z.Equivariance G_Z.obj),
        EquivariantDirectImageComparison a A_X A_Y f.hom hf F α G β →
        EquivariantDirectImageComparison a A_Y A_Z v.hom hv G β G_Z β_Z →
        let i := closedInclusion Z
        ∃ c : derivedDirectImage i ≅ closedExtensionPlus hZ,
          (∀ K : BoundedBelow (TopCat.of Z),
            (boundedBelowInverseImage i).map (c.hom.app K) ≫ (b hZ).counit.app K =
              (a i).counit.app K) ∧
          ∃ (δ : (above B A_Z.cutoff).Equivariance ((closedExtensionPlus hZ).obj G_Z).obj)
            (h : JetMapsCommute A_X (above B A_Z.cutoff) (f.hom ≫ v.hom ≫ i)),
            ClosedExtensionArrow a hZ (b hZ) A_Z B hi G_Z β_Z δ ∧
            EquivariantDirectImageComparison a A_X (above B A_Z.cutoff) (f.hom ≫ v.hom ≫ i) h
              F α ((closedExtensionPlus hZ).obj G_Z) δ

end RepTheorySurvey.Geometric.EquivariantClosedDirectImageCompositionSpecs
