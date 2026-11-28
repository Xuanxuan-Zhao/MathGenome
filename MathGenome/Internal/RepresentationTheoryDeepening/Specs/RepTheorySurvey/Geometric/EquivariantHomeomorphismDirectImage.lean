import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImageSpecs

open Analytic Analytic.IntersectionComplex EquivariantIntersectionComplexesSpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)

/-- The inverse-image isomorphism respects the equivariance arrows at every common jet level. -/
def PullbackIntertwines {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {f : X ⟶ Y} (h : JetMapsCommute A B f)
    {F : BoundedBelow X} {G : BoundedBelow Y} (α : A.Equivariance F.obj)
    (β : B.Equivariance G.obj) (c : (boundedBelowInverseImage f).obj G ≅ F) : Prop :=
  ∀ (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k),
    let act := (A.action k hx).act
    let p := AnalyticAction.projection (J.group k) X
    (derivedInverseImage act).map c.hom.hom ≫ (α.datum k hx).iso.hom =
      restrictedArrow h β k hx hy ≫
        (derivedInverseImage p).map c.hom.hom

/-- The action and projection mates are invertible and carry the source equivariance to the
target equivariance through the given direct-image isomorphism. -/
def DirectImageIntertwines {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (a : DerivedAdjunctions) (A : JetAction J X) (B : JetAction J Y)
    {f : X ⟶ Y} (h : JetMapsCommute A B f) (F : BoundedBelow X)
    (α : A.Equivariance F.obj) (G : BoundedBelow Y) (β : B.Equivariance G.obj)
    (i : (derivedDirectImage f).obj F ≅ G) : Prop :=
  ∀ (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k),
    let H := J.group k
    let t := parameterInclusion H f
    let act := directImageComparison (h k hx hy) (a t) (a f) F
    let proj := directImageComparison (projectionSquare H f) (a t) (a f) F
    let γ : (boundedBelowInverseImage (A.action k hx).act).obj F ⟶
        (boundedBelowInverseImage (AnalyticAction.projection H X)).obj F :=
      ObjectProperty.homMk (α.datum k hx).iso.hom
    IsIso act ∧ IsIso proj ∧
      (derivedInverseImage (B.action k hy).act).map i.hom.hom ≫ (β.datum k hy).iso.hom ≫
        (derivedInverseImage (AnalyticAction.projection H Y)).map i.inv.hom ≫ proj.hom =
      act.hom ≫ ((derivedDirectImage t).map γ).hom

/-- Equivariant direct-image comparison in the form used for the terminal map of convolution. -/
def EquivariantDirectImageComparison {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (a : DerivedAdjunctions) (A : JetAction J X) (B : JetAction J Y)
    (f : X ⟶ Y) (h : JetMapsCommute A B f) (F : BoundedBelow X)
    (α : A.Equivariance F.obj) (G : BoundedBelow Y) (β : B.Equivariance G.obj) : Prop :=
  ∃ i : (derivedDirectImage f).obj F ≅ G, DirectImageIntertwines a A B h F α G β i

/-- For an equivariant homeomorphism, the adjoint mate of a pullback isomorphism
intertwines the ordinary derived direct images. When every target jet level is a source
jet level, any source equivariance transports to the target. -/
def EquivariantHomeomorphismDirectImage : Prop :=
  ∀ {J : JetSystem.{0}} {X Y : TopCat.{0}} (v : X ≅ Y)
    (a : DerivedAdjunctions) (A : JetAction J X) (B : JetAction J Y)
    (h : JetMapsCommute A B v.hom),
    (∀ (F : BoundedBelow X) (G : BoundedBelow Y) (α : A.Equivariance F.obj)
      (β : B.Equivariance G.obj) (c : (boundedBelowInverseImage v.hom).obj G ≅ F),
      PullbackIntertwines h α β c →
      ∃ i : (derivedDirectImage v.hom).obj F ≅ G,
        i.inv = (a v.hom).homEquiv G F c.hom ∧
          DirectImageIntertwines a A B h F α G β i) ∧
    (A.cutoff ≤ B.cutoff → ∀ (F : BoundedBelow X) (α : A.Equivariance F.obj),
      ∃ (G : BoundedBelow Y) (β : B.Equivariance G.obj),
        EquivariantDirectImageComparison a A B v.hom h F α G β)

end RepTheorySurvey.Geometric.EquivariantHomeomorphismDirectImageSpecs
