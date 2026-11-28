import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u

namespace RepTheorySurvey.Geometric.ClosedEquivarianceExtensionSpecs

open Analytic Analytic.IntersectionComplex LocalSheaf

/-- The map on parameters induced by a map of the spaces acted on. -/
def parameterInclusion (H : AnalyticGroup.{u}) {Y X : TopCat.{u}} (i : Y ⟶ X) :
    AnalyticAction.Parameters H Y ⟶ AnalyticAction.Parameters H X :=
  TopCat.ofHom ⟨fun p => (p.1, i p.2), continuous_fst.prodMk
    (i.hom.continuous.comp continuous_snd)⟩

theorem projectionSquare (H : AnalyticGroup.{u}) {Y X : TopCat.{u}} (i : Y ⟶ X) :
    parameterInclusion H i ≫ AnalyticAction.projection H X =
      AnalyticAction.projection H Y ≫ i :=
  TopCat.ext (fun _ => rfl)

/-- Use the same actions and transition maps at the levels above the common cutoff. -/
def above {J : JetSystem.{u}} {X : TopCat.{u}} (A : JetAction J X)
    (m : ℕ) : JetAction J X where
  cutoff := max A.cutoff m
  action k h := A.action k ((le_max_left _ _).trans h)
  factors hk h := A.factors ((le_max_left _ _).trans hk) h

abbrev DerivedAdjunctions :=
  ∀ {Y X : TopCat.{u}} (f : Y ⟶ X), boundedBelowInverseImage f ⊣ derivedDirectImage f

section

variable {J : JetSystem.{u}} {X : TopCat.{u}} {Z : Set X}
variable (A : JetAction J X) (B : JetAction J (TopCat.of Z))

/-- The closed inclusion intertwines the actions at each common jet level. -/
def ActionSquares : Prop :=
  ∀ (k : ℕ) (hx : A.cutoff ≤ k) (hz : B.cutoff ≤ k),
    parameterInclusion (J.group k) (closedInclusion Z) ≫ (A.action k hx).act =
      (B.action k hz).act ≫ closedInclusion Z

variable {A B}
variable (hZ : IsClosed Z) (h : ActionSquares A B)
variable (a : DerivedAdjunctions.{u})
variable (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
variable (F : BoundedBelow (TopCat.of Z))

/-- The actual adjunction mate for the action square. -/
def actionComparison (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k) :=
  adjointSquareMap
    (pullbackSquare (h k ((le_max_left _ _).trans hk) ((le_max_right _ _).trans hk)))
    (a (parameterInclusion (J.group k) (closedInclusion Z))) b F

/-- The actual adjunction mate for the projection square. -/
def projectionComparison (H : AnalyticGroup.{u}) :=
  adjointSquareMap (pullbackSquare (projectionSquare H (closedInclusion Z)))
    (a (parameterInclusion H (closedInclusion Z))) b F

def ComparisonsAreIso : Prop :=
  ∀ (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k),
    IsIso (actionComparison hZ h a b F k hk) ∧
      IsIso (projectionComparison hZ a b F (J.group k))

variable (β : B.Equivariance F.obj)

/-- The equivariance arrow agrees with the direct image of the given arrow via
the two specified comparison maps. -/
def MatchesComparisons
    (α : (above A B.cutoff).Equivariance ((closedExtensionPlus hZ).obj F).obj) : Prop :=
  ∀ (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k),
    let hz := (le_max_right A.cutoff B.cutoff).trans hk
    let H := J.group k
    let iH := parameterInclusion H (closedInclusion Z)
    let v : (boundedBelowInverseImage (B.action k hz).act).obj F ⟶
        (boundedBelowInverseImage (AnalyticAction.projection H (TopCat.of Z))).obj F :=
      ObjectProperty.homMk (β.datum k hz).iso.hom
    (α.datum k hk).iso.hom ≫ (projectionComparison hZ a b F H).hom =
      (actionComparison hZ h a b F k hk).hom ≫ ((derivedDirectImage iH).map v).hom

end

/-- Closed extension by zero carries equivariance with all three laws of the
shared finite-jet equivariance structure. -/
def ClosedEquivarianceExtension : Prop :=
  ∀ {J : JetSystem.{u}} {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (A : JetAction J X) (B : JetAction J (TopCat.of Z)) (h : ActionSquares A B)
    (a : DerivedAdjunctions.{u})
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) (β : B.Equivariance F.obj),
    ComparisonsAreIso hZ h a b F →
      ∃ α : (above A B.cutoff).Equivariance ((closedExtensionPlus hZ).obj F).obj,
        MatchesComparisons hZ h a b F β α

/-- Changing the adjunctions transports both mates by the right-adjoint
uniqueness isomorphisms. The isomorphism on the closed extension intertwines
the resulting equivariance data at every common level. -/
def ClosedEquivarianceAdjunctionChange : Prop :=
  ∀ {J : JetSystem.{u}} {X : TopCat.{u}} {Z : Set X} (hZ : IsClosed Z)
    (A : JetAction J X) (B : JetAction J (TopCat.of Z)) (h : ActionSquares A B)
    (a a' : DerivedAdjunctions.{u})
    (b b' : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)),
    let G := (closedExtensionPlus hZ).obj F
    let τ := (b.rightAdjointUniq b').app F
    (∀ (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k),
      let H := J.group k
      let e := (A.action k ((le_max_left _ _).trans hk)).act
      let v := (B.action k ((le_max_right _ _).trans hk)).act
      let iH := parameterInclusion H (closedInclusion Z)
      let σ := (a iH).rightAdjointUniq (a' iH)
      actionComparison hZ h a' b' F k hk =
        (boundedBelowInverseImage e).map τ.inv ≫ actionComparison hZ h a b F k hk ≫
          σ.hom.app ((boundedBelowInverseImage v).obj F) ∧
      projectionComparison hZ a' b' F H =
        (boundedBelowInverseImage (AnalyticAction.projection H X)).map τ.inv ≫
          projectionComparison hZ a b F H ≫
          σ.hom.app ((boundedBelowInverseImage (AnalyticAction.projection H (TopCat.of Z))).obj F)) ∧
    (ComparisonsAreIso hZ h a b F →
      ∀ (β : B.Equivariance F.obj) (α α' : (above A B.cutoff).Equivariance G.obj),
        MatchesComparisons hZ h a b F β α → MatchesComparisons hZ h a' b' F β α' →
        ∀ (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k),
          let H := J.group k
          let e := (A.action k ((le_max_left _ _).trans hk)).act
          (derivedInverseImage e).map τ.hom.hom ≫ (α'.datum k hk).iso.hom =
            (α.datum k hk).iso.hom ≫ (derivedInverseImage (AnalyticAction.projection H X)).map τ.hom.hom)

end RepTheorySurvey.Geometric.ClosedEquivarianceExtensionSpecs
