import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.JetEquivariantRestrictionSpecs

open Analytic
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open AnalyticAction (projection multiplyParameters)
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)

/-- Commutation of the two actions with the map of spaces. -/
def ActionSquare {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    (B : AnalyticAction H U) (A : AnalyticAction H X) (j : U ⟶ X) : Prop :=
  parameterInclusion H j ≫ A.act = B.act ≫ j

/-- An arrow on the coefficient objects respects equivariance via the two
canonical pullback squares. -/
def Commutes {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {j : U ⟶ X}
    (hj : ActionSquare B A j) {G : Derived U} {F : Derived X}
    (β : B.Equivariance G) (α : A.Equivariance F)
    (v : G ⟶ (derivedInverseImage j).obj F) : Prop :=
  (derivedInverseImage B.act).map v ≫ (squareValue hj).inv.app F ≫
    (derivedInverseImage (parameterInclusion H j)).map α.iso.hom ≫
    (squareValue (projectionSquare H j)).hom.app F =
  β.iso.hom ≫ (derivedInverseImage (projection H U)).map v

namespace Expected

/-- Full faithfulness on the indicated pullback objects lifts a given equivariance
and detects its identity, multiplication and transition equations. -/
def EquivarianceLifting : Prop :=
  ∀ {J : JetSystem.{0}} {U X : TopCat.{0}}
    {B : JetAction J U} {A : JetAction J X} (j : U ⟶ X) (hc : B.cutoff ≤ A.cutoff)
    (h : ∀ (k : ℕ) (hk : A.cutoff ≤ k),
      ActionSquare (B.action k (hc.trans hk)) (A.action k hk) j)
    {G : Derived U} {F : Derived X} (v : G ≅ (derivedInverseImage j).obj F)
    (β : B.Equivariance G),
    (let E := (derivedInverseImage (𝟙 X)).obj F
     Function.Injective ((derivedInverseImage j).map : (E ⟶ E) → _)) →
    (∀ (k : ℕ) (hk : A.cutoff ≤ k),
      let H := J.group k
      let Q := (derivedInverseImage (A.action k hk).act).obj F
      let P := (derivedInverseImage (projection H X)).obj F
      ∀ (S T : Derived (AnalyticAction.Parameters H X)),
        (S = Q ∨ S = P) → (T = Q ∨ T = P) →
          Function.Bijective
            ((derivedInverseImage (parameterInclusion H j)).map : (S ⟶ T) → _)) →
    (∀ (k : ℕ) (hk : A.cutoff ≤ k),
      let H := J.group k
      let m := multiplyParameters H X
      let Q := (derivedInverseImage (m ≫ (A.action k hk).act)).obj F
      let P := (derivedInverseImage (m ≫ projection H X)).obj F
      let i := parameterInclusion H (parameterInclusion H j)
      Function.Injective ((derivedInverseImage i).map : (Q ⟶ P) → _)) →
    ∃! α : A.Equivariance F,
      ∀ (k : ℕ) (hk : A.cutoff ≤ k),
        Commutes (h k hk) (β.datum k (hc.trans hk)) (α.datum k hk) v.hom

/-- Compatibility of coefficient arrows pastes through composition, and can
be checked after a preceding compatible isomorphism with faithful pullback. -/
def EquivariancePasting : Prop :=
  ∀ {H : AnalyticGroup.{0}} {U X Y : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {C : AnalyticAction H Y}
    {j : U ⟶ X} {k : X ⟶ Y} (hj : ActionSquare B A j) (hk : ActionSquare A C k)
    (hjk : ActionSquare B C (j ≫ k))
    {G : Derived U} {F : Derived X} {E : Derived Y}
    (β : B.Equivariance G) (α : A.Equivariance F) (γ : C.Equivariance E)
    (v : G ⟶ (derivedInverseImage j).obj F) (w : F ⟶ (derivedInverseImage k).obj E),
    let z := v ≫ (derivedInverseImage j).map w ≫
      (derivedInverseImageComposition j k).inv.app E
    Commutes hj β α v →
      (Commutes hk α γ w → Commutes hjk β γ z) ∧
        (IsIso v → (derivedInverseImage (parameterInclusion H j)).Faithful →
          Commutes hjk β γ z → Commutes hk α γ w)

end Expected
end RepTheorySurvey.Geometric.JetEquivariantRestrictionSpecs
