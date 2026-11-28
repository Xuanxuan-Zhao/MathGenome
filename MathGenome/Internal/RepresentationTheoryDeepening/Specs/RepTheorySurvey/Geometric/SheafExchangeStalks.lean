import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

noncomputable section

open CategoryTheory

namespace RepTheorySurvey.Geometric.SheafExchangeStalksSpecs

open Analytic

/-- The stalk formula for the adjoint of the direct-image map induced by the square. -/
def ExchangeStalkFormula : Prop :=
  ∀ {X X' Y Y' : TopCat.{0}} (f : X ⟶ Y) (g : X' ⟶ Y')
    (s : X ≅ X') (j : Y ≅ Y') (square : f ≫ j.hom = s.hom ≫ g)
    (F : Sheaves X) (F' : Sheaves X') (α : (directImage s.hom).obj F ⟶ F') (x : X),
    let T := (directImage f).obj F
    let T' := (directImage g).obj F'
    let e : directImage f ⋙ directImage j.hom ≅ directImage s.hom ⋙ directImage g :=
      eqToIso (congrArg directImage square)
    let h : (directImage j.hom).obj T ⟶ T' := e.hom.app F ≫ (directImage g).map α
    let ε := (inverseDirectAdjunction j.hom).counit.app T
    letI : IsIso ε := inducedCounit_isIso (TopCat.homeoOfIso j).isInducing T
    let τ : T ⟶ (inverseImage j.hom).obj T' := inv ε ≫ (inverseImage j.hom).map h
    let cₛ := TopCat.Presheaf.stalkPushforward Coeff.{0} s.hom F.presheaf x
    letI : IsIso cₛ := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      Coeff.{0} (TopCat.homeoOfIso s).isInducing F.presheaf x
    let pointEq : j.hom (f x) = g (s.hom x) := congrArg (fun k : X ⟶ Y' ↦ k x) square
    (stalk (f x)).map τ ≫ (inverseImageStalkIso j.hom T' (f x)).inv ≫
        eqToHom (congrArg (fun y ↦ (stalk y).obj T') pointEq) ≫
        TopCat.Presheaf.stalkPushforward Coeff.{0} g F'.presheaf (s.hom x) =
      TopCat.Presheaf.stalkPushforward Coeff.{0} f F.presheaf x ≫ inv cₛ ≫
        (stalk (s.hom x)).map α

end RepTheorySurvey.Geometric.SheafExchangeStalksSpecs
