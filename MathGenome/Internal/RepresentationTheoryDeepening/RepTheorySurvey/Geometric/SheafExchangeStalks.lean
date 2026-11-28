import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafExchangeStalks
import Batteries.Tactic.OpenPrivate

open CategoryTheory

namespace RepTheorySurvey.Geometric.SheafExchangeStalks

open Analytic
open private stalkPushforward_naturality from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

private noncomputable abbrev pushforwardGerm {X Y : TopCat.{0}} (m : X ⟶ Y)
    (F : Sheaves X) (x : X) :
    (stalk (m x)).obj ((directImage m).obj F) ⟶ (stalk x).obj F :=
  TopCat.Presheaf.stalkPushforward Coeff.{0} m F.presheaf x

private theorem pushforwardGerm_natural {X Y : TopCat.{0}} (m : X ⟶ Y)
    {F G : Sheaves X} (v : F ⟶ G) (x : X) :
    (stalk (m x)).map ((directImage m).map v) ≫ pushforwardGerm m G x =
      pushforwardGerm m F x ≫ (stalk x).map v :=
  stalkPushforward_naturality m v.hom x

private theorem inverseImageStalkMap_natural {X Y : TopCat.{0}} (m : X ⟶ Y)
    {F G : Sheaves Y} (v : F ⟶ G) (x : X) :
    (stalk (m x)).map v ≫ inverseImageStalkMap m G x =
      inverseImageStalkMap m F x ≫ (stalk x).map ((inverseImage m).map v) := by
  let a := inverseDirectAdjunction m
  change (stalk (m x)).map v ≫ (stalk (m x)).map (a.unit.app G) ≫
      pushforwardGerm m ((inverseImage m).obj G) x =
    ((stalk (m x)).map (a.unit.app F) ≫ pushforwardGerm m ((inverseImage m).obj F) x) ≫
      (stalk x).map ((inverseImage m).map v)
  have naturality : v ≫ a.unit.app G =
      a.unit.app F ≫ (directImage m).map ((inverseImage m).map v) := a.unit.naturality v
  rw [← Functor.map_comp_assoc, naturality, Functor.map_comp, Category.assoc,
    pushforwardGerm_natural, Category.assoc]

private theorem inverseCounit_stalk {X Y : TopCat.{0}} (m : X ⟶ Y)
    (T : Sheaves X) {G : Sheaves Y} (h : (directImage m).obj T ⟶ G) (x : X)
    [IsIso ((inverseDirectAdjunction m).counit.app T)] :
    pushforwardGerm m T x ≫
        (stalk x).map (inv ((inverseDirectAdjunction m).counit.app T) ≫
          (inverseImage m).map h) ≫ (inverseImageStalkIso m G x).inv =
      (stalk (m x)).map h := by
  have counit := inducedCounit_stalk m T x
  change _ = pushforwardGerm m T x at counit
  apply (cancel_mono (inverseImageStalkIso m G x).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← counit, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id_assoc]
  exact (inverseImageStalkMap_natural m h x).symm

private theorem pushforwardGerm_congr {X Y : TopCat.{0}} {m n : X ⟶ Y} (p : m = n)
    (F : Sheaves X) (x : X) :
    (stalk (m x)).map ((eqToIso (congrArg directImage p)).hom.app F) ≫
        eqToHom (congrArg (fun y ↦ (stalk y).obj ((directImage n).obj F))
          (congrArg (fun k : X ⟶ Y ↦ k x) p)) ≫ pushforwardGerm n F x =
      pushforwardGerm m F x := by
  cases p
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Computing the stalk of the exchange via either path around the square gives the same map. -/
theorem exchangeStalkFormula : SheafExchangeStalksSpecs.ExchangeStalkFormula := by
  unfold SheafExchangeStalksSpecs.ExchangeStalkFormula
  intro X X' Y Y' f g s j square F F' α x T T' e h ε τ _ pointEq
  let H := (directImage s.hom).obj F
  have hε : IsIso ((inverseDirectAdjunction j.hom).counit.app T) :=
    inducedCounit_isIso (TopCat.homeoOfIso j).isInducing T
  have hcₛ : IsIso (pushforwardGerm s.hom F x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      Coeff.{0} (TopCat.homeoOfIso s).isInducing F.presheaf x
  let cₛInv : (stalk x).obj F ⟶ (stalk (s.hom x)).obj H := inv (pushforwardGerm s.hom F x)
  have hcⱼ : IsIso (pushforwardGerm j.hom T (f x)) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      Coeff.{0} (TopCat.homeoOfIso j).isInducing T.presheaf (f x)
  let castH := eqToHom
    (congrArg (fun y ↦ (stalk y).obj ((directImage g).obj H)) pointEq)
  let castT' := eqToHom (congrArg (fun y ↦ (stalk y).obj T') pointEq)
  -- Both composites of pushforward germs are the germ for the same map out of X.
  have commutes :
      (stalk (j.hom (f x))).map (e.hom.app F) ≫ castH ≫
          pushforwardGerm g H (s.hom x) ≫ pushforwardGerm s.hom F x =
        pushforwardGerm j.hom T (f x) ≫ pushforwardGerm f F x := by
    have composed := pushforwardGerm_congr square F x
    simp only [pushforwardGerm, TopCat.Presheaf.stalkPushforward.comp] at composed
    exact composed
  have sheetGerm :
      (stalk (j.hom (f x))).map (e.hom.app F) ≫ castH ≫ pushforwardGerm g H (s.hom x) =
        pushforwardGerm j.hom T (f x) ≫ pushforwardGerm f F x ≫ cₛInv := by
    have cancelSheet : pushforwardGerm s.hom F x ≫ cₛInv = 𝟙 ((stalk (s.hom x)).obj H) :=
      IsIso.hom_inv_id (pushforwardGerm s.hom F x)
    have postcomp := (reassoc_of% commutes) cₛInv
    rw [cancelSheet, Category.comp_id] at postcomp
    exact postcomp
  have adjointGerm :
      pushforwardGerm j.hom T (f x) ≫ (stalk (f x)).map τ ≫
          (inverseImageStalkIso j.hom T' (f x)).inv = (stalk (j.hom (f x))).map h :=
    inverseCounit_stalk j.hom T h (f x)
  change (stalk (f x)).map τ ≫ (inverseImageStalkIso j.hom T' (f x)).inv ≫
      castT' ≫ pushforwardGerm g F' (s.hom x) =
    pushforwardGerm f F x ≫ cₛInv ≫ (stalk (s.hom x)).map α
  apply (cancel_epi (pushforwardGerm j.hom T (f x))).mp
  simp only [reassoc_of% adjointGerm]
  change (stalk (j.hom (f x))).map (e.hom.app F ≫ (directImage g).map α) ≫
      castT' ≫ pushforwardGerm g F' (s.hom x) = _
  have transport :
      (stalk (j.hom (f x))).map ((directImage g).map α) ≫ castT' =
        castH ≫ (stalk (g (s.hom x))).map ((directImage g).map α) :=
    eqToHom_naturality (fun y : Y' ↦ (stalk y).map ((directImage g).map α)) pointEq
  rw [Functor.map_comp, Category.assoc, reassoc_of% transport, pushforwardGerm_natural]
  simp only [reassoc_of% sheetGerm]

end RepTheorySurvey.Geometric.SheafExchangeStalks
