import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjective

open CategoryTheory CochainComplex.HomComplex
open _root_.DerivedFormalization

universe u v w

namespace Specs.DerivedFormalization.DG.KProjectiveInvariance

open HomComplex (homComplex dgModuleCategory strictCycle gradedHom HomotopyEquation)
open KProjective (isKProjective)
open _root_.Specs.DerivedFormalization.DG.Module (acyclic quasiIsomorphism)

variable {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
variable {M N : RightDGModuleModel A}

/-- Postcomposition by a closed degree-zero map on the right-linear Hom complex. -/
@[reducible] def homComplexMap (P : RightDGModuleModel A) (f : M ⟶ N) :
    homComplex P M ⟶ homComplex P N where
  f r := ModuleCat.ofHom ((dgModuleCategory A).comp 0 r r (zero_add r) (strictCycle f).val)
  comm' r s _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    funext a
    change δ r s ((g.val a).comp (Cochain.ofHom (f.app a)) (add_zero r)) =
      (δ r s (g.val a)).comp (Cochain.ofHom (f.app a)) (add_zero s)
    exact δ_comp_ofHom (g.val a) (f.app a) s

set_option linter.checkUnivs false in
def HomComplexMapType :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (P : RightDGModuleModel A), (M ⟶ N) →
    (homComplex P M ⟶ homComplex P N)

/-- Hom out of a K-projective module takes objectwise quasi-isomorphisms to
quasi-isomorphisms of complexes of base-ring modules. -/
def HomComplexMapQuasiIso : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P M N : RightDGModuleModel A} (f : M ⟶ N),
    isKProjective P → quasiIsomorphism f → QuasiIso (homComplexMap P f)

/-- The identity of an acyclic K-projective module is null-homotopic by
a degree-minus-one right-linear family. -/
def ContractibleOfAcyclic : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {P : RightDGModuleModel A}, isKProjective P → acyclic P →
    ∃ h : gradedHom P P (-1), HomotopyEquation (𝟙 P) (0 : P ⟶ P) h

/-- A quasi-isomorphism between K-projectives has a strict map as a
two-sided inverse up to right-linear homotopy. -/
def HomotopyEquivalenceOfQuasiIso : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    {M N : RightDGModuleModel A} (f : M ⟶ N),
    isKProjective M → isKProjective N → quasiIsomorphism f →
    ∃ g : N ⟶ M, ∃ hM : gradedHom M M (-1), ∃ hN : gradedHom N N (-1),
      HomotopyEquation (f ≫ g) (𝟙 M) hM ∧ HomotopyEquation (g ≫ f) (𝟙 N) hN

end Specs.DerivedFormalization.DG.KProjectiveInvariance
