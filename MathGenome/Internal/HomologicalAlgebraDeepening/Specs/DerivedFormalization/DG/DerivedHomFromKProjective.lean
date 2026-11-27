import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Derived
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjectiveInvariance

open CategoryTheory

universe u v w

namespace Specs.DerivedFormalization.DG.DerivedHomFromKProjective

open _root_.DerivedFormalization (DGCategoryModel RightDGModuleModel RightDGModuleHomModel)
open Derived (HomotopyCategoryLaws quasiIsomorphisms quotient)
open KProjective (isKProjective)
open HomComplex (homotopyClass homComplex homotopyCategory)
open Basic (h0Hom)

/-- Postcomposition in the homotopy category inverts quasi-isomorphisms on Hom out of
a K-projective module. The test for K-projectivity uses the same coefficient universe. -/
def PostcompBijective : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : HomotopyCategoryLaws A) {P : homotopyCategory A},
    isKProjective P →
    letI := Derived.homotopyCategory A h
    ∀ {M N : homotopyCategory A} (f : M ⟶ N), quasiIsomorphisms A f →
      Function.Bijective (fun g : P ⟶ M => g ≫ f)

/-- The canonical map from degree-zero cohomology of the right-linear Hom complex
to morphisms in the native localization is bijective for a K-projective source. -/
def QuotientMapBijective : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : HomotopyCategoryLaws A) {P N : RightDGModuleModel A},
    isKProjective P →
    letI := Derived.homotopyCategory A h
    Function.Bijective (fun g : h0Hom (homComplex P N) => (quotient A h).map g)

/-- The canonical bijections commute with postcomposition in the target. -/
def QuotientMapNatural : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : HomotopyCategoryLaws A),
    letI := Derived.homotopyCategory A h
    ∀ {P N T : homotopyCategory A} (g : P ⟶ N) (f : N ⟶ T),
      (quotient A h).map (g ≫ f) = (quotient A h).map g ≫ (quotient A h).map f

/-- A given strict quasi-isomorphism p : P ⟶ M from a K-projective module
computes derived Hom out of M via the map g ↦ (Q[p])⁻¹ ≫ Qg.
This map is bijective and natural in the target. -/
def ReplacementComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : HomotopyCategoryLaws A) {P M : RightDGModuleModel A}
    (p : RightDGModuleHomModel P M), isKProjective P → ∀ (hp : Module.quasiIsomorphism p),
    letI := Derived.homotopyCategory A h
    let q := quotient A h
    letI : q.IsLocalization (quasiIsomorphisms A) :=
      inferInstanceAs ((quasiIsomorphisms A).Q.IsLocalization (quasiIsomorphisms A))
    let e := Localization.isoOfHom q (quasiIsomorphisms A) (homotopyClass p)
      ⟨p, rfl, hp⟩
    (∀ N : RightDGModuleModel A,
      Function.Bijective (fun g : h0Hom (homComplex P N) => e.inv ≫ q.map g)) ∧
    (∀ {N T : homotopyCategory A} (g : @Quiver.Hom (homotopyCategory A) inferInstance P N) (f : N ⟶ T),
      e.inv ≫ q.map (g ≫ f) = (e.inv ≫ q.map g) ≫ q.map f)

end Specs.DerivedFormalization.DG.DerivedHomFromKProjective
