import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Derived
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveInvariance
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedHomFromKProjective
import Mathlib.CategoryTheory.Yoneda
import Batteries.Tactic.OpenPrivate

open CategoryTheory

universe c d u v w

namespace DerivedFormalization.RightDGModule

/-- Localization preserves the maps out of a source whose Hom functor inverts
the chosen morphisms. Lift both Hom functors to a common universe of types. -/
private theorem localization_map_bijective_of_postcomp
    {C : Type u} {D : Type v} [Category.{c} C] [Category.{d} D]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
    (X Y : C)
    (hX : ∀ ⦃U V : C⦄ (s : U ⟶ V), W s →
      Function.Bijective (fun f : X ⟶ U => f ≫ s)) :
    Function.Bijective (fun f : X ⟶ Y => L.map f) := by
  let F := uliftCoyoneda.{d}.obj (Opposite.op X)
  let G := uliftCoyoneda.{c}.obj (Opposite.op (L.obj X))
  have hF : W.IsInvertedBy F := by
    intro U V s hs
    apply (CategoryTheory.isIso_iff_bijective (F.map s)).2
    exact Equiv.ulift.symm.bijective.comp ((hX s hs).comp Equiv.ulift.bijective)
  let H := Localization.lift F hF L
  let e : L ⋙ H ≅ F := Localization.fac F hF L
  let τ : F ⟶ L ⋙ G :=
    { app := fun U => ↾fun (f : ULift.{d} (X ⟶ U)) => ULift.up (L.map f.down)
      naturality := by
        intro U V s
        ext f
        exact congrArg ULift.up (L.map_comp f.down s) }
  let : Localization.Lifting L W (L ⋙ G) G := ⟨Iso.refl _⟩
  let β : H ⟶ G := Localization.liftNatTrans L W F (L ⋙ G) H G τ
  have β_app (U : C) (x : H.obj (L.obj U)) :
      β.app (L.obj U) x = ULift.up (L.map (e.hom.app U x).down) := by
    have h := Localization.liftNatTrans_app L W F (L ⋙ G) H G τ U
    change β.app (L.obj U) = e.hom.app U ≫ τ.app U ≫ 𝟙 _ at h
    rw [h, Category.comp_id]
    rfl
  let a : H.obj (L.obj X) := e.inv.app X (ULift.up (𝟙 X))
  have he : e.hom.app X a = ULift.up (𝟙 X) :=
    congrArg (fun f => f (ULift.up (𝟙 X))) (e.inv_hom_id_app X)
  have ha : β.app (L.obj X) a = ULift.up (𝟙 (L.obj X)) := by
    rw [β_app]
    rw [he]
    change ULift.up (L.map (𝟙 X)) = _
    rw [L.map_id]
  let recover (g : L.obj X ⟶ L.obj Y) : X ⟶ Y :=
    (e.hom.app Y (H.map g a)).down
  have hleft (f : X ⟶ Y) : recover (L.map f) = f := by
    have h := congrArg (fun m => m a) (e.hom.naturality f)
    change e.hom.app Y (H.map (L.map f) a) = F.map f (e.hom.app X a) at h
    rw [he] at h
    exact (congrArg ULift.down h).trans (Category.id_comp f)
  have hright (g : L.obj X ⟶ L.obj Y) : L.map (recover g) = g := by
    have h := congrArg (fun m => m a) (β.naturality g)
    change β.app (L.obj Y) (H.map g a) = G.map g (β.app (L.obj X) a) at h
    rw [β_app, ha] at h
    exact (congrArg ULift.down h).trans (Category.id_comp g)
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open Specs.DerivedFormalization.DG.Basic (h0Hom)
open private zeroCohomologyMap zeroCohomologyMap_bijective zeroCohomologyMap_homotopyClass
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveInvariance

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

/-- Quasi-isomorphisms induce bijections on homotopy classes out of a K-projective module. -/
theorem IsKProjective.postcomp_bijective (_h : HomotopyCategoryLaws A)
    {P : K A} (hP : IsKProjective (A := A) P) {M N : K A} (f : M ⟶ N) (hf : quasiIsomorphisms A f) :
    Function.Bijective (fun g : P ⟶ M => g ≫ f) := by
  obtain ⟨s, rfl, hs⟩ := hf
  have h := zeroCohomologyMap_bijective (homComplexMap P s)
    ((hP.homComplexMap_quasiIso s hs).quasiIsoAt 0)
  change @Function.Bijective (P ⟶ M) (P ⟶ N)
    (fun g => zeroCohomologyMap (homComplexMap P s) g) at h
  have he (g : P ⟶ M) :
      zeroCohomologyMap (homComplexMap P s) g = g ≫ homotopyClass s := by
    obtain ⟨t, rfl⟩ := homotopyClass_surjective g
    rw [zeroCohomologyMap_homotopyClass]
    exact (toHomotopyCategory A).map_comp t s
  simpa only [he] using h

/-- A morphism out of a K-projective module in the native localization is
represented by a unique degree-zero cohomology class. -/
theorem IsKProjective.Q_map_bijective
    (h : HomotopyCategoryLaws A) {P N : RightDGModule A} (hP : P.IsKProjective) :
    Function.Bijective (fun g : h0Hom (homComplex P N) => (Q A h).map g) :=
  localization_map_bijective_of_postcomp (quasiIsomorphisms A) (Q A h) P N
    (fun {_ _} f hf => hP.postcomp_bijective h f hf)

theorem Q_map_natural (h : HomotopyCategoryLaws A)
    {P N T : K A} (g : P ⟶ N) (f : N ⟶ T) :
    (Q A h).map (g ≫ f) = (Q A h).map g ≫ (Q A h).map f :=
  (Q A h).map_comp g f

/-- A given K-projective replacement identifies the native derived Hom
with degree-zero cohomology, naturally in the target. -/
theorem IsKProjective.replacement_comparison (h : HomotopyCategoryLaws A)
    {P M : RightDGModule A} (p : P ⟶ M) (hP : P.IsKProjective) (hp : IsQuasiIso p) :
    let q := Q A h
    let e := Localization.isoOfHom q (quasiIsomorphisms A) (homotopyClass p) ⟨p, rfl, hp⟩
    (∀ N : RightDGModule A,
      Function.Bijective (fun g : h0Hom (homComplex P N) => e.inv ≫ q.map g)) ∧
    (∀ {N T : K A} (g : @Quiver.Hom (K A) inferInstance P N) (f : N ⟶ T),
      e.inv ≫ q.map (g ≫ f) = (e.inv ≫ q.map g) ≫ q.map f) := by
  dsimp only
  constructor
  · intro N
    let e := Localization.isoOfHom (Q A h) (quasiIsomorphisms A) (homotopyClass p) ⟨p, rfl, hp⟩
    exact (e.homFromEquiv (Z := (Q A h).obj N)).bijective.comp (hP.Q_map_bijective h)
  · intro N T g f
    rw [Q_map_natural, Category.assoc]

end DerivedFormalization.RightDGModule
