import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CellLift
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.HomCongr

open CategoryTheory
open CategoryTheory.Limits (IsZero)

universe u v w t s r v' v''

namespace DerivedFormalization.DG.DerivedCoefficientLift

open Specs.DerivedFormalization.DG.DerivedCoefficientLift
open Specs.DerivedFormalization.DG.CoefficientLiftComparison (restrictModule restrictMap)
open Specs.DerivedFormalization.DG.DerivedKProjective
  (derivedCategoryInstance homComparisonMap replacementIso)
open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)
open CategoryTheory.Functor (isoWhiskerLeft isoWhiskerRight)
open Specs.DerivedFormalization.DG.AmbientDerived (category strictInput)
open CoefficientLift
open RightDGModule (K D Q instCategoryK homComplex homotopyClass toHomotopyCategory
  homotopyClass_surjective IsKProjective IsQuasiIso)

set_option linter.style.haveILetI false

noncomputable section

variable {k : Type u} [CommRing k]

private abbrev flatten (A : DGCategory.{u,v,w} k) :=
  flattenCategory.{u,v,w,max w t,s} A

private abbrev restrictArrows (A : DGCategory.{u,v,w} k) :
    RightDGModule (liftCategory.{u,max v w t,w,s} (category.{u,v,w,t} A)) ⥤
      RightDGModule (category.{u,v,w,max t s} A) where
  obj M := restrictModule (unflatten.{u,v,w,t,s} A) M
  map f := restrictMap (unflatten.{u,v,w,t,s} A) f
  map_id _ := RightDGModuleModel.hom_ext fun _ => rfl
  map_comp _ _ := RightDGModuleModel.hom_ext fun _ => rfl

private abbrev doubleLift (A : DGCategory.{u,v,w} k) :=
  liftFunctor.{u,max v w t,w,s} (category.{u,v,w,t} A)

private def restrictArrowsEquivalence (A : DGCategory.{u,v,w} k) :
    RightDGModule (liftCategory.{u,max v w t,w,s} (category.{u,v,w,t} A)) ≌
      RightDGModule (category.{u,v,w,max t s} A) where
  functor := restrictArrows.{u,v,w,t,s} A
  inverse :=
    { obj := restrictModule (flatten.{u,v,w,t,s} A)
      map := restrictMap (flatten.{u,v,w,t,s} A)
      map_id := fun _ => RightDGModuleModel.hom_ext fun _ => rfl
      map_comp := fun _ _ => RightDGModuleModel.hom_ext fun _ => rfl }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp; rfl)

private theorem strict_hom_ext
    {A : DGCategory.{u,v,w} k} {M N : RightDGModule A} {f g : M ⟶ N}
    (h : ∀ a i, (f.app a).f i = (g.app a).f i) : f = g :=
  RightDGModuleModel.hom_ext fun a => HomologicalComplex.hom_ext _ _ (h a)

private def inputIso (A : DGCategory.{u,v,w} k) :
    strictInput.{u,v,w,t} A ⋙ strictTransition.{u,v,w,t,s} A ≅
      strictInput.{u,v,w,max t s} A :=
  NatIso.ofComponents (fun _ => isoOfComponents
    (fun _ _ => ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv.symm))
    (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl))
    (fun {_ _} _ => strict_hom_ext fun _ _ => rfl)

private def successiveIso (A : DGCategory.{u,v,w} k) :
    strictTransition.{u,v,w,t,s} A ⋙ strictTransition.{u,v,w,max t s,r} A ≅
      strictTransition.{u,v,w,t,max s r} A :=
  NatIso.ofComponents (fun _ => isoOfComponents
    (fun _ _ => ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv.symm))
    (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl))
    (fun {_ _} _ => strict_hom_ext fun _ _ => rfl)

private def nativeAmbientIso (A : DGCategory.{u,max v w,w} k) :
    Specs.DerivedFormalization.DG.AmbientDerived.transportToAmbient.{u,v,w,0} A ⋙
      strictTransition.{u,max v w,w,0,s} A ≅ liftFunctor.{u,max v w,w,max w s} A :=
  NatIso.ofComponents (fun _ => isoOfComponents
    (fun _ _ => ULift.moduleEquiv.trans ULift.moduleEquiv.symm)
    (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl))
    (fun {_ _} _ => strict_hom_ext fun _ _ => rfl)

section Projective

open RightDGModule (GradedHom strictCycle dgCategory homotopyCriterion)
open Specs.DerivedFormalization.DG.Basic (classOf boundariesZero)

open private acyclic_iff_boundaries restrict restrict_app restrict_d restrict_zero
  gradedHom_ext_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.KProjectiveClosure

private theorem kProjective_of_homotopyRetract {A : DGCategory.{u,v,w} k}
    {P M : RightDGModule A} (p : P ⟶ M) (g : M ⟶ P) (hP : IsKProjective P)
    (h : homotopyClass (g ≫ p) = homotopyClass (𝟙 M)) : IsKProjective M := by
  change classOf (strictCycle (g ≫ p)) = classOf (strictCycle (𝟙 M)) at h
  rw [Submodule.Quotient.eq] at h
  change _ ∈ boundariesZero (homComplex M M) at h
  obtain ⟨b, hb⟩ := h
  have hb' : (homComplex M M).d (-1) 0 b =
      (strictCycle (g ≫ p)).val - (strictCycle (𝟙 M)).val :=
    congrArg Subtype.val hb
  intro N hN
  apply (acyclic_iff_boundaries _).2
  intro r z hz
  obtain ⟨y, hy⟩ := (acyclic_iff_boundaries _).1 (hP N hN) r (restrict p z) (by
    rw [← restrict_d, hz, restrict_zero])
  -- The graded Leibniz rule makes this the correction for the source homotopy.
  let c : GradedHom M N r := (dgCategory A).comp (r+1) (-1) r (by omega) z b
  have hc : (homComplex M N).d r (r+1) c =
      (r+1).negOnePow • (restrict g (restrict p z) - z) := by
    have e := (dgCategory A).toData.leibniz (r+1) (-1) r (by omega) z b
    change (homComplex M N).d r (r+1) c =
      (dgCategory A).comp (r+1+1) (-1) (r+1) (by omega)
        ((homComplex M N).d (r+1) (r+1+1) z) b +
      (r+1).negOnePow • (dgCategory A).comp (r+1) 0 (r+1) (add_zero _) z
        ((homComplex M M).d (-1) 0 b) at e
    rw [hz, map_zero, LinearMap.zero_apply, zero_add, hb', map_sub] at e
    rw [e]
    congr 1
    apply gradedHom_ext_apply
    intro a i j hij x
    change
      ((restrict (g ≫ p) z - restrict (𝟙 M) z).val a).v i j hij x =
      ((restrict g (restrict p z) - z).val a).v i j hij x
    simp only [Submodule.coe_sub, Pi.sub_apply, CochainComplex.HomComplex.Cochain.sub_v,
      ModuleCat.hom_sub, LinearMap.sub_apply]
    change (restrict (g ≫ p) z).app a i j hij x - (restrict (𝟙 M) z).app a i j hij x =
      (restrict g (restrict p z)).app a i j hij x - GradedHom.app z a i j hij x
    rw [restrict_app, restrict_app, restrict_app, restrict_app]
    rfl
  refine ⟨restrict g y - (r+1).negOnePow • c, ?_⟩
  change (homComplex M N).d r (r+1) (restrict g y - (r+1).negOnePow • c) = z
  rw [map_sub, ← restrict_d, hy]
  have hs : (homComplex M N).d r (r+1) ((r+1).negOnePow • c) =
      (r+1).negOnePow • (homComplex M N).d r (r+1) c := by
    simp only [Units.smul_def, map_zsmul]
  rw [hs, hc, smul_smul, Int.units_mul_self, one_smul, sub_sub_cancel]

private theorem nativeKProjectiveLift {A : DGCategory.{u,max v w,w} k}
    {M : RightDGModule A} (hM : IsKProjective M) : IsKProjective (liftModule.{u,max v w,w,s} M) := by
  obtain ⟨P, p, hP, _, hp⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,w} k A M
  have hPK := RightDGModule.IsSemiFree.isKProjective hP
  have hPl := RightDGModule.IsSemiFree.isKProjective (CellLift.semiFreeTransport.{u,max v w,w,s} P hP)
  obtain ⟨g, _, h, _, hh⟩ := hPK.homotopyEquivalence_of_quasiIso p hM hp
  have e := (homotopyCriterion _ _).2 ⟨h, hh⟩
  let F := liftFunctor.{u,max v w,w,s} A
  refine kProjective_of_homotopyRetract (F.map p) (F.map g) hPl ?_
  rw [← F.map_comp, ← F.map_id]
  exact (homotopyClass_lift_iff _ _).2 e

end Projective

section ArrowTransport

open RightDGModule (GradedHom dgCategory homotopyCriterion)
open Specs.DerivedFormalization.DG.Basic (h0Hom h0Map classOf)

variable {A : DGCategory.{u,v,w} k}

set_option linter.checkUnivs false in
private abbrev doubleLiftCategory (A : DGCategory.{u,v,w} k) :=
  liftCategory.{u,max v w t,w,s} (category.{u,v,w,t} A)

private def arrowGradedEquiv (M N : RightDGModule (doubleLiftCategory.{u,v,w,t,s} A)) (r : ℤ) :
    GradedHom M N r ≃ₗ[k]
      GradedHom ((restrictArrows.{u,v,w,t,s} A).obj M)
        ((restrictArrows.{u,v,w,t,s} A).obj N) r where
  toFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    exact GradedHom.comm_act f i j n ir nr h hi hn x (ULift.up (ULift.up z.down))⟩
  invFun f := ⟨f.val, by
    intro a b i j n ir nr h hi hn x z
    exact GradedHom.comm_act f i j n ir nr h hi hn x (ULift.up z.down.down)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private def arrowHomComplexIso (M N : RightDGModule (doubleLiftCategory.{u,v,w,t,s} A)) :
    homComplex M N ≅
      homComplex ((restrictArrows.{u,v,w,t,s} A).obj M)
        ((restrictArrows.{u,v,w,t,s} A).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (arrowGradedEquiv.{u,v,w,t,s} M N i).toModuleIso)
    (fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext rfl))

private theorem restrictArrows_kProjective
    (M : RightDGModule (doubleLiftCategory.{u,v,w,t,s} A)) (hM : IsKProjective M) :
    IsKProjective ((restrictArrows.{u,v,w,t,s} A).obj M) := by
  intro N hN i
  let N₀ := (restrictArrowsEquivalence.{u,v,w,t,s} A).inverse.obj N
  exact (hM N₀ hN i).of_iso (arrowHomComplexIso.{u,v,w,t,s} M N₀)

private def arrowDGFunctor (A : DGCategory.{u,v,w} k) :
    DGFunctor (dgCategory (doubleLiftCategory.{u,v,w,t,s} A))
      (dgCategory (category.{u,v,w,max t s} A)) where
  obj M := (restrictArrows.{u,v,w,t,s} A).obj M
  map M N := (arrowHomComplexIso.{u,v,w,t,s} M N).hom
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ _ _ _ := Subtype.ext rfl

private abbrev arrowHomotopy (A : DGCategory.{u,v,w} k) :
    K (doubleLiftCategory.{u,v,w,t,s} A) ⥤ K (category.{u,v,w,max t s} A) :=
  (arrowDGFunctor.{u,v,w,t,s} A).H0

private theorem arrowHomotopy_map_class
    {M N : RightDGModule (doubleLiftCategory.{u,v,w,t,s} A)} (f : M ⟶ N) :
    (arrowHomotopy.{u,v,w,t,s} A).map (homotopyClass f) =
      homotopyClass ((restrictArrows.{u,v,w,t,s} A).map f) := by
  change h0Map (arrowDGFunctor.{u,v,w,t,s} A) (classOf (RightDGModule.strictCycle f)) = _
  rw [DGFunctor.h0Map_mk]
  exact congrArg classOf (Subtype.ext (Subtype.ext rfl))

private theorem restrictArrows_homotopy_iff
    {M N : RightDGModule (doubleLiftCategory.{u,v,w,t,s} A)} (f g : M ⟶ N) :
    homotopyClass ((restrictArrows.{u,v,w,t,s} A).map f) =
      homotopyClass ((restrictArrows.{u,v,w,t,s} A).map g) ↔
        homotopyClass f = homotopyClass g := by
  rw [homotopyCriterion, homotopyCriterion]
  constructor
  · rintro ⟨h, eqn⟩
    exact ⟨(arrowGradedEquiv.{u,v,w,t,s} M N (-1)).symm h, eqn⟩
  · rintro ⟨h, eqn⟩
    exact ⟨arrowGradedEquiv.{u,v,w,t,s} M N (-1) h, eqn⟩

set_option maxHeartbeats 500000 in
private def arrowH0Equiv (M N : RightDGModule (doubleLiftCategory.{u,v,w,t,s} A)) :
    h0Hom (homComplex M N) ≃ₗ[k]
      h0Hom (homComplex ((restrictArrows.{u,v,w,t,s} A).obj M)
        ((restrictArrows.{u,v,w,t,s} A).obj N)) := by
  let H := (arrowDGFunctor.{u,v,w,t,s} A).H0
  let l : h0Hom (homComplex M N) →ₗ[k]
      h0Hom (homComplex ((restrictArrows.{u,v,w,t,s} A).obj M)
        ((restrictArrows.{u,v,w,t,s} A).obj N)) :=
    { toFun := H.map (X := M) (Y := N)
      map_add' := by
        intro f g
        exact H.map_add
      map_smul' := fun a f => H.map_smul a f }
  refine LinearEquiv.ofBijective l ⟨?_, ?_⟩
  · intro x y h
    obtain ⟨f, rfl⟩ := homotopyClass_surjective (M := M) (N := N) x
    obtain ⟨g, rfl⟩ := homotopyClass_surjective (M := M) (N := N) y
    apply (restrictArrows_homotopy_iff.{u,v,w,t,s} f g).mp
    change (arrowHomotopy.{u,v,w,t,s} A).map (homotopyClass f) =
      (arrowHomotopy.{u,v,w,t,s} A).map (homotopyClass g) at h
    rw [arrowHomotopy_map_class, arrowHomotopy_map_class] at h
    exact h
  · intro y
    obtain ⟨g, rfl⟩ := homotopyClass_surjective
      (M := (restrictArrows.{u,v,w,t,s} A).obj M)
      (N := (restrictArrows.{u,v,w,t,s} A).obj N) y
    obtain ⟨f, hf⟩ := (restrictArrowsEquivalence.{u,v,w,t,s} A).fullyFaithfulFunctor.map_surjective g
    exact ⟨homotopyClass f, (arrowHomotopy_map_class.{u,v,w,t,s} f).trans (congrArg homotopyClass hf)⟩

end ArrowTransport

theorem kProjectiveCoefficientTransition : KProjectiveTransition.{u,v,w,t,s} := by
  intro k _ A M hM
  exact restrictArrows_kProjective.{u,v,w,t,s} _ (nativeKProjectiveLift.{u,max v t,w,s} hM)

section Composition

variable {A : DGCategory.{u,v,w} k} {B : DGCategory.{u,v',w} k}
  {C : DGCategory.{u,v'',w} k}

private theorem hom_eq_of_heq {X : Type*} [Category X] {a b a' b' : X}
    (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) :
    f ≫ eqToHom hb = eqToHom ha ≫ g := by
  subst a'
  subst b'
  simpa using eq_of_heq h

private theorem heq_of_hom_eq {X : Type*} [Category X] {a b a' b' : X}
    (ha : a = a') (hb : b = b') {f : a ⟶ b} {g : a' ⟶ b'}
    (h : f ≫ eqToHom hb = eqToHom ha ≫ g) : HEq f g := by
  subst a'
  subst b'
  exact heq_of_eq (by simpa using h)

private def strictSquare {h : HomotopyCategoryLaws A}
    {h' : HomotopyCategoryLaws B} {T : RightDGModule A ⥤ RightDGModule B}
    (d : Descent h h' T) :
    letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory A h
    letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory B h'
    toHomotopyCategory A ⋙ d.H ≅ T ⋙ toHomotopyCategory B := by
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory A h
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory B h'
  exact NatIso.ofComponents (fun M => eqToIso (d.obj M)) (by
    intro M N f
    exact hom_eq_of_heq (d.obj M) (d.obj N) (d.map f))

private theorem descend_iso {X Y Z : Type*} [Category X] [Category Y] [Category Z]
    (L : X ⥤ Y) (W : MorphismProperty X) [L.IsLocalization W]
    {U V : X ⥤ Z} {F G : Y ⥤ Z}
    (sigma : L ⋙ F ≅ U) (tau : L ⋙ G ≅ V) (eta : U ≅ V) :
    ∃ theta : F ≅ G, ∀ x : X,
      theta.hom.app (L.obj x) ≫ tau.hom.app x = sigma.hom.app x ≫ eta.hom.app x := by
  let P := (Functor.whiskeringLeft X Y Z).obj L
  let full : P.FullyFaithful := Localization.fullyFaithfulWhiskeringLeft L W Z
  let beta := sigma ≪≫ eta ≪≫ tau.symm
  let theta := full.preimageIso beta
  have h : P.map theta.hom = beta.hom := full.map_preimage _
  refine ⟨theta, fun x => ?_⟩
  change (P.map theta.hom).app x ≫ tau.hom.app x = _
  rw [h]
  change (sigma.hom.app x ≫ eta.hom.app x ≫ tau.inv.app x) ≫ tau.hom.app x = _
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem compositionComparison
    {hA : HomotopyCategoryLaws A} {hB : HomotopyCategoryLaws B}
    {hC : HomotopyCategoryLaws C}
    {F : RightDGModule A ⥤ RightDGModule B} {G : RightDGModule B ⥤ RightDGModule C}
    {J : RightDGModule A ⥤ RightDGModule C}
    (dF : Descent hA hB F) (dG : Descent hB hC G) (dJ : Descent hA hC J)
    (alpha : F ⋙ G ≅ J) : CompositionComparison dF dG dJ alpha := by
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory A hA
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory B hB
  letI := Specs.DerivedFormalization.DG.Derived.homotopyCategory C hC
  letI := derivedCategoryInstance A hA
  letI := derivedCategoryInstance B hB
  letI := derivedCategoryInstance C hC
  let U := toHomotopyCategory A
  let V := toHomotopyCategory C
  let eta₀ : U ⋙ (dF.H ⋙ dG.H) ≅ U ⋙ dJ.H :=
    isoWhiskerRight (strictSquare dF) dG.H ≪≫
      isoWhiskerLeft F (strictSquare dG) ≪≫
      isoWhiskerRight alpha V ≪≫ (strictSquare dJ).symm
  let eta : dF.H ⋙ dG.H ≅ dJ.H :=
    NatIso.ofComponents (fun M => eta₀.app M) (by
      intro M N f
      obtain ⟨g, rfl⟩ := homotopyClass_surjective f
      exact eta₀.hom.naturality g)
  refine ⟨eta, ?_, ?_⟩
  · intro M
    apply heq_of_hom_eq
      ((congrArg dG.H.obj (dF.obj M)).trans (dG.obj (F.obj M))) (dJ.obj M)
    change (dG.H.map (eqToHom (dF.obj M)) ≫ eqToHom (dG.obj (F.obj M)) ≫
      homotopyClass (alpha.hom.app M) ≫ eqToHom (dJ.obj M).symm) ≫ eqToHom (dJ.obj M) = _
    simp only [eqToHom_map, Category.assoc, eqToHom_trans_assoc]
    erw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · let QA := Q A hA
    let QC := Q C hC
    letI : QA.IsLocalization (RightDGModule.quasiIsomorphisms A) :=
      RightDGModule.Q_isLocalization A hA
    let sigma : QA ⋙ (dF.D ⋙ dG.D) ≅ (dF.H ⋙ dG.H) ⋙ QC :=
      isoWhiskerRight dF.square dG.D ≪≫ isoWhiskerLeft dF.H dG.square
    obtain ⟨theta, ht⟩ := descend_iso QA (RightDGModule.quasiIsomorphisms A)
      sigma dJ.square (isoWhiskerRight eta QC)
    refine ⟨theta, fun M => ?_⟩
    erw [← Category.assoc]
    exact ht M

theorem derivedCoefficientTransitionOnInputs : OriginalInputCompatibility.{u,v,w,t,s} := by
  intro k _ A h h' h''
  exact ⟨inputIso.{u,v,w,t,s} A, fun _ _ _ _ => rfl, fun dI dT dJ =>
    compositionComparison dI dT dJ (inputIso.{u,v,w,t,s} A)⟩

theorem derivedCoefficientTransitionSuccessive : SuccessiveCompatibility.{u,v,w,t,s,r} := by
  intro k _ A h h' h''
  exact ⟨successiveIso.{u,v,w,t,s,r} A, fun _ _ _ _ => rfl, fun dF dG dJ =>
    compositionComparison dF dG dJ (successiveIso.{u,v,w,t,s,r} A)⟩

theorem derivedCoefficientTransitionNativeCompatibility : NativeAmbientCompatibility.{u,v,w,s} := by
  intro k _ A h h' h''
  exact ⟨nativeAmbientIso.{u,v,w,s} A, fun _ _ _ _ => rfl, fun dI dT dJ =>
    compositionComparison dI dT dJ (nativeAmbientIso.{u,v,w,s} A)⟩

end Composition

section LocalizationComparison

open Specs.DerivedFormalization.DG.Derived (homotopyCategory)
open Specs.DerivedFormalization.DG.Basic (h0Hom)
open RightDGModule (derivedHomComparison_bijective)

variable {A : DGCategory.{u,v,w} k} {B : DGCategory.{u,v',w} k}
  {h : HomotopyCategoryLaws A} {h' : HomotopyCategoryLaws B}
  {T : RightDGModule A ⥤ RightDGModule B}

private theorem classMap_strict (d : Descent h h' T)
    {P N : RightDGModule A} (f : P ⟶ N) :
    d.classMap (homotopyClass f) = homotopyClass (T.map f) := by
  letI := homotopyCategory A h
  letI := homotopyCategory B h'
  have e := hom_eq_of_heq (d.obj P) (d.obj N) (d.map f)
  change eqToHom (d.obj P).symm ≫
    d.H.map (homotopyClass f) ≫ eqToHom (d.obj N) = _
  rw [e]
  erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

private theorem represented_naturality (d : Descent h h' T)
    {P N : RightDGModule A} (g : h0Hom (homComplex P N)) :
    letI := homotopyCategory A h
    letI := homotopyCategory B h'
    letI := derivedCategoryInstance A h
    letI := derivedCategoryInstance B h'
    d.D.map ((Q A h).map g) ≫ (d.representedIso N).hom =
      (d.representedIso P).hom ≫ (Q B h').map (d.classMap g) := by
  letI := homotopyCategory A h
  letI := homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  let Q' := Q B h'
  change d.D.map ((Q A h).map g) ≫ d.square.hom.app N ≫
      eqToHom (congrArg Q'.obj (d.obj N)) =
    (d.square.hom.app P ≫ eqToHom (congrArg Q'.obj (d.obj P))) ≫ Q'.map
      (eqToHom (d.obj P).symm ≫ d.H.map g ≫ eqToHom (d.obj N))
  have hs := d.square.hom.naturality g
  change d.D.map ((Q A h).map g) ≫ d.square.hom.app N =
    d.square.hom.app P ≫ Q'.map (d.H.map g) at hs
  erw [← eqToHom_map Q' (d.obj N), ← eqToHom_map Q' (d.obj P), ← Category.assoc, hs]
  erw [Category.assoc, Category.assoc, ← Q'.map_comp, ← Q'.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

private theorem replacement_compatible (d : Descent h h' T)
    (hq : ∀ {P M : RightDGModule A} (p : P ⟶ M), IsQuasiIso p → IsQuasiIso (T.map p)) :
    d.ReplacementCompatible := by
  letI := homotopyCategory A h
  letI := homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  intro P M p hp
  refine ⟨hq p hp, ?_⟩
  intro N g
  let e := replacementIso h p hp
  let e' := replacementIso h' (T.map p) (hq p hp)
  let L := Q A h
  let L' := Q B h'
  have hn := represented_naturality d g
  have hm := represented_naturality d (homotopyClass p)
  rw [classMap_strict] at hm
  change d.D.map e.hom ≫ (d.representedIso M).hom = (d.representedIso P).hom ≫ e'.hom at hm
  change d.D.map (e.inv ≫ L.map g) ≫ (d.representedIso N).hom =
    (d.representedIso M).hom ≫ e'.inv ≫ L'.map (d.classMap g)
  haveI : Epi (d.D.map e.hom) := inferInstanceAs (Epi (d.D.mapIso e).hom)
  apply (cancel_epi (d.D.map e.hom)).mp
  have hleft : d.D.map e.hom ≫
      (d.D.map (e.inv ≫ L.map g) ≫ (d.representedIso N).hom) =
      d.D.map (L.map g) ≫ (d.representedIso N).hom := by
    erw [← Category.assoc, ← d.D.map_comp, e.hom_inv_id_assoc]
    rfl
  have hright : d.D.map e.hom ≫
      ((d.representedIso M).hom ≫ e'.inv ≫ L'.map (d.classMap g)) =
      (d.representedIso P).hom ≫ L'.map (d.classMap g) := by
    erw [← Category.assoc, hm, Category.assoc, e'.hom_inv_id_assoc]
  exact hleft.trans (hn.trans hright.symm)

/-- Comparison on resolutions gives full faithfulness on the entire localization. -/
private theorem fullyFaithful_of_resolutions (d : Descent h h' T)
    (hlinear : d.LinearOnClasses) (hcompat : d.ReplacementCompatible)
    (hres : ∀ M : RightDGModule A, ∃ (P : RightDGModule A) (p : P ⟶ M),
      IsQuasiIso p ∧ IsKProjective P ∧ IsKProjective (T.obj P)) :
    d.FullyFaithful := by
  letI := homotopyCategory A h
  letI := homotopyCategory B h'
  letI := derivedCategoryInstance A h
  letI := derivedCategoryInstance B h'
  have hclass (M N : RightDGModule A) : Function.Bijective (d.classMap (P := M) (N := N)) := by
    obtain ⟨e, he⟩ := hlinear M N
    exact (funext he : (e : _ → _) = d.classMap).symm ▸ e.bijective
  have hhom (M N : K A) : Function.Bijective (d.H.map (X := M) (Y := N)) := by
    let e := (eqToIso (d.obj M)).homCongr (eqToIso (d.obj N))
    exact (e.bijective.of_comp_iff' _).1 (hclass M N)
  have hder (X Y : D A h) : Function.Bijective (d.D.map (X := X) (Y := Y)) := by
    let L := Q A h
    obtain ⟨M, rfl⟩ := (Localization.Construction.objEquiv
      (RightDGModule.quasiIsomorphisms A)).surjective X
    obtain ⟨N, rfl⟩ := (Localization.Construction.objEquiv
      (RightDGModule.quasiIsomorphisms A)).surjective Y
    obtain ⟨P, p, hp, hP, hTP⟩ := hres M
    obtain ⟨hp', hn⟩ := hcompat p hp
    let l := homComparisonMap (N := N) h p hp
    let l' := homComparisonMap (N := T.obj N) h' (T.map p) hp'
    let e := (d.representedIso M).homCongr (d.representedIso N)
    have hl : Function.Bijective l := derivedHomComparison_bijective h p hp hP
    have hl' : Function.Bijective l' := derivedHomComparison_bijective h' (T.map p) hp' hTP
    have he : e ∘ d.D.map ∘ l = l' ∘ d.classMap := by
      funext g
      change (d.representedIso M).inv ≫ d.D.map (l g) ≫ (d.representedIso N).hom =
        l' (d.classMap g)
      rw [hn]
      exact Iso.inv_hom_id_assoc _ _
    exact (e.bijective.of_comp_iff' _).1
      ((hl.of_comp_iff _).1 (he.symm ▸ hl'.comp (hclass P N)))
  letI : d.H.Full := ⟨fun {M N} => (hhom M N).surjective⟩
  letI : d.H.Faithful := ⟨fun {M N} => (hhom M N).injective⟩
  letI : d.D.Full := ⟨fun {X Y} => (hder X Y).surjective⟩
  letI : d.D.Faithful := ⟨fun {X Y} => (hder X Y).injective⟩
  exact ⟨⟨Functor.FullyFaithful.ofFullyFaithful d.H⟩, ⟨Functor.FullyFaithful.ofFullyFaithful d.D⟩⟩

end LocalizationComparison

theorem nativeDerivedCoefficientTransition : NativeTransition.{u,v,w,s} := by
  intro k _ A h h'
  let T := liftFunctor.{u,max v w,w,s} A
  let d : Descent h h' T :=
    ⟨homotopyLift.{u,max v w,w,s} A, derivedLift.{u,max v w,w,s} A,
      fun _ => rfl, fun f => heq_of_eq (homotopyLift_map_class f), derivedLiftComparison A⟩
  have hlin : d.LinearOnClasses := by
    intro P N
    obtain ⟨e, he⟩ := h0LinearComparison.{u,max v w,w,s} P N
    refine ⟨e, fun g => ?_⟩
    obtain ⟨f, rfl⟩ := homotopyClass_surjective (M := P) (N := N) g
    rw [he, classMap_strict]
  have hrep : d.ReplacementCompatible := replacement_compatible d (fun p => (lift_quasiIso_iff p).2)
  refine ⟨⟨d, fullyFaithful_of_resolutions d hlin hrep ?_, hlin, hrep⟩,
    fun _ => nativeKProjectiveLift.{u,v,w,s}⟩
  intro M
  obtain ⟨P, p, hP, _, hp⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,v,w} k A M
  exact ⟨P, p, hp, RightDGModule.IsSemiFree.isKProjective hP,
    RightDGModule.IsSemiFree.isKProjective (CellLift.semiFreeTransport.{u,max v w,w,s} P hP)⟩

set_option maxHeartbeats 750000 in
theorem derivedCoefficientTransition : AmbientTransition.{u,v,w,t,s} := by
  intro k _ A h h'
  let B := category.{u,v,w,t} A
  let C := category.{u,v,w,max t s} A
  let T := strictTransition.{u,v,w,t,s} A
  letI := derivedCategoryInstance B h
  letI := derivedCategoryInstance C h'
  letI : (Q B h).IsLocalization (RightDGModule.quasiIsomorphisms B) :=
    RightDGModule.Q_isLocalization B h
  letI : (Q C h').IsLocalization (RightDGModule.quasiIsomorphisms C) :=
    RightDGModule.Q_isLocalization C h'
  let H := homotopyLift.{u,max v w t,w,s} B ⋙ arrowHomotopy.{u,v,w,t,s} A
  have hmap {M N : RightDGModule B} (f : M ⟶ N) :
      H.map (homotopyClass f) = homotopyClass (T.map f) := by
    change (arrowHomotopy.{u,v,w,t,s} A).map
      ((homotopyLift.{u,max v w t,w,s} B).map (homotopyClass f)) = _
    exact (congrArg (arrowHomotopy.{u,v,w,t,s} A).map
      (homotopyLift_map_class.{u,max v w t,w,s} f)).trans (arrowHomotopy_map_class.{u,v,w,t,s} _)
  have hq {M N : RightDGModule B} (f : M ⟶ N) : IsQuasiIso f → IsQuasiIso (T.map f) :=
    (lift_quasiIso_iff f).2
  have hi : (RightDGModule.quasiIsomorphisms B).IsInvertedBy (H ⋙ Q C h') := by
    intro M N g hg
    obtain ⟨f, rfl, hf⟩ := hg
    change IsIso ((Q C h').map (H.map (homotopyClass f)))
    rw [hmap]
    exact Localization.inverts (Q C h') (RightDGModule.quasiIsomorphisms C) _ ⟨T.map f, rfl, hq f hf⟩
  let D₀ := Localization.lift (H ⋙ Q C h') hi (Q B h)
  let d : Descent h h' T :=
    ⟨H, D₀, fun _ => rfl, fun f => heq_of_eq (hmap f),
      Localization.fac (H ⋙ Q C h') hi (Q B h)⟩
  have hlin : d.LinearOnClasses := by
    intro P N
    obtain ⟨E, hE⟩ := h0LinearComparison.{u,max v w t,w,s} P N
    let E' := arrowH0Equiv.{u,v,w,t,s} ((doubleLift.{u,v,w,t,s} A).obj P)
      ((doubleLift.{u,v,w,t,s} A).obj N)
    refine ⟨E.trans E', fun g => ?_⟩
    obtain ⟨f, rfl⟩ := homotopyClass_surjective (M := P) (N := N) g
    change (arrowHomotopy.{u,v,w,t,s} A).map (E (homotopyClass f)) = _
    rw [hE, arrowHomotopy_map_class, classMap_strict]
  have hrep : d.ReplacementCompatible := replacement_compatible d hq
  refine ⟨d, fullyFaithful_of_resolutions d hlin hrep ?_, hlin, hrep⟩
  intro M
  obtain ⟨P, p, hP, _, hp⟩ := RightDGModule.unboundedSemiFreeResolutionInUniverse.{u,max v t,w} k B M
  exact ⟨P, p, hp, RightDGModule.IsSemiFree.isKProjective hP,
    restrictArrows_kProjective.{u,v,w,t,s} _
      (RightDGModule.IsSemiFree.isKProjective (CellLift.semiFreeTransport.{u,max v w t,w,s} P hP))⟩

open Specs.DerivedFormalization.DG.IndexedSemiFree (StrictSum)

private def transitionSum {A : DGCategory.{u,v,w} k} {I : Type v'}
    {F : I → RightDGModule (category.{u,v,w,t} A)} {S : RightDGModule (category.{u,v,w,t} A)}
    (b : StrictSum F S) :
    StrictSum (fun i => (strictTransition.{u,v,w,t,s} A).obj (F i))
      ((strictTransition.{u,v,w,t,s} A).obj S) := by
  let c := IndexedSums.liftStrictSum.{u,max v w t,w,v',s} b
  exact
    { inclusion := fun i => (strictTransition.{u,v,w,t,s} A).map (b.inclusion i)
      coordinates := c.coordinates
      coordinate_inclusion := c.coordinate_inclusion
      coordinate_d := c.coordinate_d
      coordinate_act := fun _ _ _ _ _ z _ => c.coordinate_act _ _ _ _ _
        (((unflatten.{u,v,w,t,s} A).map _ _).f _ z) _ }

theorem derivedCoefficientTransitionFiniteOperations : FiniteOperations.{u,v,w,t,s} := by
  intro k _ A
  let R := restrictArrows.{u,v,w,t,s} A
  let E := restrictArrowsEquivalence.{u,v,w,t,s} A
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨isoOfComponents
      (fun _ _ => ULift.moduleEquiv.trans (ULift.moduleEquiv.trans ULift.moduleEquiv.symm))
      (fun _ _ _ => rfl) (fun _ _ _ _ _ _ => rfl), fun _ _ _ => rfl⟩
  · intro Z
    have h : IsZero Z ↔ IsZero ((doubleLift.{u,v,w,t,s} A).obj Z) :=
      zeroComparison.{u,max v w t,w,s} Z
    refine h.trans ?_
    rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero]
    let Z' := (doubleLift.{u,v,w,t,s} A).obj Z
    have hz : R.map (0 : Z' ⟶ Z') = 0 :=
      strict_hom_ext fun _ _ => rfl
    change 𝟙 Z' = 0 ↔ 𝟙 (R.obj Z') = 0
    rw [← R.map_id, ← hz]
    exact ⟨congrArg R.map, E.fullyFaithfulFunctor.map_injective⟩
  · intro n F S b
    exact ⟨transitionSum.{u,v,w,t,s,0} b, fun _ => rfl, fun _ _ _ _ => rfl⟩
  · refine ⟨fun M n => R.mapIso (shiftIso.{u,max v w t,w,s} M n),
      (fun _ _ _ _ _ => rfl), (fun {_ _} _ _ => strict_hom_ext fun _ _ => rfl), ?_⟩
    refine ⟨fun f => R.mapIso (coneIso.{u,max v w t,w,s} f),
      (fun {_ _} _ _ _ _ => rfl), ?_, ?_⟩
    · intro M N f
      exact ⟨strict_hom_ext fun _ _ => rfl, strict_hom_ext fun _ _ => rfl⟩
    · intro M N M' N' f g p q h
      exact strict_hom_ext fun _ _ => rfl

end

end DerivedFormalization.DG.DerivedCoefficientLift
