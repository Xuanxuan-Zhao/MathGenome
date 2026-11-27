import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CompleteLocalDuality
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CoinductionComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompleteLocalDuality

/-! Complete local duality on the normalized coinduced model. -/

namespace DerivedFormalization.CompleteLocalDuality

open CategoryTheory Opposite CochainComplex.HomComplex
open Specs.DerivedFormalization.CompleteLocalDuality
  (CompleteLocalDualityType RestrictedHomModel derivedHomFromModule derivedHomFromRestrictedModule)
open Specs.DerivedFormalization.Cochains
  (compValue derivedValue stalkValue derivedStalkValue qValue
    derivedCohomologyValue cohomologyValue cohomologyFactorsValue)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue)
open Specs.DerivedFormalization.CoinductionComplex (coinduceValue restrictedHomValue evaluationValue)
open Specs.DerivedFormalization.DerivedRestriction
  (restrictScalarsComplexValue derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)
open Specs.DerivedFormalization.DerivedHomModels (Models)
open Specs.DerivedFormalization.DerivedCoinduction (Coinduction)
open Specs.DerivedFormalization.NormalizedRegularCoverDuality (normalizedObjectValue modelIso)
open Specs.DerivedFormalization.DerivedHomAdjunction (homComparison)
open _root_.DerivedFormalization.Coinduction
  (underlyingHomIso underlyingHomIso_natural isKInjective_coinduce evaluation_apply)
open _root_.Specs.CommutativeAlgebraNotes.CompleteLocalDuality (finiteModules homFromModule)
open _root_.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (ShiftedRingResolution)
open _root_.CommutativeAlgebraNotes.ExactDualCochainCohomologySpecs (precomp)

universe u

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

noncomputable section

variable {S R : Type u} [CommRing S] [CommRing R]

private theorem precomp_apply {U V T : compValue.{u} R} (a : U ⟶ V)
    (n i j : ℤ) (h : i + n = j) (z : Cochain V T n) (x : U.X i) :
    ((precomp (R := R) a T).f n z).v i j h x = z.v i j h (a.f i x) := by
  simp [precomp, Cochain.zero_cochain_comp_v _ _ i j h]

private theorem homFromModule_map (T : compValue.{u} R)
    {X X' : (ModuleCat.{u} R)ᵒᵖ} (f : X ⟶ X') :
    (homFromModule T).map f = internalHomMapValue ((stalkValue R).map f.unop) (𝟙 T) := by
  change precomp (R := R) ((stalkValue R).map f.unop) T =
    internalHomMapValue ((stalkValue R).map f.unop) (𝟙 T)
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro i j h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((precomp (R := R) ((stalkValue R).map f.unop) T).f n z).v i j h x = _
  rw [precomp_apply]
  simp [internalHomMapValue, Cochain.zero_cochain_comp_v _ _ i j h]

section RestrictedHom

variable (f : S →+* R) (I : compValue.{u} S)

private abbrev coinduced := (coinduceValue.{u} f).obj I

private abbrev adjunctionAt (M : (ModuleCat.{u} R)ᵒᵖ) :
    (homFromModule (coinduced f I)).obj M ≅
      restrictedHomValue.{u} f ((stalkValue R).obj M.unop) I :=
  _root_.DerivedFormalization.Coinduction.homIso.{u} f ((stalkValue R).obj M.unop) I

/-- The restricted Hom complex acts on coefficient maps by conjugating
precomposition through the cochain coinduction adjunction. -/
private def restrictedHomFunctor : (ModuleCat.{u} R)ᵒᵖ ⥤ compValue.{u} R where
  obj M := restrictedHomValue.{u} f ((stalkValue R).obj M.unop) I
  map {M M'} a := (adjunctionAt f I M).inv ≫ (homFromModule (coinduced f I)).map a ≫
    (adjunctionAt f I M').hom
  map_id M := by
    change (adjunctionAt f I M).inv ≫ (homFromModule (coinduced f I)).map (𝟙 M) ≫
      (adjunctionAt f I M).hom = 𝟙 _
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp _ _ := by simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

private def restrictedHomModel : RestrictedHomModel f I where
  functor := restrictedHomFunctor f I
  obj_eq _ := rfl
  map_apply {M M'} a n i j h z x := by
    change (ModuleCat.CoextendScalars.equiv f (I.X j)
      (((precomp (R := R) ((stalkValue R).map a) (coinduced f I)).f n
        ((adjunctionAt f I (op M)).inv.f n z)).v i j h x)) (1 : R) = _
    rw [precomp_apply]
    change z.v i j h ((1 : R) • ((stalkValue R).map a).f i x) = _
    rw [one_smul]

private def cochainAdjunction : homFromModule (coinduced f I) ≅
    (restrictedHomModel f I).functor :=
  NatIso.ofComponents (adjunctionAt f I) (by
    intro M M' a
    change (homFromModule (coinduced f I)).map a ≫ (adjunctionAt f I M').hom =
      (adjunctionAt f I M).hom ≫
        (adjunctionAt f I M).inv ≫ (homFromModule (coinduced f I)).map a ≫
          (adjunctionAt f I M').hom
    simp only [Iso.hom_inv_id_assoc])

end RestrictedHom

/-- On the target ring, the natural comparison to the derived Hom is the
single K-injective model computation of U08. -/
private def homModelIso (H : Models.{u,u} R) (T : compValue.{u} R)
    {D : derivedValue.{u} R} (e : (qValue R).obj T ≅ D) (hT : T.IsKInjective) :
    homFromModule T ⋙ qValue R ≅ derivedHomFromModule H D := by
  refine NatIso.ofComponents (fun M =>
    DerivedHomModels.modelIso H (DerivedHomModels.representative (Iso.refl _))
      (DerivedHomModels.representative e) (Or.inr hT)) ?_
  intro M M' a
  rw [Functor.comp_map, homFromModule_map]
  exact DerivedHomModels.modelIso_chain_natural H (Iso.refl _) (Iso.refl _) e e
    (Or.inr hT) (Or.inr hT) ((derivedStalkValue R).map a.unop) (𝟙 D)
    ((stalkValue R).map a.unop) (𝟙 T)
    (by simp [derivedStalkValue, stalkValue, DerivedCategory.singleFunctor])
    (by simp)

/-- Restriction of the model comparison computes the usual derived Hom over
the cover, by naturality of the cochain adjunction and localization. -/
private def restrictedHomModelIso (f : S →+* R) (H : Models.{u,u} S) (I : compValue.{u} S)
    {Y : derivedValue.{u} S} (e : (qValue S).obj I ≅ Y) (hI : I.IsKInjective) :
    (homFromModule (coinduced f I) ⋙ qValue R) ⋙ derivedRestrictScalarsValue.{u} f ≅
      derivedHomFromRestrictedModule f H Y := by
  let P := stalkValue.{u} R
  let Q := qValue.{u} S
  let L := derivedRestrictScalarsValue.{u} f
  let B := restrictScalarsComplexValue.{u} f
  let factor := derivedRestrictScalarsFactorsValue.{u} f
  let eM (M : (ModuleCat.{u} R)ᵒᵖ) := (factor.app (P.obj M.unop)).symm
  let compare (M : (ModuleCat.{u} R)ᵒᵖ) :=
    DerivedHomModels.modelIso H (DerivedHomModels.representative (eM M))
      (DerivedHomModels.representative e) (Or.inr hI)
  refine NatIso.ofComponents (fun M =>
    factor.app ((homFromModule (coinduced f I)).obj M) ≪≫
      Q.mapIso (underlyingHomIso.{u} f (P.obj M.unop) I) ≪≫ compare M) ?_
  intro M M' a
  let g := P.map a.unop
  let b := (homFromModule (coinduced f I)).map a
  have hb := factor.hom.naturality b
  change L.map ((qValue R).map b) ≫ factor.hom.app _ =
    factor.hom.app _ ≫ Q.map (B.map b) at hb
  have hcochain := underlyingHomIso_natural.{u} f g (𝟙 I)
  rw [CategoryTheory.Functor.map_id] at hcochain
  change B.map (internalHomMapValue ((stalkValue R).map a.unop) (𝟙 (coinduced f I))) ≫
      (underlyingHomIso.{u} f (P.obj M'.unop) I).hom =
    (underlyingHomIso.{u} f (P.obj M.unop) I).hom ≫
      internalHomMapValue (B.map g) (𝟙 I) at hcochain
  rw [← homFromModule_map (coinduced f I) a] at hcochain
  have hg : Q.map (B.map g) = (eM M').hom ≫
      ((derivedStalkValue R) ⋙ L).map a.unop ≫ (eM M).inv := by
    have h := factor.inv.naturality g
    change Q.map (B.map g) ≫ (eM M).hom =
      (eM M').hom ≫ ((derivedStalkValue R) ⋙ L).map a.unop at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hderived := DerivedHomModels.modelIso_chain_natural H (eM M) (eM M') e e
    (Or.inr hI) (Or.inr hI) (((derivedStalkValue R) ⋙ L).map a.unop) (𝟙 Y)
    (B.map g) (𝟙 I) hg (by simp)
  change L.map ((qValue R).map b) ≫ factor.hom.app _ ≫
      Q.map (underlyingHomIso.{u} f (P.obj M'.unop) I).hom ≫ (compare M').hom =
    (factor.hom.app _ ≫ Q.map (underlyingHomIso.{u} f (P.obj M.unop) I).hom ≫
      (compare M).hom) ≫ (derivedHomFromRestrictedModule f H Y).map a
  rw [reassoc_of% hb]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, hcochain, CategoryTheory.Functor.map_comp_assoc]
  exact congrArg (fun k => factor.hom.app _ ≫ Q.map
    (underlyingHomIso.{u} f (P.obj M.unop) I).hom ≫ k) hderived

/-- The normalized dualizing object gives both the coinduction comparison
and local duality, with the derived counit induced by evaluation at one. -/
theorem completeLocalDuality : CompleteLocalDualityType.{u} := by
  intro S R _ _ _ _ _ _ _ f _ hf d hd G HS HR J E Y D C L H
  have hJ : J.complex.IsKInjective := by
    let := J.isStrictlyGE
    let := J.injective
    exact CochainComplex.isKInjective_of_injective J.complex J.lower
  have hC : C.IsKInjective := isKInjective_coinduce.{u} f J.complex hJ
  let := J.quasiIso
  let eJ : Y ≅ (qValue S).obj J.complex := asIso ((qValue S).map J.ι)
  let eD : D ≅ (qValue R).obj C := modelIso f G J hJ
  let F := restrictedHomModel f J.complex
  let a := cochainAdjunction f J.complex
  let b : homFromModule C ⋙ qValue R ≅ H := homModelIso HR C eD.symm hC
  let e : H ≅ F.functor ⋙ qValue R := b.symm ≪≫ Functor.isoWhiskerRight a (qValue R)
  refine ⟨hJ, F, a, e, ?_, ?_, ?_, ?_, ?_, evaluation_apply.{u} f J.complex⟩
  · intros
    rfl
  · intro M
    rfl
  · exact ⟨Functor.isoWhiskerRight (Functor.isoWhiskerRight a.symm (qValue R)) L ≪≫
      restrictedHomModelIso f HS J.complex eJ.symm hJ⟩
  · have hMatlis := (_root_.CommutativeAlgebraNotes.completeLocalDuality
      f hf hd J E).2
    intro q
    obtain ⟨m⟩ := hMatlis q
    let U := homFromModule C
    let V := derivedCohomologyValue R (-q)
    let compare := Functor.isoWhiskerRight b.symm V ≪≫
      Functor.associator U (qValue R) V ≪≫
      Functor.isoWhiskerLeft U (cohomologyFactorsValue R (-q))
    exact ⟨Functor.isoWhiskerLeft (finiteModules R).ι.op compare ≪≫ m.symm⟩
  · exact G.modelCounit f J.complex eJ hJ

end

end DerivedFormalization.CompleteLocalDuality
