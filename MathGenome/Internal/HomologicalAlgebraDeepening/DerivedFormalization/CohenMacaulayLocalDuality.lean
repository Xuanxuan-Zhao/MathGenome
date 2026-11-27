import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CohenMacaulayLocalDuality
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CanonicalModuleAndConcentration

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CompleteLocalDuality
namespace DerivedFormalization.CohenMacaulayLocalDuality

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Abelian (Ext)
open IsLocalRing (maximalIdeal)
open Specs.DerivedFormalization.Cochains
  (derivedValue derivedStalkValue derivedCohomologyValue cohomologyFactorsValue)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)
open Specs.DerivedFormalization.NormalizedRegularCoverDuality (modelIso)
open Specs.DerivedFormalization.CompleteLocalDuality
  (CompleteLocalDualityType derivedHomFromModule)
open Specs.DerivedFormalization.CohenMacaulayLocalDuality (CohenMacaulayLocalDualityType)
open Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality (extInto)
open Specs.CommutativeAlgebraNotes.CompleteLocalDuality (finiteModules)
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (dualizingComplex)
open Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration (canonicalModule)
open CommutativeAlgebraNotes.MatlisDualFunctorSpecs (matlisDualValue)
open CommutativeAlgebraNotes.CompletionOfFiniteExt (extModule)

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

private def shiftedStalkIso (W : ModuleCat.{u} R) (s : ℤ) :
    ((derivedStalkValue R).obj W)⟦s⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) (-s)).obj W :=
  ((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso s (-s) 0
    (add_neg_cancel s)).app W

private theorem subsingleton_negative_shift (M W : ModuleCat.{u} R) {j : ℤ} (hj : j < 0) :
    Subsingleton ((derivedStalkValue R).obj M ⟶ ((derivedStalkValue R).obj W)⟦j⟧) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{u} R)
  let : ((derivedStalkValue R).obj M).IsLE 0 :=
    inferInstanceAs (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M).IsLE 0)
  let : (((derivedStalkValue R).obj W)⟦j⟧).IsGE (-j) :=
    t.isGE_of_iso (shiftedStalkIso W j).symm (-j)
  have vanishes (f : (derivedStalkValue R).obj M ⟶ ((derivedStalkValue R).obj W)⟦j⟧) :
      f = 0 := t.zero f 0 (-j) (by omega)
  exact ⟨fun f g => (vanishes f).trans (vanishes g).symm⟩

private theorem signedExt_isZero (M W : ModuleCat.{u} R) {j : ℤ} (hj : j < 0) :
    IsZero (extModule R j M W) := by
  cases j with
  | ofNat n => exact (not_lt_of_ge (Int.natCast_nonneg n) hj).elim
  | negSucc n =>
    exact ModuleCat.isZero_iff_subsingleton.2
      (inferInstanceAs (Subsingleton PUnit.{u+1}))

/-- U08 identifies cohomology of derived Hom into a shifted stalk with signed
Ext. The isomorphism acts contravariantly by precomposition in the source. -/
private def derivedHomShiftExtIso (HR : Models.{u,u} R) {D : derivedValue.{u} R}
    {W : ModuleCat.{u} R} {s : ℤ} (e : D ≅ ((derivedStalkValue R).obj W)⟦s⟧)
    (i j : ℤ) (hj : s + i = j) :
    derivedHomFromModule HR D ⋙ derivedCohomologyValue R i ≅ extInto W j := by
  let h := (DerivedFormalization.DerivedHomAdjunction.cohomology HR).some
  let A := DerivedCategory.singleFunctor (ModuleCat.{u} R) 0
  let F := derivedHomFromModule HR D ⋙ derivedCohomologyValue R i
  let shifted : D⟦i⟧ ≅ (A.obj W)⟦j⟧ :=
    (shiftFunctor _ i).mapIso e ≪≫ (shiftFunctorAdd' _ s i j hj).symm.app (A.obj W)
  let cmp (M : ModuleCat.{u} R) : F.obj (op M) ≃ₗ[R] (A.obj M ⟶ (A.obj W)⟦j⟧) :=
    (h.equiv (A.obj M) D i).trans (Linear.homCongr R (Iso.refl _) shifted)
  have cmp_apply (M : ModuleCat.{u} R) (z : F.obj (op M)) :
      cmp M z = h.equiv (A.obj M) D i z ≫ shifted.hom := by
    change (𝟙 _ ≫ h.equiv (A.obj M) D i z) ≫ shifted.hom = _
    rw [Category.id_comp]
  have cmp_natural {X Y : (ModuleCat.{u} R)ᵒᵖ} (f : X ⟶ Y) (z : F.obj X) :
      cmp Y.unop (F.map f z) = A.map f.unop ≫ cmp X.unop z := by
    have he := h.natural (A.map f.unop) (𝟙 D) i z
    rw [(shiftFunctor (derivedValue.{u} R) i).map_id D, Category.comp_id] at he
    calc
      _ = h.equiv (A.obj Y.unop) D i (F.map f z) ≫ shifted.hom :=
        cmp_apply Y.unop _
      _ = (A.map f.unop ≫ h.equiv (A.obj X.unop) D i z) ≫ shifted.hom :=
        congrArg (· ≫ shifted.hom) he
      _ = A.map f.unop ≫ cmp X.unop z := by rw [cmp_apply X.unop z, Category.assoc]
  cases j with
  | ofNat n =>
    refine NatIso.ofComponents (fun X =>
      ((cmp X.unop).trans (Ext.homLinearEquiv (R := R)).symm).toModuleIso) ?_
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let a := Ext.homLinearEquiv (R := R) (X := X.unop) (Y := W) (n := n)
    let b := Ext.homLinearEquiv (R := R) (X := Y.unop) (Y := W) (n := n)
    change b.symm (cmp Y.unop (F.map f z)) =
      (Ext.mk₀ f.unop).comp (a.symm (cmp X.unop z)) (zero_add n)
    apply b.injective
    calc
      _ = cmp Y.unop (F.map f z) := b.apply_symm_apply _
      _ = A.map f.unop ≫ cmp X.unop z := cmp_natural f z
      _ = A.map f.unop ≫ (a.symm (cmp X.unop z)).hom :=
        congrArg (A.map f.unop ≫ ·) (a.apply_symm_apply (cmp X.unop z)).symm
      _ = ((Ext.mk₀ f.unop).comp (a.symm (cmp X.unop z)) (zero_add n)).hom := by
        rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  | negSucc n =>
    refine NatIso.ofComponents (fun X => ?_) ?_
    · let hzero := subsingleton_negative_shift X.unop W (j := Int.negSucc n) (Int.negSucc_lt_zero n)
      letI : Subsingleton (F.obj X) :=
        ⟨fun x y => (cmp X.unop).injective (@Subsingleton.elim _ hzero _ _)⟩
      exact (LinearEquiv.ofSubsingleton (R := R) (F.obj X) PUnit.{u+1}).toModuleIso
    · intro X Y f
      exact (signedExt_isZero Y.unop W (j := Int.negSucc n) (Int.negSucc_lt_zero n)).eq_of_tgt _ _

/-- The Cohen–Macaulay comparison conditional on the full U19 theorem. -/
theorem cohenMacaulayLocalDuality_conditional (localDuality : CompleteLocalDualityType.{u}) :
    CohenMacaulayLocalDualityType.{u} := by
  intro S R _ _ _ _ _ _ _ f _ hf d e hd he hCM G HR E D ω dual top
  obtain ⟨HS, _, _⟩ := DerivedFormalization.DerivedHomModels.canonicalDerivedHom.{u,u} S
  obtain ⟨J, _, _⟩ :=
    CommutativeAlgebraNotes.RegularCoverDualizingModel.shiftedRingResolution_exists S d hd
  obtain ⟨hJ, _, _, _, _, _, _, matlisComparison, _, _⟩ := localDuality f hf d hd G HS HR J E
  let C := dualizingComplex f J.complex
  let ωC := canonicalModule C e
  let onModel := modelIso f G J hJ
  let ωIso : ω ≅ ωC :=
    (derivedCohomologyValue R (-(e : ℤ))).mapIso onModel ≪≫
      (cohomologyFactorsValue R (-(e : ℤ))).app C
  obtain ⟨hFinite, ⟨topDual, topBidual, _⟩, unique, criterion⟩ :=
    CommutativeAlgebraNotes.canonicalModuleForCover f hf hd he J E
  obtain ⟨shiftC⟩ := criterion.mp hCM
  let shift : D ≅ ((derivedStalkValue R).obj ω)⟦(e : ℤ)⟧ :=
    onModel ≪≫ shiftC ≪≫ (shiftFunctor _ (e : ℤ)).mapIso ((derivedStalkValue R).mapIso ωIso.symm)
  have nonzero : Nontrivial ω := by
    obtain ⟨e', he', ht, _⟩ := CommutativeAlgebraNotes.cohenMacaulayRing_iff_localCohomology_concentrated R
    have hdim : e' = e := by exact_mod_cast he'.symm.trans he
    subst e'
    let : Nontrivial top := ht
    have : Nontrivial (dual.obj (op top)) :=
      (CommutativeAlgebraNotes.matlisDual_nontrivial_iff E top).2 inferInstance
    exact (ωIso ≪≫ topDual).toLinearEquiv.symm.injective.nontrivial
  refine ⟨Module.Finite.equiv ωIso.toLinearEquiv.symm, nonzero,
    ⟨ωIso ≪≫ topDual⟩, ⟨topBidual ≪≫ dual.mapIso ωIso.op⟩,
    fun W _ hW => (unique W hW).map (· ≪≫ ωIso.symm), ?_, ⟨shift⟩, ?_⟩
  · intro i hi
    let shifted := shift ≪≫ shiftedStalkIso ω (e : ℤ)
    apply IsZero.of_iso _ ((derivedCohomologyValue R i).mapIso shifted)
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ (-(e : ℤ)) i h
    · exact DerivedCategory.isZero_of_isLE _ (-(e : ℤ)) i h
  · intro q H B T
    obtain ⟨m⟩ := matlisComparison q
    let b : B ≅ H := m.symm
    let t : H ≅ T := Functor.isoWhiskerLeft (finiteModules R).ι.op
      (derivedHomShiftExtIso HR shift (-q) ((e : ℤ) - q) (by omega))
    refine ⟨⟨b⟩, ⟨t⟩, ⟨b ≪≫ t⟩, ?_⟩
    intro h X
    have hz : IsZero (T.obj X) := signedExt_isZero X.unop.obj ω h
    exact ⟨hz.of_iso ((b ≪≫ t).app X), hz.of_iso (t.app X), hz⟩

end

end DerivedFormalization.CohenMacaulayLocalDuality

universe v8_closure_a02438f86638bdd9_u0
theorem _root_.«DerivedFormalization».«CohenMacaulayLocalDuality».«cohenMacaulayLocalDuality» : _root_.«Specs».«DerivedFormalization».«CohenMacaulayLocalDuality».«CohenMacaulayLocalDualityType».{v8_closure_a02438f86638bdd9_u0} :=
  @_root_.«DerivedFormalization».«CohenMacaulayLocalDuality».«cohenMacaulayLocalDuality_conditional».{v8_closure_a02438f86638bdd9_u0} (@_root_.«DerivedFormalization».«CompleteLocalDuality».«completeLocalDuality».{v8_closure_a02438f86638bdd9_u0})
