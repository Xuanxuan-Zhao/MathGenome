import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalDualityAfterCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionOfFiniteExt
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularCover
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay

noncomputable section

open CategoryTheory Opposite
open CategoryTheory.Abelian (Ext)
open HomologicalComplex (homologyFunctor)
open IsLocalRing (maximalIdeal)

namespace CommutativeAlgebraNotes

open Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality
open Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel (Complex stalk dualizingComplex)
open Specs.CommutativeAlgebraNotes.CompleteLocalDuality (finiteModules homFromModule)
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)
open Specs.CommutativeAlgebraNotes.LocalCohomologyCompletion (adicCompletionFunctor)
open Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open MatlisDualFunctorSpecs (matlisDualValue matlisBidualEvaluationValue residueFieldEnvelopeValue)
open RegularCoverDualizingModel (homologyHomEquiv homPrecomposition coinduced_bounded_injective)
open private homologyHomEquiv_precomp shiftedStalkHom_subsingleton
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel

universe u v w

section Shift

open DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable {D : Complex R} [D.IsKInjective] {W : ModuleCat.{u} R}

private def homCohomologyIsoExt
    {s : ℤ} (e : Q.obj D ≅ ((singleFunctor (ModuleCat.{u} R) 0).obj W)⟦s⟧)
    (q j : ℤ) (hj : s + q = j) :
    homFromModule D ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℤ) q ≅ extInto W j := by
  let V := (singleFunctor (ModuleCat.{u} R) 0).obj W
  let t : Q.obj (D⟦q⟧) ≅ V⟦j⟧ :=
    (Q.commShiftIso q).app D ≪≫ (shiftFunctor _ q).mapIso e ≪≫
      (shiftFunctorAdd' _ s q j hj).symm.app V
  let c (X : ModuleCat.{u} R) :
      (CochainComplex.linearHomComplex R (stalk R 0 X) D).homology q ≃ₗ[R]
        ShiftedHom ((singleFunctor (ModuleCat.{u} R) 0).obj X) V j :=
    (homologyHomEquiv q).trans (Linear.homCongr R (Iso.refl _) t)
  have natural {X Y : (ModuleCat.{u} R)ᵒᵖ} (f : X ⟶ Y)
      (x : (CochainComplex.linearHomComplex R (stalk R 0 X.unop) D).homology q) :
      c Y.unop ((homFromModule D ⋙ homologyFunctor _ (.up ℤ) q).map f x) =
        (singleFunctor (ModuleCat.{u} R) 0).map f.unop ≫ c X.unop x := by
    change c Y.unop (HomologicalComplex.homologyMap
      (homPrecomposition ((CochainComplex.singleFunctor _ 0).map f.unop) D) q x) =
      Q.map ((CochainComplex.singleFunctor _ 0).map f.unop) ≫ c X.unop x
    simp only [c, LinearEquiv.trans_apply, homologyHomEquiv_precomp,
      Linear.homCongr_apply, Iso.refl_inv, Category.assoc]
    change (𝟙 _ ≫ Q.map ((CochainComplex.singleFunctor _ 0).map f.unop) ≫
        homologyHomEquiv q x ≫ t.hom) =
      (Q.map ((CochainComplex.singleFunctor _ 0).map f.unop) ≫ 𝟙 _ ≫
        homologyHomEquiv q x ≫ t.hom)
    rw [Category.id_comp, Category.id_comp]
  cases j with
  | ofNat n =>
    refine NatIso.ofComponents (fun X =>
      ((c X.unop).trans (Ext.homLinearEquiv (R := R)).symm).toModuleIso) ?_
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let a := Ext.homLinearEquiv (R := R) (X := X.unop) (Y := W) (n := n)
    let b := Ext.homLinearEquiv (R := R) (X := Y.unop) (Y := W) (n := n)
    change b.symm (c Y.unop ((homFromModule D ⋙ homologyFunctor _ (.up ℤ) q).map f x)) =
      (Ext.mk₀ f.unop).comp (a.symm (c X.unop x)) (zero_add n)
    apply b.injective
    rw [LinearEquiv.apply_symm_apply, natural f x]
    change _ = ((Ext.mk₀ f.unop).comp (a.symm (c X.unop x)) (zero_add n)).hom
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
    exact congrArg ((singleFunctor (ModuleCat.{u} R) 0).map f.unop ≫ ·)
      (a.apply_symm_apply (c X.unop x)).symm
  | negSucc n =>
    refine NatIso.ofComponents (fun X => ?_) ?_
    · let Z := (homFromModule D ⋙ homologyFunctor _ (.up ℤ) q).obj X
      change Z ≅ ModuleCat.of R PUnit.{u+1}
      let C := (singleFunctor (ModuleCat.{u} R) 0).obj X.unop
      let t' : (Q.obj (stalk R 0 X.unop) ⟶ Q.obj ((stalk R 0 W)⟦Int.negSucc n⟧)) ≃ₗ[R]
          ShiftedHom C V (Int.negSucc n) :=
        Linear.homCongr R (Iso.refl _) ((Q.commShiftIso (Int.negSucc n)).app (stalk R 0 W))
      have hs := shiftedStalkHom_subsingleton X.unop W (Int.negSucc n) (by omega)
      let hs' : Subsingleton (ShiftedHom C V (Int.negSucc n)) :=
        ⟨fun x y => t'.symm.injective (@Subsingleton.elim _ hs _ _)⟩
      letI : Subsingleton Z :=
        ⟨fun x y => (c X.unop).injective (@Subsingleton.elim _ hs' _ _)⟩
      exact (LinearEquiv.ofSubsingleton (R := R) Z PUnit.{u+1}).toModuleIso
    · intro X Y f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let : Subsingleton ((extInto W (Int.negSucc n)).obj Y) :=
        inferInstanceAs (Subsingleton PUnit.{u+1})
      exact Subsingleton.elim _ _

end Shift

section Evaluation

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]

private theorem duality_of_artinian {C : Type v} [Category.{w} C]
    (E : residueFieldEnvelopeValue R) {H : C ⥤ ModuleCat.{u} R}
    {F T : Cᵒᵖ ⥤ ModuleCat.{u} R}
    (hH : ∀ X, IsArtinian R (H.obj X)) (c : F ≅ H.op ⋙ matlisDualValue E) (a : F ≅ T) :
    evaluationCompatible E c a := by
  let D := matlisDualValue E
  let b (X : C) : H.obj X ≅ ((H.op ⋙ D).rightOp ⋙ D).obj X :=
    letI := hH X
    (LinearEquiv.ofBijective _ (matlisEvaluation_bijective_of_isArtinian E (H.obj X))).toModuleIso
  let eval : H ≅ (H.op ⋙ D).rightOp ⋙ D := NatIso.ofComponents b (by
    intro X Y f
    exact (matlisBidualEvaluationValue E).naturality (H.map f))
  let m := c.symm ≪≫ a
  let d : (H.op ⋙ D).rightOp ⋙ D ≅ T.rightOp ⋙ D :=
    NatIso.ofComponents (fun X => D.mapIso (m.app (op X)).op.symm) (by
      intro X Y f
      change D.map (((H.op ⋙ D).map f.op).op) ≫ D.map (m.inv.app (op Y)).op =
        D.map (m.inv.app (op X)).op ≫ D.map (T.map f.op).op
      rw [← D.map_comp, ← D.map_comp]
      apply congrArg D.map
      apply Quiver.Hom.unop_inj
      exact (m.inv.naturality f.op).symm)
  exact ⟨eval ≪≫ d, fun _ => rfl⟩

end Evaluation

private theorem hasRegularCoverModel (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] : HasRegularCoverModel R := by
  obtain ⟨S, _, _, hS, f, hfLocal, hf, _⟩ := CoefficientRings.completeRegularCover R
  let n := (maximalIdeal S).spanFinrank
  have hn : ringKrullDim S = (n : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)).symm
  obtain ⟨J, _, _⟩ := RegularCoverDualizingModel.shiftedRingResolution_exists S n hn
  exact ⟨S, ‹CommRing S›, ‹IsRegularLocalRing S›, hS, f, hfLocal, hf, n, hn, ⟨J⟩⟩

/-- Complete Cohen–Macaulay local duality with its two natural comparisons. -/
theorem completeCohenMacaulayLocalDuality : CompleteCohenMacaulayLocalDualityType.{u} := by
  intro R _ _ _ _ d hd hCM
  refine ⟨hasRegularCoverModel R, ?_⟩
  intro S _ _ _ f _ hf n hn J E i
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let D := dualizingComplex f J.complex
  let : D.IsKInjective := (coinduced_bounded_injective f J).2.2.2
  obtain ⟨e⟩ := (canonicalModuleForCover f hf hn hd J E).2.2.2.mp hCM
  obtain ⟨a⟩ := (completeLocalDuality f hf hn J E).2 i
  let h := homCohomologyIsoExt e (-i) ((d : ℤ) - i) (by omega)
  let iso := (Functor.isoWhiskerRight (Functor.opComp _ _) _) ≪≫
    Functor.associator _ _ _ ≪≫ a ≪≫
    Functor.isoWhiskerLeft (finiteModules R).ι.op h
  refine ⟨iso, duality_of_artinian E (fun X => ?_) (Iso.refl _) iso⟩
  let : Module.Finite R X.obj := X.property
  exact localCohomology_artinian X.obj i

section Completion

open CompletionOfFiniteExt (signedExt complete completionEquiv completionNaturality)
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (IsPowerTorsion completionModule completionScalarTower)
open AdvCommAlg.CohenMacaulay (LocalCohenMacaulay completion_cohenMacaulay completion_dimension)

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Completion commutes with signed Ext into a finite coefficient module,
naturally on finite modules in the first argument. -/
private def extIntoCompletion (ω : ModuleCat.{u} R) [Module.Finite R ω] (j : ℤ) :
    (finiteModules R).ι.op ⋙ extInto ω j ⋙ complete R ≅
      ((finiteModules R).ι ⋙ adicCompletionFunctor R).op ⋙
        extInto ((adicCompletionFunctor R).obj ω) j := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · letI : Module.Finite R X.unop.obj := X.unop.property
    exact (completionEquiv R X.unop.obj ω j).toModuleIso
  · intro X Y f
    let : Module.Finite R X.unop.obj := X.unop.property
    let : Module.Finite R Y.unop.obj := Y.unop.property
    exact (completionNaturality R X.unop.obj Y.unop.obj ω ω f.unop.hom (𝟙 ω) j).1.symm

/-- The two comparisons over the completion, with the first comparison using
the original-ring Matlis dual. A descended canonical module also gives the
completed Ext formula over the original ring. -/
theorem cohenMacaulayLocalDualityAfterCompletion :
    CohenMacaulayLocalDualityAfterCompletionType.{u} := by
  intro R _ _ _ d hd hCM
  let A := Completion R
  let : IsNoetherianRing A := AdvCommAlg.CohenMacaulay.Specs.completionNoetherian R
  refine ⟨hasRegularCoverModel A, ?_⟩
  intro S _ _ _ f _ hf n hn J E i
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  have hdA : ringKrullDim A = (d : WithBot ℕ∞) := by
    rw [← Module.supportDim_self_eq_ringKrullDim A]
    exact (completion_dimension R R).trans ((Module.supportDim_self_eq_ringKrullDim R).trans hd)
  have hCMA : LocalCohenMacaulay A A := (completion_cohenMacaulay R R).2 hCM
  let G := localCohomology (maximalIdeal R) i
  let K := (finiteModules R).ι ⋙ adicCompletionFunctor R
  let D := dualizingComplex f J.complex
  let W := canonicalModule D d
  let : D.IsKInjective := (coinduced_bounded_injective f J).2.2.2
  obtain ⟨e⟩ := (canonicalModuleForCover f hf hn hdA J E).2.2.2.mp hCMA
  obtain ⟨a⟩ := localDualityAfterCompletion f hf hn J E i
  let iso := a ≪≫ Functor.isoWhiskerLeft K.op
    (homCohomologyIsoExt e (-i) ((d : ℤ) - i) (by omega))
  obtain ⟨h, _⟩ := localCohomologyFiniteCompletion (R := R) i
  refine ⟨h, iso, duality_of_artinian E (fun X => ?_) (completedCohomologyDualIso E G h) iso, ?_⟩
  · let : Module.Finite R X.obj := X.property
    let := completionModule (h X.obj)
    let := completionScalarTower (h X.obj)
    exact (MatlisHullUnderCompletion.powerTorsion_artinian_iff (h X.obj)).mp
      (localCohomology_artinian X.obj i)
  · intro ω _ eω
    let c : extInto ((adicCompletionFunctor R).obj ω) ((d : ℤ) - i) ≅
        extInto W ((d : ℤ) - i) := (signedExt A ((d : ℤ) - i)).flip.mapIso eω
    let b := Functor.isoWhiskerLeft K.op c
    let z := extIntoCompletion ω ((d : ℤ) - i) ≪≫ b
    refine ⟨iso ≪≫ z.symm, ?_⟩
    intro X
    change iso.hom.app (op X) ≫ z.inv.app (op X) ≫ z.hom.app (op X) =
      iso.hom.app (op X)
    exact (congrArg (iso.hom.app (op X) ≫ ·) (z.app (op X)).inv_hom_id).trans
      (Category.comp_id _)

end Completion

end CommutativeAlgebraNotes
