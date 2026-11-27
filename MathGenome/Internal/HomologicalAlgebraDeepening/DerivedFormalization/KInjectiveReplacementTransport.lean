import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KInjectiveReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KInjectiveReplacementTransport
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
namespace DerivedFormalization.KInjectiveReplacementTransport

open CategoryTheory CategoryTheory.Limits Opposite
open Specs.DerivedFormalization.Cochains (compValue qValue)
open Specs.DerivedFormalization.InjectiveTruncationTower (stage projection)
open Specs.DerivedFormalization.CochainCoefficientLift (lift)
open Specs.DerivedFormalization.KInjectiveReplacementTransport
open Specs.DerivedFormalization.TowerExactSequence (transition)

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Truncation

universe v u t

variable {R : Type u} [CommRing R]

private theorem projectionAtCutoff (X : compValue.{v} R) (a : ℤ) :
    (X.πTruncGE a).f a ≫ (X.truncGEXIsoOpcycles a).hom = X.pOpcycles a := by
  let e := ComplexShape.embeddingUpIntGE a
  have ha : e.f 0 = a := by simp [e]
  have hb : e.BoundaryGE 0 := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  unfold CochainComplex.πTruncGE HomologicalComplex.πTruncGE CochainComplex.truncGEXIsoOpcycles
  rw [e.liftExtend_f _ _ ha,
    X.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e ha hb]
  simp [HomologicalComplex.truncGEXIsoOpcycles, e]

private theorem projectionAboveCutoff (X : compValue.{v} R) (a i : ℤ) (hi : a < i) :
    (X.πTruncGE a).f i ≫ (X.truncGEXIso a i hi).hom = 𝟙 _ := by
  let e := ComplexShape.embeddingUpIntGE a
  have he : e.f (i - a).natAbs = i := by
    change a + ((i - a).natAbs : ℤ) = i
    rw [Int.natAbs_of_nonneg (by omega), add_sub_cancel]
  have hb : ¬ e.BoundaryGE (i - a).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    omega
  unfold CochainComplex.πTruncGE HomologicalComplex.πTruncGE CochainComplex.truncGEXIso
  rw [e.liftExtend_f _ _ he,
    X.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e he hb]
  simp [HomologicalComplex.truncGEXIso, e]

private theorem liftOpcyclesProjection (X : compValue.{v} R) (i : ℤ) :
    (ModuleCat.uliftFunctor.{max u t, v} R).map (X.pOpcycles i) ≫
      ((X.sc i).mapOpcyclesIso (ModuleCat.uliftFunctor.{max u t, v} R)).inv =
      ((lift.{max u t, v} R).obj X).pOpcycles i := by
  exact ShortComplex.RightHomologyData.p_comp_opcyclesIso_inv
    ((X.sc i).rightHomologyData.map (ModuleCat.uliftFunctor.{max u t, v} R))

private def truncationTermIso (X : compValue.{v} R) (a i : ℤ) :
    ((lift.{max u t, v} R).obj (X.truncGE a)).X i ≅ (((lift.{max u t, v} R).obj X).truncGE a).X i :=
  if hi : a < i then
    (ModuleCat.uliftFunctor.{max u t, v} R).mapIso (X.truncGEXIso a i hi) ≪≫
      (((lift.{max u t, v} R).obj X).truncGEXIso a i hi).symm
  else if h : i = a then by
    subst i
    exact cutoffIso.{v, u, t} X a
  else
    ((ModuleCat.uliftFunctor.{max u t, v} R).map_isZero
      ((X.truncGE a).isZero_of_isStrictlyGE a i (by omega))).iso
      ((((lift.{max u t, v} R).obj X).truncGE a).isZero_of_isStrictlyGE a i (by omega))

private theorem truncationTermIso_fac (X : compValue.{v} R) (a i : ℤ) :
    ((lift.{max u t, v} R).map (X.πTruncGE a)).f i ≫ (truncationTermIso.{v, u, t} X a i).hom =
      (((lift.{max u t, v} R).obj X).πTruncGE a).f i := by
  change (ModuleCat.uliftFunctor.{max u t, v} R).map ((X.πTruncGE a).f i) ≫ _ = _
  rcases lt_trichotomy i a with hi | he | hi
  · exact ((((lift.{max u t, v} R).obj X).truncGE a).isZero_of_isStrictlyGE a i hi).eq_of_tgt _ _
  · subst i
    rw [truncationTermIso, dite_eq_right (lt_irrefl a), dite_eq_left rfl]
    simp only [cutoffIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ← Category.assoc]
    rw [← Functor.map_comp, projectionAtCutoff, liftOpcyclesProjection,
      ← projectionAtCutoff ((lift.{max u t, v} R).obj X) a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [truncationTermIso, dite_eq_left hi]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, ← Category.assoc]
    rw [← Functor.map_comp, projectionAboveCutoff X a i hi,
      CategoryTheory.Functor.map_id, Category.id_comp]
    let Y := (lift.{max u t, v} R).obj X
    apply (cancel_mono (Y.truncGEXIso a i hi).hom).1
    rw [Iso.inv_hom_id, projectionAboveCutoff Y a i hi]
    rfl

private instance liftProjectionEpi (X : compValue.{v} R) (a i : ℤ) :
    Epi (((lift.{max u t, v} R).map (X.πTruncGE a)).f i) := by
  change Epi ((ModuleCat.uliftFunctor.{max u t, v} R).map ((X.πTruncGE a).f i))
  let : Epi ((X.πTruncGE a).f i) :=
    inferInstanceAs (Epi ((HomologicalComplex.πTruncGE X (ComplexShape.embeddingUpIntGE a)).f i))
  infer_instance

private def truncationIso (X : compValue.{v} R) (a : ℤ) :
    (lift.{max u t, v} R).obj (X.truncGE a) ≅ ((lift.{max u t, v} R).obj X).truncGE a :=
  HomologicalComplex.Hom.isoOfComponents (truncationTermIso.{v, u, t} X a)
    (fun i j _ ↦ by
      apply (cancel_epi (((lift.{max u t, v} R).map (X.πTruncGE a)).f i)).1
      rw [← Category.assoc, truncationTermIso_fac, (((lift.{max u t, v} R).obj X).πTruncGE a).comm,
        ((lift.{max u t, v} R).map (X.πTruncGE a)).comm_assoc, truncationTermIso_fac])

private theorem truncationIso_fac (X : compValue.{v} R) (a : ℤ) :
    (lift.{max u t, v} R).map (X.πTruncGE a) ≫ (truncationIso.{v, u, t} X a).hom =
      ((lift.{max u t, v} R).obj X).πTruncGE a :=
  HomologicalComplex.hom_ext _ _ (truncationTermIso_fac.{v, u, t} X a)

private theorem truncationIso_components (X : compValue.{v} R) (n : ℕ) :
    TruncationComponents.{v, u, t} X n (truncationIso.{v, u, t} X (-(n : ℤ))) := by
  let a := -(n : ℤ)
  refine ⟨?_, ?_, ?_⟩
  · change (truncationTermIso.{v, u, t} X a a).hom = _
    rw [truncationTermIso, dite_eq_right (lt_irrefl a), dite_eq_left rfl]
  · intro i hi
    change (truncationTermIso.{v, u, t} X a i).hom = _
    rw [truncationTermIso, dite_eq_left hi]
  · intro i hi
    exact ((((lift.{max u t, v} R).obj X).truncGE a).isZero_of_isStrictlyGE a i hi).eq_of_tgt _ _

end Truncation

section Replacement

universe v u t

open private injective_of_split_tower_limit from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KInjectiveReplacement

private theorem liftedReplacement : liftedReplacementType.{v, u, t} := by
  intro R _ X
  let L := lift.{max u t, v} R
  let Y := L.obj X
  obtain ⟨s, hs, hSurj, π, hπ, ⟨hX⟩⟩ := truncationTowerExists X
  obtain ⟨s', hs', hSurj', π', hπ', ⟨hY⟩⟩ := truncationTowerExists Y
  let A := Functor.ofOpSequence s
  let B := Functor.ofOpSequence s'
  let stageIso (n : ℕ) := truncationIso.{v, u, t} X (-(n : ℤ))
  have hStageIso (n : ℕ) : L.map (projection X n) ≫ (stageIso n).hom = projection Y n :=
    truncationIso_fac.{v, u, t} X _
  let comparison : A ⋙ L ⟶ B :=
    NatTrans.ofOpSequence (fun n ↦ (stageIso n).hom) (by
      intro n
      dsimp only [Functor.comp_map, A, B]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
      let q := L.map (projection X (n + 1))
      have : Epi q := HomologicalComplex.epi_of_epi_f _ (fun i ↦
        liftProjectionEpi.{v, u, t} X (-(↑(n + 1) : ℤ)) i)
      apply (cancel_epi q).1
      change L.map (projection X (n + 1)) ≫ _ = _
      rw [← Category.assoc, ← L.map_comp, hs, hStageIso,
        ← Category.assoc, hStageIso, hs'])
  let (n : ℕᵒᵖ) : IsIso (comparison.app n) :=
    inferInstanceAs (IsIso (stageIso n.unop).hom)
  let : IsIso comparison := NatIso.isIso_of_isIso_app comparison
  let e := asIso comparison
  let := CochainCoefficientLift.preservesLimits.{max u t, v} R ℕᵒᵖ
  have hLifted : IsLimit ((Cone.postcompose e.hom).obj (L.mapCone (Cone.mk X π))) :=
    (IsLimit.postcomposeHomEquiv e _).symm (isLimitOfPreserves L hX)
  obtain ⟨J, ι, hJ, hSplit⟩ := injectiveTruncationTowerExists.{u, max v t} Y s' hs'
  let yIso : Y ≅ limit B := hY.conePointUniqueUpToIso (limit.isLimit B)
  let f := yIso.hom ≫ limMap ι
  have hSurjB (n : ℕ) (i : ℤ) : Function.Surjective ((transition B n).f i) := by
    change Function.Surjective (((Functor.ofOpSequence s').map
      (homOfLE (Nat.le_add_right n 1)).op).f i)
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact hSurj' n i
  have hSurjJ (n : ℕ) (i : ℤ) : Function.Surjective ((transition J n).f i) := by
    obtain ⟨σ, hσ⟩ := hSplit n i
    intro x
    exact ⟨σ x, congrArg (fun k : (J.obj (op n)).X i ⟶ _ ↦ k x) hσ⟩
  have : QuasiIso (limMap ι) :=
    towerLimitMap_quasiIso R B J ι hSurjB hSurjJ (fun n ↦ (hJ n).2.2.2)
  have (n : ℕᵒᵖ) : Mono (ι.app n) :=
    HomologicalComplex.mono_of_mono_f _ (hJ n.unop).2.2.1
  have hfMono (i : ℤ) : Mono (f.f i) := by dsimp [f]; infer_instance
  have hfQuasi : QuasiIso f := by dsimp [f]; infer_instance
  have hπe (n : ℕ) : L.map (π.app (op n)) ≫ e.hom.app (op n) = π'.app (op n) := by
    rw [hπ, hπ']
    exact hStageIso n
  have he (n : ℕ) : e.app (op n) = stageIso n := Iso.ext rfl
  refine ⟨s, s', π, π', e, fun n ↦ ⟨hπ n, hπ' n, hπe n, ?_⟩,
    fun n i ↦ ⟨hSurj n i, hSurj' n i⟩, ⟨hX⟩, ⟨hLifted⟩, ⟨hY⟩, J, ι, hJ, hSplit, f,
    ?_, hfMono, hfQuasi, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact truncationIso_components X n
  · intro n
    dsimp [f]
    rw [Category.assoc, limMap_π, ← Category.assoc, limit.conePointUniqueUpToIso_hom_comp]
  · refine towerLimit_isKInjective R J hSplit (fun n ↦ ?_)
    have := (hJ n).1
    have := (hJ n).2.1
    exact CochainComplex.isKInjective_of_injective (J.obj (op n)) (-(n : ℤ))
  · intro i
    let F := HomologicalComplex.eval (ModuleCat.{max u v t} R) (.up ℤ) i
    exact injective_of_split_tower_limit (isLimitOfPreserves F (limit.isLimit J))
      (fun n ↦ (hJ n).2.1 i) (fun n ↦ hSplit n i)
  · intro i
    exact (CochainCoefficientLift.fromOriginal_injective.{max u t} f i).2 (hfMono i)
  · exact (CochainCoefficientLift.fromOriginal_quasiIso_iff.{max u t} f).1 hfQuasi
  · exact ⟨(CochainCoefficientLift.liftDFactors.{max u t, v} R).app X ≪≫
      asIso ((qValue.{max u v t} R).map f)⟩

open Specs.DerivedFormalization.CochainRingTransport
  (complexPropertiesType modulePropertiesType shrinkRingEquivValue moduleEquivalenceValue
    complexEquivalenceValue complexFunctorValue)

private theorem smallReplacement
    (hComplex : complexPropertiesType.{v, u}) (hModule : modulePropertiesType.{v, u}) :
    smallReplacementType.{v, u} := by
  intro R _ _ X
  let e := shrinkRingEquivValue.{v, u} R
  let E := complexEquivalenceValue e
  let F := complexFunctorValue e
  obtain ⟨J, g, hgMono, hgQI, hJK, hJInj⟩ :=
    kInjectiveReplacement.{v, v} (F.obj X)
  let I := E.inverse.obj J
  let c : F.obj I ≅ J := E.counitIso.app J
  let f : X ⟶ I := F.preimage (g ≫ c.inv)
  have hf : F.map f = g ≫ c.inv := F.map_preimage _
  have hp := hComplex e X I f
  refine ⟨I, f, ?_, ?_, ?_, ?_⟩
  · intro i
    apply (ModuleCat.mono_iff_injective _).2
    apply (hp.2.2.1 i).1
    rw [hf, HomologicalComplex.comp_f]
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  · apply hp.2.1.1
    rw [hf]
    infer_instance
  · have hFI : CochainComplex.IsKInjective (F.obj I) := CochainComplex.isKInjective_of_iso c.symm
    refine ⟨fun {K} p hK ↦ ?_⟩
    have hFK := (hComplex e K I p).1.2 hK
    obtain ⟨H⟩ := hFI.nonempty_homotopy_zero (F.map p) hFK
    refine ⟨(moduleEquivalenceValue e).functor.preimageHomotopy (f₁ := p) (f₂ := 0) ?_⟩
    simpa only [Functor.map_zero] using H
  · intro i
    exact (hModule e (I.X i)).2.1.1
      (Injective.of_iso (HomologicalComplex.Hom.isoApp c.symm i) (hJInj i))

end Replacement

open Specs.DerivedFormalization.CochainRingTransport

/-- Conditional transport of unbounded injective replacement, including the native
small-ring case. The ring transport premises are in the prescribed order. -/
theorem replacementTransport_conditional.{v, u, t, s}
    (_coextensionMate : coextensionMateType.{v, u, s})
    (_complexComponents : complexComponentsType.{v, u})
    (hComplex : complexPropertiesType.{v, u})
    (_complexRestrictionComponents : complexRestrictionComponentsType.{v, u, s})
    (_compositionCoherence : compositionCoherenceType.{v, u, s, t})
    (_derivedRestrictionComponents : derivedRestrictionComponentsType.{v, u, s})
    (_extensionMate : extensionMateType.{v, u, s})
    (_flatness : flatnessType.{v, u})
    (_identityCoherence : identityCoherenceType.{v, u})
    (_inducedEquivalences : inducedEquivalencesType.{v, u})
    (_localizationCompatibility : localizationCompatibilityType.{v, u})
    (_moduleAction : moduleActionType.{v, u})
    (_moduleExact : moduleExactType.{v, u})
    (_moduleMap : moduleMapType.{v, u})
    (hModule : modulePropertiesType.{v, u})
    (_rankOneGenerator : rankOneGeneratorType.{v, u})
    (_representedCoextensionMate : representedCoextensionMateType.{v, u, s})
    (_representedExtensionMate : representedExtensionMateType.{v, u, s})
    (_restrictionIdentityOnCarriers : restrictionIdentityOnCarriersType.{v, u, s})
    (_shiftCompatibility : shiftCompatibilityType.{v, u})
    (_uliftAction : uliftActionType.{v, u})
    (_uliftConjugate : uliftConjugateType.{v, u, s})
    : replacementTransportType.{v, u, t} :=
  ⟨liftedReplacement, kInjectiveReplacement, smallReplacement hComplex hModule⟩

end

end DerivedFormalization.KInjectiveReplacementTransport

universe v8_closure_d517c7419748a837_u0 v8_closure_d517c7419748a837_u1 v8_closure_d517c7419748a837_u2
theorem _root_.«DerivedFormalization».«KInjectiveReplacementTransport».«replacementTransport» : _root_.«Specs».«DerivedFormalization».«KInjectiveReplacementTransport».«replacementTransportType».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, v8_closure_d517c7419748a837_u2} :=
  @_root_.«DerivedFormalization».«KInjectiveReplacementTransport».«replacementTransport_conditional».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, v8_closure_d517c7419748a837_u2, 0} (@_root_.«DerivedFormalization».«CochainRingTransport».«coextensionMate».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«complexComponents».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«complexProperties».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«complexRestrictionComponents».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«compositionCoherence».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0, v8_closure_d517c7419748a837_u2}) (@_root_.«DerivedFormalization».«CochainRingTransport».«derivedRestrictionComponents».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«extensionMate».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«flatness».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«identityCoherence».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«inducedEquivalences».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«localizationCompatibility».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«moduleAction».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«moduleExact».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«moduleMap».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«moduleProperties».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«rankOneGenerator».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«representedCoextensionMate».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«representedExtensionMate».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«restrictionIdentityOnCarriers».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0}) (@_root_.«DerivedFormalization».«CochainRingTransport».«shiftCompatibility».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«uliftAction».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1}) (@_root_.«DerivedFormalization».«CochainRingTransport».«uliftConjugate».{v8_closure_d517c7419748a837_u0, v8_closure_d517c7419748a837_u1, 0})
