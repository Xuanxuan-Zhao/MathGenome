import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.FiniteAffineSchemeDuality
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.AffineModuleSheaves
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedScalarExtension
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedCoinduction
import Mathlib.CategoryTheory.Adjunction.Whiskering

namespace DerivedFormalization.FiniteAffineSchemeDuality

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open Specs.DerivedFormalization.FiniteAffineSchemeDuality
open Specs.DerivedFormalization.CochainRingTransport (adjunctionCompatible)
open Specs.DerivedFormalization.DerivedRestriction (derivedRestrictScalarsValue)
open Specs.DerivedFormalization.DerivedCoinduction (Coinduction)
open Specs.DerivedFormalization.Cochains (qValue)
open Specs.DerivedFormalization.CoinductionComplex (coinduceValue)
open DerivedFormalization.AffineModuleSheaves
  (QC derivedEquiv qcPushforward pushforwardPreservesQC pullbackPreservesQC)

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section Localization

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} {L : D₁ ⥤ D₂} {R : D₂ ⥤ D₁}
  {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}
  (ordinary : F ⊣ G) (derived : L ⊣ R)
  (s : Q₂ ⋙ R ≅ G ⋙ Q₁) (W₂ : MorphismProperty C₂) [Q₂.IsLocalization W₂]

/-- Transpose along the two adjunctions and use full faithfulness of
precomposition by the target localization between the two transpositions. -/
private def derivedHomEquiv (T : D₁ ⥤ D₂) :
    (T ⟶ L) ≃ (Q₁ ⋙ T ⟶ F ⋙ Q₂) :=
  (Iso.homCongr (Iso.refl T) (rightUnitor L).symm).trans
    (((derived.whiskerLeft D₂).homEquiv T (𝟭 D₂)).symm.trans
      ((Localization.fullyFaithfulWhiskeringLeft Q₂ W₂ D₂).homEquiv.trans
        ((Iso.homCongr
          ((associator Q₂ R T).symm ≪≫ isoWhiskerRight s T ≪≫ associator G Q₁ T)
          (rightUnitor Q₂)).trans
          ((ordinary.whiskerLeft D₂).homEquiv (Q₁ ⋙ T) Q₂))))

private theorem derivedHomEquiv_apply {T : D₁ ⥤ D₂} (t : T ⟶ L) :
    derivedHomEquiv ordinary derived s W₂ T t =
      whiskerLeft Q₁ t ≫ (mateEquiv ordinary derived).symm s.inv := by
  ext X
  simp only [derivedHomEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_unit, Functor.FullyFaithful.homEquiv_apply, Adjunction.homEquiv_counit]
  simp [mateEquiv]

include W₂ in
private theorem isRightKanExtension_of_localized_right_adjoint :
    L.IsRightKanExtension ((mateEquiv ordinary derived).symm s.inv) := by
  let α := (mateEquiv ordinary derived).symm s.inv
  let e (T : D₁ ⥤ D₂) := derivedHomEquiv ordinary derived s W₂ T
  have eq (T : D₁ ⥤ D₂) (t : T ⟶ L) :
      e T t = whiskerLeft Q₁ t ≫ α :=
    derivedHomEquiv_apply ordinary derived s W₂ t
  refine ⟨⟨IsTerminal.ofUniqueHom (fun Y => CostructuredArrow.homMk
    ((e Y.left).symm Y.hom) ?_) ?_⟩⟩
  · change whiskerLeft Q₁ ((e _).symm _) ≫ α = _
    rw [← eq, Equiv.apply_symm_apply]
  · intro Y f
    apply CostructuredArrow.hom_ext
    apply (e Y.left).injective
    change e Y.left f.left = e Y.left ((e Y.left).symm Y.hom)
    rw [Equiv.apply_symm_apply, eq]
    exact CostructuredArrow.w f

end Localization

section Equivalences

variable {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]

private theorem equivalenceMate_isIso {F : C ≌ D} {G : E ≌ K}
    {U : C ⥤ E} {V : D ⥤ K} (α : U ⋙ G.functor ⟶ F.functor ⋙ V) :
    IsIso (mateEquiv F.toAdjunction G.toAdjunction α) ↔ IsIso α := by
  let e := mateEquiv (G := U) (H := V) F.toAdjunction G.toAdjunction
  have inverse_iso (β : F.inverse ⋙ U ⟶ V ⋙ G.inverse) [IsIso β] :
      IsIso (e.symm β) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    have : IsIso (F.toAdjunction.unit.app X) := inferInstanceAs (IsIso (F.unitIso.hom.app X))
    have : IsIso (G.toAdjunction.counit.app (V.obj (F.functor.obj X))) :=
      inferInstanceAs (IsIso (G.counitIso.hom.app _))
    simp [e, mateEquiv]
    infer_instance
  constructor
  · intro h
    change IsIso (e α) at h
    rw [← e.symm_apply_apply α]
    exact inverse_iso _
  · intro h
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    have : IsIso (G.toAdjunction.unit.app (U.obj (F.inverse.obj Y))) :=
      inferInstanceAs (IsIso (G.unitIso.hom.app _))
    have : IsIso (F.toAdjunction.counit.app Y) :=
      inferInstanceAs (IsIso (F.counitIso.hom.app Y))
    simp [mateEquiv]
    infer_instance

private theorem affineMate_isIso {F : C ≌ E} {G : D ≌ K}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ K} {R₂ : K ⥤ E}
    (alg : L₁ ⊣ R₁) (geo : L₂ ⊣ R₂) (α : F.functor ⋙ L₂ ⟶ L₁ ⋙ G.functor) :
    IsIso (mateEquiv alg geo α) ↔ IsIso α := by
  rw [← equivalenceMate_isIso (F := G) (G := F),
    iterated_mateEquiv_conjugateEquiv alg geo F.toAdjunction G.toAdjunction]
  exact ⟨fun _ => conjugateEquiv_of_iso (alg.comp G.toAdjunction)
    (F.toAdjunction.comp geo) α, fun _ => inferInstance⟩

private def directImageInModuleCoordinates
    (F : C ≌ E) (G : D ≌ K) {R : D ⥤ C} {P : K ⥤ E}
    (s : G.functor ⋙ P ≅ R ⋙ F.functor) : P ≅ G.inverse ⋙ (R ⋙ F.functor) :=
  (leftUnitor P).symm ≪≫ isoWhiskerRight G.counitIso.symm P ≪≫
    associator G.inverse G.functor P ≪≫ isoWhiskerLeft G.inverse s

end Equivalences

section Affine

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

private def comparison (M : ScalarExtension φ) (N : Coinduction.{u} φ.hom) :
    Comparison φ M N := by
  let E := derivedEquiv A
  let H := derivedEquiv B
  let O : Ordinary φ :=
    ⟨pushforwardPreservesQC φ, pullbackPreservesQC φ,
      inferInstanceAs (qcPushforward φ).Additive,
      inferInstanceAs (PreservesFiniteLimits (qcPushforward φ)),
      inferInstanceAs (PreservesFiniteColimits (qcPushforward φ))⟩
  let s := directImageComparison φ O
  let p := directImageInModuleCoordinates E H s
  let adjL := ((E.symm.toAdjunction.comp M.adj).comp H.toAdjunction).ofNatIsoRight p.symm
  let adjR := (H.symm.toAdjunction.comp (N.adjunction.comp E.toAdjunction)).ofNatIsoLeft p.symm
  let left := (mateEquiv M.adj adjL).symm s.inv
  let right := mateEquiv N.adjunction adjR s.hom
  haveI : IsIso left := (affineMate_isIso (F := E) (G := H) M.adj adjL left).1
    (by
      let m := mateEquiv (G := E.functor) (H := H.functor) M.adj adjL
      change IsIso (m (m.symm s.inv))
      exact (congrArg (fun t => IsIso t) (m.apply_symm_apply s.inv)).mpr
        (inferInstance : IsIso s.inv))
  haveI : IsIso right := (affineMate_isIso (F := H) (G := E) N.adjunction adjR s.hom).2
    (inferInstance : IsIso s.hom)
  refine ⟨O, _, _, adjL, adjR, ⟨?_⟩, asIso left, asIso right, ?_, ?_, ?_⟩
  · exact isRightKanExtension_of_localized_right_adjoint (cochainAdjunction φ O) adjL
      (directImageFactors φ O)
      (HomologicalComplex.quasiIso (QC B) (.up ℤ))
  · exact ⟨unit_mateEquiv_symm M.adj adjL s.inv, mateEquiv_counit_symm M.adj adjL s.inv⟩
  · exact ⟨unit_mateEquiv N.adjunction adjR s.hom, mateEquiv_counit N.adjunction adjR s.hom⟩
  · intro Y I i hI
    let J := (qValue B).obj ((coinduceValue.{u} φ.hom).obj I)
    let k : J ⟶ N.functor.obj Y := (N.modelIso φ.hom I i hI).inv
    let eval := Specs.DerivedFormalization.DerivedCoinduction.evaluation.{u} φ.hom I
    change (directImage φ O).map (H.functor.map k ≫ right.app Y) ≫
        adjR.counit.app (E.functor.obj Y) =
      s.hom.app J ≫ E.functor.map (eval ≫ i.inv)
    let P := directImage φ O
    let ε := adjR.counit.app (E.functor.obj Y)
    let ε₀ := N.adjunction.counit.app Y
    have map_comp := congrArg (fun g => g ≫ ε) (P.map_comp (H.functor.map k) (right.app Y))
    have assoc := Category.assoc (P.map (H.functor.map k)) (P.map (right.app Y)) ε
    have mate := congrArg (fun g => P.map (H.functor.map k) ≫ g)
      (mateEquiv_counit N.adjunction adjR s.hom Y)
    have natural := s.hom.naturality_assoc k (E.functor.map ε₀)
    have model := congrArg (fun g => s.hom.app J ≫ g)
      ((E.functor.map_comp ((derivedRestrictScalarsValue φ.hom).map k) ε₀).symm.trans
        (congrArg (fun g => E.functor.map g) (N.modelCounit φ.hom I i hI)))
    exact map_comp.trans (assoc.trans (mate.trans (natural.trans model)))

/-- The natural comparisons use the specified affine equivalences and identify
both adjunctions, including the trace on each K-injective coinduction model. -/
theorem compareAdjunctions : comparisonType.{u} := by
  intro A B φ _ M N
  exact ⟨comparison φ M N⟩

/-- Finite affine duality in the unbounded derived categories of quasi-coherent modules. -/
theorem finiteAffineDuality : finiteAffineDualityType.{u} := by
  intro A B f _
  let φ := Spec.preimage f
  refine ⟨Spec.map_preimage f, ?_⟩
  let e := RingEquiv.refl A
  let d := RingEquiv.refl B
  let MA := CochainTensorTransport.adequateModelData e
  let MB := CochainTensorTransport.adequateModelData d
  obtain ⟨DA⟩ := DerivedTensor.existsModel MA
  obtain ⟨DB⟩ := DerivedTensor.existsModel MB
  obtain ⟨NA⟩ := DerivedScalarExtension.ringTensor DA.toDescent
  obtain ⟨NB⟩ := DerivedScalarExtension.ringTensor DB.toDescent
  obtain ⟨_, _, _, _, ⟨native⟩⟩ :=
    DerivedScalarExtension.existsExtension (e := e) (d := d) φ.hom NA NB
  obtain ⟨N⟩ := derivedCoinductionExists.{u,u,u} φ.hom
  exact ⟨native.native, N, ⟨comparison φ native.native N⟩⟩

end Affine

end

end DerivedFormalization.FiniteAffineSchemeDuality
