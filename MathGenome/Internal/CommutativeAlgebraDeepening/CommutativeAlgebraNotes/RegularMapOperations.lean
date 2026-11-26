import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularMapOperations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.GeometricRegularityFieldExtension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FlatLocalRegularity

/-! Permanence properties of regular ring homomorphisms. -/

universe u v w x

open scoped TensorProduct
open Algebra.TensorProduct

namespace CommutativeAlgebraNotes.Excellence

private theorem noetherianRegular_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : IsNoetherianRing R ∧ RegularRing R) : IsNoetherianRing S ∧ RegularRing S := by
  let : IsNoetherianRing R := h.1
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  let : IsRegularRing R := (regularRing_iff R).mp h.2
  exact ⟨inferInstance, (regularRing_iff S).mpr (IsRegularRing.of_ringEquiv e)⟩

private theorem GeometricallyRegular.of_algEquiv
    {k T T' : Type*} [Field k] [CommRing T] [CommRing T']
    [Algebra k T] [Algebra k T'] (e : T ≃ₐ[k] T')
    (h : GeometricallyRegular k T) : GeometricallyRegular k T' := by
  intro L _ _ _
  exact noetherianRegular_of_ringEquiv (congr (AlgEquiv.refl : L ≃ₐ[k] L) e).toRingEquiv
    (h.regular_tensorProduct L)

private theorem noetherianRegular_localization
    {R : Type*} [CommRing R] (M : Submonoid R) (h : IsNoetherianRing R ∧ RegularRing R) :
    IsNoetherianRing (Localization M) ∧ RegularRing (Localization M) := by
  refine ⟨IsLocalization.isNoetherianRing M _ h.1, ?_⟩
  intro q hq
  let : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R (Localization M)))) :=
    h.2 (q.comap (algebraMap R (Localization M)))
  exact .of_ringEquiv (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

private theorem RegularMap.baseChange_essFiniteType
    (A B A' B' : Type*) [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing A'] [IsNoetherianRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Algebra.IsPushout A A' B B']
    [Algebra.EssFiniteType A A']
    (h : RegularMap A B (algebraMap A B)) : RegularMap A' B' (algebraMap A' B') := by
  rw [regularMap_algebraMap_iff] at h ⊢
  let : Module.Flat A B := h.1
  refine ⟨Module.Flat.isBaseChange A A' B B' Algebra.IsPushout.out, ?_⟩
  intro q hq
  let p := q.comap (algebraMap A A')
  let : p.IsPrime := Ideal.IsPrime.comap _
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.map p q (algebraMap A A') rfl).toAlgebra
  let : IsScalarTower A p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun a ↦ by
      change algebraMap A q.ResidueField a = Ideal.ResidueField.map p q (algebraMap A A') rfl
        (algebraMap A p.ResidueField a)
      rw [Ideal.ResidueField.map_algebraMap, ← IsScalarTower.algebraMap_apply]
  let : Algebra.EssFiniteType A q.ResidueField := .comp A A' _
  let : Algebra.EssFiniteType p.ResidueField q.ResidueField := .of_comp A _ _
  let e := (cancelBaseChange A p.ResidueField q.ResidueField q.ResidueField B).trans
    ((cancelBaseChange A A' q.ResidueField q.ResidueField B).symm.trans
      (congr (AlgEquiv.refl : q.ResidueField ≃ₐ[q.ResidueField] q.ResidueField)
        (Algebra.IsPushout.equiv A A' B B')))
  exact GeometricallyRegular.of_algEquiv e
    (GeometricallyRegular.fieldExtension p.ResidueField (p.Fiber B) q.ResidueField (h.2 p))

/-- Regularity is preserved by finite-type base change. -/
theorem RegularMap.baseChange : Specs.regularMap_baseChangeType.{u,v,w,x} := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  let : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  let : Algebra.IsPushout A B A' B' :=
    Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout A A' B B')
  let : IsNoetherianRing (B ⊗[A] A') := Algebra.FiniteType.isNoetherianRing B _
  let : IsNoetherianRing B' :=
    isNoetherianRing_of_ringEquiv _ (Algebra.IsPushout.equiv A B A' B').toRingEquiv
  exact RegularMap.baseChange_essFiniteType A B A' B' h

/-- Localizing the target preserves regularity. -/
theorem RegularMap.localizationTarget : Specs.regularMap_localizationTargetType.{u,v,w} := by
  intro A B B' _ _ _ _ _ _ _ _ _ N _ h
  let : IsNoetherianRing B' := IsLocalization.isNoetherianRing N B' inferInstance
  change RegularMap A B _ at h
  change RegularMap A B' _
  rw [regularMap_algebraMap_iff] at h ⊢
  let : Module.Flat A B := h.1
  let : Module.Flat B B' := IsLocalization.flat B' N
  refine ⟨Module.Flat.trans A B B', ?_⟩
  intro p hp L _ _ _
  let : Algebra A L := Algebra.compHom L (algebraMap A p.ResidueField)
  let : IsScalarTower A p.ResidueField L := .of_algebraMap_eq' rfl
  let e := cancelBaseChange A p.ResidueField L L B
  let e' := cancelBaseChange A p.ResidueField L L B'
  let M : Submonoid (L ⊗[A] B) := N.map (includeRight (R := A) (A := L))
  let eLoc := IsLocalization.tensorProductEquivOfMapIncludeRight A L N B' (Localization M)
  have hTest : IsNoetherianRing (L ⊗[A] B) ∧ RegularRing (L ⊗[A] B) :=
    noetherianRegular_of_ringEquiv e.toRingEquiv ((h.2 p).regular_tensorProduct L)
  exact noetherianRegular_of_ringEquiv (eLoc.symm.trans e'.symm).toRingEquiv
    (noetherianRegular_localization M hTest)

/-- Compatible localizations of the source and target preserve regularity. -/
theorem RegularMap.localization : Specs.regularMap_localizationType.{u,v,w,x} := by
  intro A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ M N _ _ h
  let : IsNoetherianRing A' := IsLocalization.isNoetherianRing M A' inferInstance
  let : IsNoetherianRing B' := IsLocalization.isNoetherianRing N B' inferInstance
  let : Algebra.EssFiniteType A A' := .of_isLocalization A' M
  let : IsLocalization (Algebra.algebraMapSubmonoid B' M) B' := by
    apply IsLocalization.of_le_isUnit
    rintro _ ⟨a, ha, rfl⟩
    rw [IsScalarTower.algebraMap_apply A A' B']
    exact (IsLocalization.map_units A' (⟨a, ha⟩ : M)).map (algebraMap A' B')
  let : Algebra.IsPushout A A' B' B' := (Algebra.isPushout_of_isLocalization M A' B' B').symm
  exact RegularMap.baseChange_essFiniteType A B' A' B'
    (RegularMap.localizationTarget A B B' N h)


private theorem GeometricallyRegular.regularRing
    {k T : Type*} [Field k] [CommRing T] [Algebra k T] (h : GeometricallyRegular k T) :
    RegularRing T :=
  (noetherianRegular_of_ringEquiv (Algebra.TensorProduct.lid k T).toRingEquiv
    (h.regular_tensorProduct k)).2

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem isRegularLocalRing_of_flat_of_regularClosedFiber
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hR : IsRegularLocalRing R)
    (hF : IsRegularLocalRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))) :
    IsRegularLocalRing S := by
  let R' := ULift.{v} R
  let S' := ULift.{u} S
  let eR : R' ≃+* R := ULift.ringEquiv
  let eS : S' ≃+* S := ULift.ringEquiv
  let : Algebra R' S' := ULift.algebra' R S'
  let : IsRegularLocalRing R := hR
  let hR' := IsRegularLocalRing.of_ringEquiv eR.symm
  let : IsLocalRing R' := hR'.toIsLocalRing
  let : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv R eR.symm
  let : IsLocalRing S' := eS.symm.isLocalRing
  let : IsNoetherianRing S' := isNoetherianRing_of_ringEquiv S eS.symm
  let : Module.Flat R' S' := Module.Flat.ulift_left_iff.mpr inferInstance
  have hMap : algebraMap R' S' =
      eS.symm.toRingHom.comp ((algebraMap R S).comp eR.toRingHom) := rfl
  let : IsLocalHom (algebraMap R' S') := by
    rw [hMap]
    let : IsLocalHom eR.toRingHom := isLocalHom_toRingHom eR
    let : IsLocalHom eS.symm.toRingHom := isLocalHom_toRingHom eS.symm
    infer_instance
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let I' := (IsLocalRing.maximalIdeal R').map (algebraMap R' S')
  have hI : I' = I.map eS.symm.toRingHom := by
    dsimp only [I, I']
    have hMax := IsLocalRing.map_maximalIdeal_of_surjective eR.toRingHom eR.surjective
    rw [hMap, ← Ideal.map_map, ← Ideal.map_map, hMax]
  let : IsRegularLocalRing (S ⧸ I) := hF
  have hF' : IsRegularLocalRing (S' ⧸ I') :=
    IsRegularLocalRing.of_ringEquiv (Ideal.quotientEquiv I I' eS.symm hI)
  let : IsRegularLocalRing S' :=
    isRegularLocalRing_of_flatLocal_of_regularClosedFiber R' S' hR' hF'
  exact IsRegularLocalRing.of_ringEquiv eS

set_option backward.isDefEq.respectTransparency false in
private theorem RegularMap.regularRing
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra B C]
    [IsNoetherianRing B] [IsNoetherianRing C]
    (h : RegularMap B C (algebraMap B C)) (hB : RegularRing B) : RegularRing C := by
  rw [regularMap_algebraMap_iff] at h
  let : Module.Flat B C := h.1
  intro q hq
  let p := q.comap (algebraMap B C)
  let : p.IsPrime := Ideal.IsPrime.comap _
  let e := PrimeSpectrum.preimageEquivFiber B C ⟨p, inferInstance⟩
  let qF := e ⟨⟨q, hq⟩, rfl⟩
  let r := qF.asIdeal.comap (includeRight : C →ₐ[B] p.Fiber C)
  have hr : r = q := congrArg (fun s => s.val.asIdeal) (e.symm_apply_apply ⟨⟨q, hq⟩, rfl⟩)
  let : r.IsPrime := Ideal.IsPrime.comap _
  let : r.LiesOver p := ⟨by rw [hr]⟩
  let Bp := Localization.AtPrime p
  let Cr := Localization.AtPrime r
  let : Algebra Bp Cr := Localization.AtPrime.algebraOfLiesOver p r
  let : IsLocalHom (algebraMap Bp Cr) := by
    rw [Localization.AtPrime.algebraMap_eq p r]
    infer_instance
  have hF := (h.2 p).regularRing qF.asIdeal
  let : IsRegularLocalRing (Localization.AtPrime qF.asIdeal) := hF
  let J := (IsLocalRing.maximalIdeal Bp).map (algebraMap Bp Cr)
  have hJ : J = (p.map (algebraMap B C)).map (algebraMap C Cr) := by
    dsimp only [J, Bp, Cr]
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let eF : Localization.AtPrime qF.asIdeal ≃+* Cr ⧸ J :=
    (Ideal.Fiber.algEquivAux₂ (R := B) (S := C) p qF.asIdeal).toRingEquiv.trans
      (Ideal.quotEquivOfEq hJ.symm)
  have hClosed : IsRegularLocalRing (Cr ⧸ J) :=
    IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime qF.asIdeal) eF
  let : IsRegularLocalRing Cr :=
    isRegularLocalRing_of_flat_of_regularClosedFiber Bp Cr (hB p) hClosed
  exact IsRegularLocalRing.of_ringEquiv (Localization.localRingEquiv r q (RingEquiv.refl C)
    (by change r = q.comap (RingHom.id C); rwa [Ideal.comap_id]))

private theorem isNoetherianRing_tensorLeft
    (A B L : Type*) [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    [IsNoetherianRing B] [Algebra.EssFiniteType A L] :
    IsNoetherianRing (L ⊗[A] B) := by
  let : IsNoetherianRing (B ⊗[A] L) := Algebra.EssFiniteType.isNoetherianRing B _
  exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A B L).toRingEquiv

/-- The composite of two regular homomorphisms is regular. -/
theorem RegularMap.comp : Specs.regularMap_compType.{u,v,w} := by
  intro A B C _ _ _ _ _ _ f g hf hg
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  let : IsScalarTower A B C := .of_algebraMap_eq' rfl
  change RegularMap A B (algebraMap A B) at hf
  change RegularMap B C (algebraMap B C) at hg
  change RegularMap A C (algebraMap A C)
  rw [regularMap_algebraMap_iff] at hf ⊢
  let : Module.Flat A B := hf.1
  let : Module.Flat B C := ((regularMap_algebraMap_iff B C).mp hg).1
  refine ⟨Module.Flat.trans A B C, ?_⟩
  intro p hp L _ _ _
  let : Algebra A L := Algebra.compHom L (algebraMap A p.ResidueField)
  let : IsScalarTower A p.ResidueField L := .of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType A L := .comp A p.ResidueField L
  let D := L ⊗[A] B
  let E := D ⊗[B] C
  let e := Algebra.IsPushout.cancelBaseChangeAlg A L B D C
  let : IsNoetherianRing D := isNoetherianRing_tensorLeft A B L
  let : IsNoetherianRing (L ⊗[A] C) := isNoetherianRing_tensorLeft A C L
  let : IsNoetherianRing E := isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  let : Algebra.EssFiniteType B D :=
    (Algebra.EssFiniteType.iff_of_algEquiv (commRight A B L)).mp inferInstance
  have hD : RegularRing D :=
    (noetherianRegular_of_ringEquiv (cancelBaseChange A p.ResidueField L L B).toRingEquiv
      ((hf.2 p).regular_tensorProduct L)).2
  have hE := (RegularMap.baseChange_essFiniteType B C D E hg).regularRing hD
  exact noetherianRegular_of_ringEquiv
    (e.trans (cancelBaseChange A p.ResidueField L L C).symm).toRingEquiv
    ⟨inferInstance, hE⟩

private theorem regularRing_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (hS : RegularRing S) : RegularRing R := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := p.exists_isPrime_liesOver_of_faithfullyFlat (B := S)
  let Rₚ := Localization.AtPrime p
  let Sᵩ := Localization.AtPrime q
  let : Algebra Rₚ Sᵩ := Localization.AtPrime.algebraOfLiesOver p q
  let : IsLocalHom (algebraMap Rₚ Sᵩ) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  let R' := ULift.{v} Rₚ
  let S' := ULift.{u} Sᵩ
  let eR : R' ≃+* Rₚ := ULift.ringEquiv
  let eS : S' ≃+* Sᵩ := ULift.ringEquiv
  let : Algebra R' S' := ULift.algebra' Rₚ S'
  let : IsLocalRing R' := eR.symm.isLocalRing
  let : IsLocalRing S' := eS.symm.isLocalRing
  let : IsNoetherianRing R' := isNoetherianRing_of_ringEquiv Rₚ eR.symm
  let : IsNoetherianRing S' := isNoetherianRing_of_ringEquiv Sᵩ eS.symm
  let : Module.Flat Rₚ Sᵩ := inferInstance
  let : Module.Flat R' S' := Module.Flat.ulift_left_iff.mpr inferInstance
  let : IsLocalHom (algebraMap R' S') := by
    change IsLocalHom (eS.symm.toRingHom.comp ((algebraMap Rₚ Sᵩ).comp eR.toRingHom))
    let : IsLocalHom eR.toRingHom := isLocalHom_toRingHom eR
    let : IsLocalHom eS.symm.toRingHom := isLocalHom_toRingHom eS.symm
    infer_instance
  let : IsRegularLocalRing Sᵩ := hS q
  let : IsRegularLocalRing R' :=
    isRegularLocalRing_of_flatLocal_target R' S' (IsRegularLocalRing.of_ringEquiv eS.symm)
  exact IsRegularLocalRing.of_ringEquiv eR

private theorem flat_of_faithfullyFlat_target
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] [Module.Flat A C] : Module.Flat A B := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  let i (M : Type _) [AddCommGroup M] [Module A M] :=
    TensorProduct.map (Algebra.linearMap B C |>.restrictScalars A) (LinearMap.id (R := A) (M := M))
  have hi (M : Type _) [AddCommGroup M] [Module A M] : Function.Injective (i M) := by
    let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B B C M
    have he : i M = e.toLinearMap.restrictScalars A ∘ₗ
        (TensorProduct.mk B C (B ⊗[A] M) 1).restrictScalars A := by
      ext b m
      simp [i, e, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def]
    rw [he]
    exact e.injective.comp (Module.FaithfullyFlat.tensorProduct_mk_injective (B := C) _)
  have hcomm : i P ∘ₗ f.lTensor B = f.lTensor C ∘ₗ i N := by
    ext b n
    simp [i]
  apply Function.Injective.of_comp (f := i P)
  change Function.Injective ⇑(i P ∘ₗ f.lTensor B)
  rw [hcomm]
  exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp (hi N)

/-- A regular composite descends along a faithfully flat second map. -/
theorem RegularMap.of_comp_faithfullyFlat : Specs.regularMap_of_comp_faithfullyFlatType.{u,v,w} := by
  intro A B C _ _ _ _ _ _ f g h hff
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  let : IsScalarTower A B C := .of_algebraMap_eq' rfl
  let : Module.FaithfullyFlat B C := hff
  change RegularMap A C (algebraMap A C) at h
  change RegularMap A B (algebraMap A B)
  rw [regularMap_algebraMap_iff] at h ⊢
  let : Module.Flat A C := h.1
  refine ⟨flat_of_faithfullyFlat_target A B C, ?_⟩
  intro p hp L _ _ _
  let : Algebra A L := Algebra.compHom L (algebraMap A p.ResidueField)
  let : IsScalarTower A p.ResidueField L := .of_algebraMap_eq' rfl
  let : Algebra.EssFiniteType A L := .comp A p.ResidueField L
  let D := L ⊗[A] B
  let E := D ⊗[B] C
  let e := Algebra.IsPushout.cancelBaseChangeAlg A L B D C
  let : IsNoetherianRing D := isNoetherianRing_tensorLeft A B L
  have hE := noetherianRegular_of_ringEquiv
    ((cancelBaseChange A p.ResidueField L L C).trans e.symm).toRingEquiv
    ((h.2 p).regular_tensorProduct L)
  let : IsNoetherianRing E := hE.1
  have hD : RegularRing D := regularRing_of_faithfullyFlat (R := D) (S := E) hE.2
  exact noetherianRegular_of_ringEquiv (cancelBaseChange A p.ResidueField L L B).symm.toRingEquiv
    ⟨inferInstance, hD⟩

end CommutativeAlgebraNotes.Excellence
