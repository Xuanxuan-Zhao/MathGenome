import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FormalPowerSeriesExtension
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

universe u
open scoped TensorProduct
open TensorProduct
noncomputable section
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
namespace AdvCommAlg.CohenMacaulay

/- Helpers use the module namespace so this file can be imported together
with the independently proved polynomial-extension module. -/

theorem formalPowerSeries_noetherian : Specs.formalPowerSeries_noetherianType.{u} := by
  intro R _ _ n
  infer_instance

/-- Flatness comes from polynomial freeness followed by adic completion. -/
lemma FormalPowerSeriesExtension.mvPowerSeries_flat (R : Type u) [CommRing R] [IsNoetherianRing R]
    (σ : Type) [Finite σ] : Module.Flat R (MvPowerSeries σ R) := by
  let P := MvPolynomial σ R
  let I := MvPolynomial.idealOfVars σ R
  let A := AdicCompletion I P
  letI : Module.Flat R A := Module.Flat.trans R P A
  exact Module.Flat.of_linearEquiv
    ((MvPowerSeries.toAdicCompletionAlgEquiv σ R).restrictScalars R).toLinearEquiv

theorem formalPowerSeries_flat : Specs.formalPowerSeries_flatType.{u} := by
  intro R _ _ n
  exact FormalPowerSeriesExtension.mvPowerSeries_flat R (Fin n)

theorem powerSeries_X_mem_maximal : Specs.powerSeries_X_mem_maximalType.{u} := by
  intro R _ q _
  have hX : (PowerSeries.X : PowerSeries R) ∈ Ideal.jacobson (⊥ : Ideal (PowerSeries R)) := by
    rw [Ideal.mem_jacobson_bot]
    intro y
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp
  exact (sInf_le (show (⊥ : Ideal (PowerSeries R)) ≤ q ∧ q.IsMaximal from
    ⟨bot_le, inferInstance⟩) : Ideal.jacobson ⊥ ≤ q) hX

theorem powerSeries_maximal_lift : Specs.powerSeries_maximal_liftType.{u} := by
  intro R _ m _
  exact Ideal.comap_isMaximal_of_surjective PowerSeries.constantCoeff
    PowerSeries.constantCoeff_surj

/-- Every maximal ideal is the inverse image of its constant-coefficient
ideal. Invertibility of series with unit constant coefficient is used above. -/
theorem powerSeries_maximal_correspondence :
    Specs.powerSeries_maximal_correspondenceType.{u} := by
  intro R _ q _
  have hX := powerSeries_X_mem_maximal R q
  have hq : q = (q.comap PowerSeries.C).comap PowerSeries.constantCoeff := by
    ext f
    change f ∈ q ↔ PowerSeries.C (PowerSeries.constantCoeff f) ∈ q
    have hs : f - PowerSeries.C (PowerSeries.constantCoeff f) ∈ q := by
      rw [PowerSeries.sub_const_eq_X_mul_shift]
      exact q.mul_mem_right _ hX
    exact ⟨fun hf => by simpa only [sub_sub_cancel] using q.sub_mem hf hs,
      fun hf => by simpa only [sub_add_cancel] using q.add_mem hs hf⟩
  refine ⟨?_, hq⟩
  have hk : RingHom.ker (PowerSeries.constantCoeff (R := R)) ≤ q := by
    rw [hq]
    exact Ideal.comap_mono bot_le
  have hm := Ideal.IsMaximal.map_of_surjective_of_ker_le
    PowerSeries.constantCoeff_surj hk
  have heq : q.map PowerSeries.constantCoeff = q.comap PowerSeries.C := by
    nth_rw 1 [hq]
    exact Ideal.map_comap_of_surjective _ PowerSeries.constantCoeff_surj _
  exact heq ▸ hm

theorem powerSeries_quotient_equiv : Specs.powerSeries_quotient_equivType.{u} := by
  intro R _ _ I
  let f := PowerSeries.map (Ideal.Quotient.mk I)
  have hf : Function.Surjective f :=
    PowerSeries.map_surjective _ Ideal.Quotient.mk_surjective
  have hk : RingHom.ker f = I.map PowerSeries.C := by
    change RingHom.ker (MvPowerSeries.map (σ := Unit) (Ideal.Quotient.mk I)) =
      Ideal.map (MvPowerSeries.C (σ := Unit)) I
    rw [MvPowerSeries.ker_map_of_fg _ (RingHom.ker (Ideal.Quotient.mk I)).fg_of_isNoetherianRing,
      Ideal.mk_ker]
  let e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hf)
  refine ⟨e, ?_⟩
  intro g
  simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- Localization adds no fractions to the fiber: all its denominators
already have invertible nonzero constant coefficients. -/
theorem powerSeries_local_fiber_equiv : Specs.powerSeries_local_fiber_equivType.{u} := by
  intro R _ _ m _
  let S := PowerSeries R
  let q := m.comap (PowerSeries.constantCoeff : S →+* R)
  letI : q.IsMaximal := powerSeries_maximal_lift R m
  let B := Localization.AtPrime q
  let I := m.map PowerSeries.C
  let J := I.map (algebraMap S B)
  let D := S ⧸ I
  let E := B ⧸ J
  let T := Algebra.algebraMapSubmonoid D q.primeCompl
  obtain ⟨e, he⟩ := powerSeries_quotient_equiv R m
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hT : T ≤ IsUnit.submonoid D := by
    rintro x ⟨f, hf, rfl⟩
    have hu : IsUnit (e (Ideal.Quotient.mk I f)) := by
      rw [he, PowerSeries.isUnit_iff_constantCoeff]
      apply Ne.isUnit
      change Ideal.Quotient.mk m (PowerSeries.constantCoeff f) ≠ 0
      exact Ideal.Quotient.eq_zero_iff_mem.not.mpr hf
    have hu' := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (e (Ideal.Quotient.mk I f))) at hu'
    change IsUnit (Ideal.Quotient.mk I f)
    simpa only [e.symm_apply_apply] using hu'
  let a : D ≃ₐ[D] E := IsLocalization.atUnits D T (S := E) hT
  refine ⟨a.symm.toRingEquiv.trans e, ?_⟩
  intro f
  change e (a.symm (a (Ideal.Quotient.mk I f))) = _
  rw [a.symm_apply_apply, he]

/-- Changing coefficients by a ring isomorphism changes the series ring
by the corresponding coefficientwise ring isomorphism. -/
def FormalPowerSeriesExtension.powerSeries_mapRingEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    PowerSeries R ≃+* PowerSeries S where
  __ := PowerSeries.map e.toRingHom
  invFun := PowerSeries.map e.symm.toRingHom
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp

theorem powerSeries_residueField_fiber_equiv :
    Specs.powerSeries_residueField_fiber_equivType.{u} := by
  intro R _ _ m _
  obtain ⟨e, _⟩ := powerSeries_local_fiber_equiv R m
  let k : (R ⧸ m) ≃+* m.ResidueField := RingEquiv.ofBijective
    (algebraMap (R ⧸ m) m.ResidueField) m.bijective_algebraMap_quotient_residueField
  exact ⟨e.trans (FormalPowerSeriesExtension.powerSeries_mapRingEquiv k)⟩

/-- The parameter X has depth and dimension one over a field. -/
theorem powerSeries_field_cohenMacaulay : Specs.powerSeries_field_cohenMacaulayType.{u} := by
  intro K _
  let S := PowerSeries K
  have hmem : ∀ x ∈ [PowerSeries.X (R := K)], x ∈ IsLocalRing.maximalIdeal S := by
    intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact powerSeries_X_mem_maximal K _
  have hreg : RingTheory.Sequence.IsRegular S [PowerSeries.X] :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      ((RingTheory.Sequence.isWeaklyRegular_singleton_iff S _).mpr
        (IsSMulRegular.of_ne_zero PowerSeries.X_ne_zero))
  have hd : (1 : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of S S) := by
    rw [IsLocalRing.depth_eq_sSup_length_isRegular]
    exact le_sSup ⟨[PowerSeries.X], hreg, hmem, rfl⟩
  apply (localCohenMacaulay_self_iff S).mpr
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one S]
  apply le_antisymm
  · have hb := Depth.depth_le_supportDim (R := S) S
    rw [Depth.depth_eq_libraryDepth (ModuleCat.of S S),
      Module.supportDim_self_eq_ringKrullDim,
      IsDiscreteValuationRing.ringKrullDim_eq_one S] at hb
    exact hb
  · exact WithBot.coe_le_coe.mpr hd

lemma FormalPowerSeriesExtension.localCohenMacaulay_self_iff_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : LocalCohenMacaulay R R ↔ LocalCohenMacaulay S S := by
  exact localCohenMacaulay_iff_of_semilinearEquiv R e e.toSemilinearEquiv

/-- One-variable local ascent and descent for rings, with the actual
coefficient quotient as the closed fiber. -/
lemma FormalPowerSeriesExtension.powerSeries_local_ring_cohenMacaulay (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    LocalCohenMacaulay (PowerSeries R) (PowerSeries R) ↔ LocalCohenMacaulay R R := by
  let S := PowerSeries R
  letI : IsLocalHom (algebraMap R S) := ⟨fun r hr => by
    change IsUnit (PowerSeries.C r) at hr
    simpa only [PowerSeries.constantCoeff_C] using
      hr.map (PowerSeries.constantCoeff : S →+* R)⟩
  letI : Module.Flat R S := FormalPowerSeriesExtension.mvPowerSeries_flat R Unit
  let m := IsLocalRing.maximalIdeal R
  let J := m.map (algebraMap R S)
  letI : IsLocalRing (S ⧸ J) := Specs.closedFiberLocalRing R S
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  obtain ⟨e, _⟩ := powerSeries_quotient_equiv R m
  have hf : LocalCohenMacaulay (S ⧸ J) (S ⧸ J) :=
    (FormalPowerSeriesExtension.localCohenMacaulay_self_iff_of_ringEquiv (R := S ⧸ J) e).mpr (powerSeries_field_cohenMacaulay (R ⧸ m))
  exact (flatLocal_ring_cohenMacaulay R S).trans (and_iff_left hf)

lemma FormalPowerSeriesExtension.field_localCohenMacaulay (K : Type u) [Field K] : LocalCohenMacaulay K K := by
  apply (localCohenMacaulay_self_iff K).mpr
  rw [ringKrullDim_eq_zero_of_field]
  have hb := Depth.depth_le_supportDim (R := K) K
  rw [Depth.depth_eq_libraryDepth (ModuleCat.of K K),
    Module.supportDim_self_eq_ringKrullDim, ringKrullDim_eq_zero_of_field] at hb
  exact le_antisymm hb (WithBot.coe_le_coe.mpr zero_le)

lemma FormalPowerSeriesExtension.mvPowerSeries_field_cohenMacaulay (K : Type u) [Field K] (n : ℕ) :
    LocalCohenMacaulay (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K) := by
  induction n with
  | zero =>
    exact (FormalPowerSeriesExtension.localCohenMacaulay_self_iff_of_ringEquiv
      (MvPowerSeries.isEmptyEquiv (Fin 0) K).toRingEquiv).mpr (FormalPowerSeriesExtension.field_localCohenMacaulay K)
  | succ n ih =>
    apply (FormalPowerSeriesExtension.localCohenMacaulay_self_iff_of_ringEquiv
      (MvPowerSeries.finSuccEquiv K n).toRingEquiv).mpr
    exact (FormalPowerSeriesExtension.powerSeries_local_ring_cohenMacaulay (MvPowerSeries (Fin n) K)).mpr ih

lemma FormalPowerSeriesExtension.mvPowerSeries_maximal_correspondence (R : Type u) [CommRing R] (n : ℕ)
    (q : Ideal (MvPowerSeries (Fin n) R)) [q.IsMaximal] :
    (q.comap MvPowerSeries.C).IsMaximal ∧
      q = (q.comap MvPowerSeries.C).comap MvPowerSeries.constantCoeff := by
  let S := MvPowerSeries (Fin n) R
  let cc : S →+* R := MvPowerSeries.constantCoeff
  have hcc : Function.Surjective cc := fun r => ⟨MvPowerSeries.C r, MvPowerSeries.constantCoeff_C r⟩
  have hk : RingHom.ker cc ≤ q := by
    intro f hf
    have hj : f ∈ Ideal.jacobson (⊥ : Ideal S) := by
      rw [Ideal.mem_jacobson_bot]
      intro g
      apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
      change IsUnit (cc (f * g + 1))
      change cc f = 0 at hf
      simpa only [map_add, map_mul, hf, zero_mul, map_one, zero_add] using (isUnit_one : IsUnit (1 : R))
    exact (sInf_le ⟨bot_le, (inferInstance : q.IsMaximal)⟩ : Ideal.jacobson ⊥ ≤ q) hj
  have hq : (q.map cc).comap cc = q := by
    rw [Ideal.comap_map_of_surjective cc hcc, ← RingHom.ker_eq_comap_bot,
      sup_of_le_left hk]
  have hm : (q.map cc).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hcc hk
  have hbase : q.comap MvPowerSeries.C = q.map cc := by
    nth_rw 1 [← hq]
    ext r
    change cc (MvPowerSeries.C r) ∈ q.map cc ↔ r ∈ q.map cc
    rw [show cc (MvPowerSeries.C r) = r from MvPowerSeries.constantCoeff_C r]
  exact ⟨hbase.symm ▸ hm, hq.symm.trans (congrArg (Ideal.comap cc) hbase.symm)⟩

lemma FormalPowerSeriesExtension.mvPowerSeries_quotient_equiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) (I : Ideal R) :
    ∃ e : (MvPowerSeries (Fin n) R ⧸ I.map MvPowerSeries.C) ≃+*
        MvPowerSeries (Fin n) (R ⧸ I),
      ∀ f, e (Ideal.Quotient.mk (I.map MvPowerSeries.C) f) =
        MvPowerSeries.map (Ideal.Quotient.mk I) f := by
  let f := MvPowerSeries.map (σ := Fin n) (Ideal.Quotient.mk I)
  have hf : Function.Surjective f := by
    intro g
    choose a ha using fun d => Ideal.Quotient.mk_surjective (MvPowerSeries.coeff d g)
    exact ⟨a, MvPowerSeries.ext ha⟩
  have hk : RingHom.ker f = I.map MvPowerSeries.C := by
    rw [MvPowerSeries.ker_map_of_fg _ (RingHom.ker (Ideal.Quotient.mk I)).fg_of_isNoetherianRing,
      Ideal.mk_ker]
  let e := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hf)
  refine ⟨e, ?_⟩
  intro g
  simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

lemma FormalPowerSeriesExtension.mvPowerSeries_local_fiber_equiv (R : Type u) [CommRing R] [IsNoetherianRing R]
    (n : ℕ) (q : Ideal (MvPowerSeries (Fin n) R)) [q.IsMaximal] :
    let m := q.comap MvPowerSeries.C
    let B := Localization.AtPrime q
    let J := (m.map MvPowerSeries.C).map (algebraMap (MvPowerSeries (Fin n) R) B)
    ∃ e : (B ⧸ J) ≃+* MvPowerSeries (Fin n) (R ⧸ m),
      ∀ f, e (Ideal.Quotient.mk J (algebraMap (MvPowerSeries (Fin n) R) B f)) =
        MvPowerSeries.map (Ideal.Quotient.mk m) f := by
  let S := MvPowerSeries (Fin n) R
  let m := q.comap (MvPowerSeries.C : R →+* S)
  have hm := FormalPowerSeriesExtension.mvPowerSeries_maximal_correspondence R n q
  letI : m.IsMaximal := hm.1
  let B := Localization.AtPrime q
  let I : Ideal S := m.map MvPowerSeries.C
  let J := I.map (algebraMap S B)
  let D := S ⧸ I
  let E := B ⧸ J
  let T := Algebra.algebraMapSubmonoid D q.primeCompl
  obtain ⟨e, he⟩ := FormalPowerSeriesExtension.mvPowerSeries_quotient_equiv R n m
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hT : T ≤ IsUnit.submonoid D := by
    rintro x ⟨f, hf, rfl⟩
    have hu : IsUnit (e (Ideal.Quotient.mk I f)) := by
      rw [he, MvPowerSeries.isUnit_iff_constantCoeff]
      apply Ne.isUnit
      change Ideal.Quotient.mk m (MvPowerSeries.constantCoeff f) ≠ 0
      apply Ideal.Quotient.eq_zero_iff_mem.not.mpr
      change f ∉ q at hf
      rw [hm.2] at hf
      exact hf
    have hu' := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (e (Ideal.Quotient.mk I f))) at hu'
    change IsUnit (Ideal.Quotient.mk I f)
    simpa only [e.symm_apply_apply] using hu'
  let a : D ≃ₐ[D] E := IsLocalization.atUnits D T (S := E) hT
  refine ⟨a.symm.toRingEquiv.trans e, ?_⟩
  intro f
  change e (a.symm (a (Ideal.Quotient.mk I f))) = _
  rw [a.symm_apply_apply, he]

lemma FormalPowerSeriesExtension.isCohenMacaulay_iff_of_linearEquiv {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (e : M ≃ₗ[R] N) :
    IsCohenMacaulay R M ↔ IsCohenMacaulay R N := by
  rw [isCohenMacaulay_iff_maximal, isCohenMacaulay_iff_maximal]
  refine forall_congr' fun q => forall_congr' fun _ => ?_
  let f := LocalizedModule.mkLinearMap q.primeCompl M
  let g := (LocalizedModule.mkLinearMap q.primeCompl N).comp e.toLinearMap
  let a := IsLocalizedModule.linearEquiv q.primeCompl f g
  let b := a.extendScalarsOfIsLocalization q.primeCompl (Localization.AtPrime q)
  exact localCohenMacaulay_iff_of_linearEquiv b

section GlobalBaseChange
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The localized extended module has the expected two equivalent tensor
presentations. All equivalences are linear over the target local ring. -/
def FormalPowerSeriesExtension.localized_baseChange_equiv (q : Ideal S) [q.IsPrime] :
    let p := q.comap (algebraMap R S)
    letI := Localization.AtPrime.algebraOfLiesOver p q
    LocalizedModule.AtPrime q (S ⊗[R] M) ≃ₗ[Localization.AtPrime q]
      ((Localization.AtPrime q) ⊗[Localization.AtPrime p] (LocalizedModule.AtPrime p M)) := by
  let p := q.comap (algebraMap R S)
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  exact LocalizedModule.equivTensorProduct q.primeCompl (S ⊗[R] M) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange R S B B M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange R A B B M).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (LocalizedModule.equivTensorProduct p.primeCompl M).symm

/-- Local scalar extension criterion, with the zero localized module included. -/
lemma FormalPowerSeriesExtension.localized_baseChange_cohenMacaulay_iff [Module.Flat R S]
    (q : Ideal S) [q.IsPrime]
    (hf : let p := q.comap (algebraMap R S)
      letI := Localization.AtPrime.algebraOfLiesOver p q
      let A := Localization.AtPrime p
      let B := Localization.AtPrime q
      let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
      letI : IsLocalHom (algebraMap A B) := by
        rw [Localization.AtPrime.algebraMap_eq p q]
        exact Localization.isLocalHom_localRingHom p q _ _
      letI := Specs.closedFiberLocalRing A B
      LocalCohenMacaulay (B ⧸ J) (B ⧸ J)) :
    letI : Module.Finite S (S ⊗[R] M) := tensor_finite_left R S M S
    LocalCohenMacaulay (Localization.AtPrime q)
      (LocalizedModule.AtPrime q (S ⊗[R] M)) ↔
      LocalCohenMacaulay (Localization.AtPrime (q.comap (algebraMap R S)))
        (LocalizedModule.AtPrime (q.comap (algebraMap R S)) M) := by
  let p := q.comap (algebraMap R S)
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  let U := LocalizedModule.AtPrime p M
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI : IsLocalHom (algebraMap A B) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    exact Localization.isLocalHom_localRingHom p q _ _
  letI := Specs.closedFiberLocalRing A B
  letI : Module.Finite S (S ⊗[R] M) := tensor_finite_left R S M S
  letI := RegularSequence.Specs.rightTensorModule (R := A) (S := B) U B
  letI := Specs.rightTensorFinite A B U B
  let e := FormalPowerSeriesExtension.localized_baseChange_equiv R S M q ≪≫ₗ
    (RegularSequence.rightTensorComm (S := B) U B).symm
  rw [localCohenMacaulay_iff_of_linearEquiv e]
  rcases subsingleton_or_nontrivial U with hU | hU
  · letI := hU
    exact iff_of_true (localCohenMacaulay_of_subsingleton B (U ⊗[A] B))
      (localCohenMacaulay_of_subsingleton A U)
  · letI := hU
    let F := B ⧸ (J • (⊤ : Submodule B B))
    letI : Module.Finite (B ⧸ J) F := Module.Finite.of_restrictScalars_finite B (B ⧸ J) F
    have hf' : LocalCohenMacaulay (B ⧸ J) F :=
      (localCohenMacaulay_iff_of_linearEquiv (quotientSelfEquiv B J)).mpr hf
    exact (flatLocal_tensor_cohenMacaulay A B U B).trans (and_iff_left hf')

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- The localized base maximal ideal has the same extension as the original
prime ideal. This identifies the closed fiber used by CM-10. -/
lemma FormalPowerSeriesExtension.localized_baseChange_fiberIdeal (q : Ideal S) [q.IsPrime] :
    let p := q.comap (algebraMap R S)
    letI := Localization.AtPrime.algebraOfLiesOver p q
    let A := Localization.AtPrime p
    let B := Localization.AtPrime q
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (p.map (algebraMap R S)).map (algebraMap S B) := by
  let p := q.comap (algebraMap R S)
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  change (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
    (p.map (algebraMap R S)).map (algebraMap S B)
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p),
    Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq]

end GlobalBaseChange

lemma FormalPowerSeriesExtension.mvPowerSeries_localized_fiber_cohenMacaulay (R : Type u) [CommRing R]
    [IsNoetherianRing R] (n : ℕ)
    (q : Ideal (MvPowerSeries (Fin n) R)) [q.IsMaximal] :
    let S := MvPowerSeries (Fin n) R
    let p := q.comap (algebraMap R S)
    letI := Localization.AtPrime.algebraOfLiesOver p q
    let A := Localization.AtPrime p
    let B := Localization.AtPrime q
    let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
    letI : IsLocalHom (algebraMap A B) := by
      rw [Localization.AtPrime.algebraMap_eq p q]
      exact Localization.isLocalHom_localRingHom p q _ _
    letI := Specs.closedFiberLocalRing A B
    LocalCohenMacaulay (B ⧸ J) (B ⧸ J) := by
  let S := MvPowerSeries (Fin n) R
  let p := q.comap (algebraMap R S)
  letI := Localization.AtPrime.algebraOfLiesOver p q
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  letI : IsLocalHom (algebraMap A B) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    exact Localization.isLocalHom_localRingHom p q _ _
  letI := Specs.closedFiberLocalRing A B
  letI : p.IsMaximal := (FormalPowerSeriesExtension.mvPowerSeries_maximal_correspondence R n q).1
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  obtain ⟨e, _⟩ := FormalPowerSeriesExtension.mvPowerSeries_local_fiber_equiv R n q
  have hJ := FormalPowerSeriesExtension.localized_baseChange_fiberIdeal R S q
  let a := (Ideal.quotEquivOfEq hJ).trans e
  exact (FormalPowerSeriesExtension.localCohenMacaulay_self_iff_of_ringEquiv (R := B ⧸ J) a).mpr
    (FormalPowerSeriesExtension.mvPowerSeries_field_cohenMacaulay (R ⧸ p) n)

/-- Changing only the presentation of the prime ideal changes neither
its local ring nor its localized module. -/
lemma FormalPowerSeriesExtension.localCohenMacaulay_congr_primeIdeal (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (h : p = q) :
    LocalCohenMacaulay (Localization.AtPrime p) (LocalizedModule.AtPrime p M) ↔
      LocalCohenMacaulay (Localization.AtPrime q) (LocalizedModule.AtPrime q M) := by
  subst q
  rfl

/-- Maximal ideals of the series ring and of the base correspond, and at
such a pair CM-10 applies to the localized scalar extension. -/
lemma FormalPowerSeriesExtension.mvPowerSeries_tensor_left_cohenMacaulay (R : Type u) [CommRing R]
    [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (n : ℕ) :
    let S := MvPowerSeries (Fin n) R
    letI : Module.Finite S (S ⊗[R] M) := tensor_finite_left R S M S
    IsCohenMacaulay S (S ⊗[R] M) ↔ IsCohenMacaulay R M := by
  let S := MvPowerSeries (Fin n) R
  letI : Module.Flat R S := formalPowerSeries_flat R n
  letI : Module.Finite S (S ⊗[R] M) := tensor_finite_left R S M S
  change IsCohenMacaulay S (S ⊗[R] M) ↔ IsCohenMacaulay R M
  rw [isCohenMacaulay_iff_maximal, isCohenMacaulay_iff_maximal]
  constructor
  · intro h m hm
    let q := m.comap (MvPowerSeries.constantCoeff : S →+* R)
    letI : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _
      (fun r => ⟨MvPowerSeries.C r, MvPowerSeries.constantCoeff_C r⟩)
    have hp : q.comap (algebraMap R S) = m := by
      ext r
      change MvPowerSeries.constantCoeff (MvPowerSeries.C r) ∈ m ↔ r ∈ m
      rw [MvPowerSeries.constantCoeff_C]
    have ht := (FormalPowerSeriesExtension.localized_baseChange_cohenMacaulay_iff R S M q
      (FormalPowerSeriesExtension.mvPowerSeries_localized_fiber_cohenMacaulay R n q)).mp (h q)
    exact (FormalPowerSeriesExtension.localCohenMacaulay_congr_primeIdeal R M _ _ hp).mp ht
  · intro h q hq
    letI : (q.comap (algebraMap R S)).IsMaximal :=
      (FormalPowerSeriesExtension.mvPowerSeries_maximal_correspondence R n q).1
    exact (FormalPowerSeriesExtension.localized_baseChange_cohenMacaulay_iff R S M q
      (FormalPowerSeriesExtension.mvPowerSeries_localized_fiber_cohenMacaulay R n q)).mpr (h _)

/-- CM-15 for arbitrary Noetherian base rings, all finite modules, and every
finite number of formal variables, with the source's tensor order. -/
theorem formalPowerSeries_cohenMacaulay : Specs.formalPowerSeries_cohenMacaulayType.{u} := by
  intro R _ _ M _ _ _ n
  let S := MvPowerSeries (Fin n) R
  letI := RegularSequence.Specs.rightTensorModule (R := R) (S := S) M S
  letI := Specs.rightTensorFinite R S M S
  letI : Module.Finite S (S ⊗[R] M) := tensor_finite_left R S M S
  change IsCohenMacaulay S (M ⊗[R] S) ↔ IsCohenMacaulay R M
  exact (FormalPowerSeriesExtension.isCohenMacaulay_iff_of_linearEquiv
    (RegularSequence.rightTensorComm (S := S) M S)).trans
      (FormalPowerSeriesExtension.mvPowerSeries_tensor_left_cohenMacaulay R M n)

end AdvCommAlg.CohenMacaulay
