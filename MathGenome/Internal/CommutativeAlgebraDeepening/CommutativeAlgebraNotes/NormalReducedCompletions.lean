import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.NormalReducedCompletions
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FlatLocalRegularity
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.SerreCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure

/-! Normality and reducedness under completion for Noetherian local G-rings. -/

universe u
noncomputable section
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace CommutativeAlgebraNotes.Excellence

open IsLocalRing
open AdvCommAlg.CohenMacaulay
open AdvCommAlg.CohenMacaulay.SerreFlatTransfer
open AdvCommAlg.Normality

private theorem serreConditions_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) (i j : ℕ)
    (h : RegularInCodimension A i ∧ RingSerreCondition A j) :
    RegularInCodimension B i ∧ RingSerreCondition B j := by
  refine ⟨?_, ringSerreCondition_of_ringEquiv e j h.2⟩
  intro q hq
  let p := PrimeSpectrum.comap e.toRingHom q
  let e' := Localization.localRingEquiv p.asIdeal q.asIdeal e rfl
  have hp : p.asIdeal.height ≤ (i : ℕ∞) :=
    (e.height_comap q.asIdeal).le.trans hq
  have := h.1 p hp
  exact IsRegularLocalRing.of_ringEquiv e'

private theorem serreConditions_at_fiberPrime (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (i j : ℕ) (h : RegularInCodimension A i ∧ RingSerreCondition A j)
    (p : PrimeSpectrum A) (r : PrimeSpectrum (p.asIdeal.Fiber B))
    (hr : IsRegularLocalRing (Localization.AtPrime r.asIdeal)) :
    let q := PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B).toRingHom r
    (q.asIdeal.height ≤ (i : ℕ∞) → IsRegularLocalRing (Localization.AtPrime q.asIdeal)) ∧
      LocalSerreBound (Localization.AtPrime q.asIdeal) j := by
  let q := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B).toRingHom r
  have := fiberPrime_liesOver A B p r
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  have := localizedMap_isLocalHom A B p.asIdeal q.asIdeal
  have := localizedMap_flat A B p.asIdeal q.asIdeal
  let R := Localization.AtPrime p.asIdeal
  let S := Localization.AtPrime q.asIdeal
  let J := (maximalIdeal R).map (algebraMap R S)
  have := AdvCommAlg.CohenMacaulay.Specs.closedFiberLocalRing R S
  have := hr
  let e : Localization.AtPrime r.asIdeal ≃+* S ⧸ J := by
    simpa only [S, R, J, q] using fiberLocalEquiv A B p r
  have : IsRegularLocalRing (S ⧸ J) :=
    IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime r.asIdeal) e
  refine ⟨?_, ?_⟩
  · intro hq
    have hdim : ringKrullDim R ≤ ringKrullDim S := by
      rw [(flatLocal_ring_formulas R S).1]
      exact le_add_of_nonneg_right (ringKrullDim_nonneg_of_nontrivial (R := S ⧸ J))
    have hp : p.asIdeal.height ≤ (i : ℕ∞) := by
      change ringKrullDim (Localization.AtPrime p.asIdeal) ≤
        ringKrullDim (Localization.AtPrime q.asIdeal) at hdim
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),
        IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)] at hdim
      exact (WithBot.coe_le_coe.mp hdim).trans hq
    exact isRegularLocalRing_of_flatLocal_of_regularClosedFiber R S (h.1 p hp) inferInstance
  · have depth_eq : (IsLocalRing.depth (ModuleCat.of (S ⧸ J) (S ⧸ J)) : WithBot ℕ∞) =
        ringKrullDim (S ⧸ J) := by
      rw [← Module.supportDim_self_eq_ringKrullDim]
      exact (localCohenMacaulay_iff_depth_eq _ _).mp (regularLocal_cohenMacaulay _)
    apply localSerreBound_flatLocal_ascent R S j ((ringSerreCondition_iff A j).mp h.2 p)
    unfold LocalSerreBound
    exact (min_le_right _ _).trans depth_eq.symm.le

private theorem serreConditions_of_regularMap (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    (reg : RegularMap A B (algebraMap A B)) (i j : ℕ)
    (h : RegularInCodimension A i ∧ RingSerreCondition A j) :
    RegularInCodimension B i ∧ RingSerreCondition B j := by
  obtain ⟨flat, fibers⟩ := (regularMap_algebraMap_iff A B).mp reg
  have atPrime (q : PrimeSpectrum B) :
      (q.asIdeal.height ≤ (i : ℕ∞) → IsRegularLocalRing (Localization.AtPrime q.asIdeal)) ∧
        LocalSerreBound (Localization.AtPrime q.asIdeal) j := by
    let p := PrimeSpectrum.comap (algebraMap A B) q
    let e := PrimeSpectrum.preimageEquivFiber A B p
    let r := e ⟨q, rfl⟩
    have eq : PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B).toRingHom r = q :=
      congrArg Subtype.val (e.symm_apply_apply ⟨q, rfl⟩)
    obtain ⟨noetherianTensor, regularTensor⟩ :=
      (fibers p.asIdeal).regular_tensorProduct p.asIdeal.ResidueField
    have hr : IsRegularLocalRing (Localization.AtPrime r.asIdeal) := by
      let eT := (Algebra.TensorProduct.lid p.asIdeal.ResidueField (p.asIdeal.Fiber B)).toRingEquiv
      have := isNoetherianRing_of_ringEquiv _ eT
      have : IsRegularRing (p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) :=
        (regularRing_iff _).mp regularTensor
      have regularFiber : IsRegularRing (p.asIdeal.Fiber B) := IsRegularRing.of_ringEquiv
        (R := p.asIdeal.ResidueField ⊗[p.asIdeal.ResidueField] p.asIdeal.Fiber B) eT
      exact (regularRing_iff _).mpr regularFiber r.asIdeal
    have bound := serreConditions_at_fiberPrime A B i j h p r hr
    dsimp only at bound
    exact eq ▸ bound
  exact ⟨fun q => (atPrime q).1, (ringSerreCondition_iff B j).mpr fun q => (atPrime q).2⟩

private def quotientPowerEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {I : Ideal A} {J : Ideal B} (h : I.map e.toRingHom = J) (n : ℕ) :
    (A ⧸ I ^ n) ≃+* (B ⧸ J ^ n) :=
  Ideal.quotientEquiv (I ^ n) (J ^ n) e (by
    change J ^ n = Ideal.map e.toRingHom (I ^ n)
    rw [Ideal.map_pow, h])

private theorem quotientPowerEquiv_compatible {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {I : Ideal A} {J : Ideal B} (h : I.map e.toRingHom = J)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow J hmn).comp
      ((quotientPowerEquiv e h n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) =
    (quotientPowerEquiv e h m).toRingHom.comp (AdicCompletion.evalₐ I m).toRingHom := by
  ext1 x
  induction x using AdicCompletion.induction_on with
  | h f =>
    change Ideal.Quotient.mk (J ^ m) (e (f.val n)) =
      Ideal.Quotient.mk (J ^ m) (e (f.val m))
    apply Ideal.Quotient.eq.mpr
    rw [← map_sub, ← h, ← Ideal.map_pow]
    apply Ideal.mem_map_of_mem e.toRingHom
    have hf := Ideal.Quotient.eq.mp (AdicCompletion.AdicCauchySequence.mk_eq_mk hmn f)
    simpa only [smul_eq_mul, Ideal.mul_top] using hf

private def completionMapOfRingEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {I : Ideal A} {J : Ideal B} (h : I.map e.toRingHom = J) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (quotientPowerEquiv e h n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (quotientPowerEquiv_compatible e h)

private theorem eval_completionMapOfRingEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {I : Ideal A} {J : Ideal B} (h : I.map e.toRingHom = J)
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (completionMapOfRingEquiv e h x) =
      quotientPowerEquiv e h n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (quotientPowerEquiv_compatible e h) n x

/-- Isomorphic rings have isomorphic completions at corresponding ideals. -/
private def completionRingEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) {I : Ideal A} {J : Ideal B} (h : I.map e.toRingHom = J) :
    AdicCompletion I A ≃+* AdicCompletion J B := by
  have h' : J.map e.symm.toRingHom = I := by
    have hinv : e.symm.toRingHom.comp e.toRingHom = RingHom.id A :=
      RingHom.ext e.symm_apply_apply
    rw [← h, Ideal.map_map, hinv, Ideal.map_id]
  have hsymm (n : ℕ) : quotientPowerEquiv e.symm h' n = (quotientPowerEquiv e h n).symm := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  refine { completionMapOfRingEquiv e h with
    invFun := completionMapOfRingEquiv e.symm h'
    left_inv := fun x => AdicCompletion.ext_evalₐ fun n => ?_
    right_inv := fun x => AdicCompletion.ext_evalₐ fun n => ?_ }
  · change AdicCompletion.evalₐ I n
      (completionMapOfRingEquiv e.symm h' (completionMapOfRingEquiv e h x)) = _
    rw [eval_completionMapOfRingEquiv, eval_completionMapOfRingEquiv, hsymm,
      RingEquiv.symm_apply_apply]
  · change AdicCompletion.evalₐ J n
      (completionMapOfRingEquiv e h (completionMapOfRingEquiv e.symm h' x)) = _
    rw [eval_completionMapOfRingEquiv, eval_completionMapOfRingEquiv, hsymm,
      RingEquiv.apply_symm_apply]

private theorem serreConditions_of_gRingCompletion (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hG : IsGRing A) (i j : ℕ)
    (h : RegularInCodimension A i ∧ RingSerreCondition A j) :
    letI := P103.Ch07.CompletedNoetherian.completed_noetherian A (maximalIdeal A)
    RegularInCodimension (AdicCompletion (maximalIdeal A) A) i ∧
      RingSerreCondition (AdicCompletion (maximalIdeal A) A) j := by
  let m := maximalIdeal A
  let R := Localization.AtPrime m
  let B := AdicCompletion (maximalIdeal R) R
  have := P103.Ch07.CompletedNoetherian.completed_noetherian R (maximalIdeal R)
  have := P103.Ch07.CompletedNoetherian.completed_noetherian A m
  let e : A ≃+* R :=
    (IsLocalization.atUnits A m.primeCompl (S := R) fun _ hx => notMem_maximalIdeal.mp hx).toRingEquiv
  let eHat : AdicCompletion m A ≃+* B := completionRingEquiv e (map_ringEquiv_maximalIdeal e)
  have reg : RegularMap R B (algebraMap R B) := hG m
  exact serreConditions_of_ringEquiv eHat.symm i j
    (serreConditions_of_regularMap R B reg i j (serreConditions_of_ringEquiv e i j h))

/-- Normality ascends to the maximal-ideal completion of a Noetherian local G-ring. -/
theorem normalCompletion (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hG : IsGRing A) (hA : IsNormal A) :
    letI := P103.Ch07.CompletedNoetherian.completed_noetherian A (maximalIdeal A)
    IsNormal (AdicCompletion (maximalIdeal A) A) := by
  have := P103.Ch07.CompletedNoetherian.completed_noetherian A (maximalIdeal A)
  exact (serreCriterion _).mpr
    (serreConditions_of_gRingCompletion A hG 1 2 ((serreCriterion A).mp hA))

/-- Reducedness ascends to the maximal-ideal completion of a Noetherian local G-ring. -/
theorem reducedCompletion (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hG : IsGRing A) (hA : IsReduced A) :
    IsReduced (AdicCompletion (maximalIdeal A) A) := by
  have := P103.Ch07.CompletedNoetherian.completed_noetherian A (maximalIdeal A)
  exact (isReduced_iff_regularInCodimension_zero_and_serreCondition_one _).mpr
    (serreConditions_of_gRingCompletion A hG 0 1
      ((isReduced_iff_regularInCodimension_zero_and_serreCondition_one A).mp hA))

end CommutativeAlgebraNotes.Excellence
