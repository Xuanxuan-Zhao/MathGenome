import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivationHypersurface
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivationsOfNonPowers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAlgebraCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteDomainModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SeparableInseparableTower
import Mathlib.RingTheory.PolynomialAlgebra

namespace CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants

open scoped TensorProduct Polynomial
open IsLocalRing Polynomial IntermediateField
open Algebra.TensorProduct
open CommutativeAlgebraNotes.Excellence
open _root_.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants

universe u

noncomputable section

set_option linter.style.haveILetI false

private theorem regular_of_localization {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (W : Submonoid R) [IsLocalization W T] [IsRegularRing R] :
    IsRegularRing T := by
  letI : IsNoetherianRing T := IsLocalization.isNoetherianRing W T inferInstance
  refine (isRegularRing_iff (R := T)).2 fun q hq => ?_
  let p := q.comap (algebraMap R T)
  letI : p.IsPrime := hq.comap _
  letI : IsLocalization p.primeCompl (Localization.AtPrime q) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization W _ q
  exact IsRegularLocalRing.of_ringEquiv (Localization.algEquiv p.primeCompl
    (Localization.AtPrime q)).toRingEquiv

private theorem regular_genericConstantsFibre {S : Type u} [CommRing S] [IsDomain S]
    [IsRegularLocalRing S] (P : Ideal S[X]) [P.IsPrime] :
    IsRegularRing (GenericConstantsFibre P) := by
  letI : IsRegularRing S := (regularRing_iff S).mp
    (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime S)
  letI : IsRegularLocalRing (Localization.AtPrime P) := inferInstance
  let C := CompletedPolynomialStalk P
  letI : IsRegularLocalRing C := regularLocalRing_completion _ inferInstance
  letI : IsRegularRing C := (regularRing_iff C).mp
    (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime C)
  letI : Algebra C (FractionRing S ⊗[S] C) := rightAlgebra
  exact regular_of_localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors S))

private theorem regular_separable_tensor {K M A : Type*} [Field K] [Field M] [CommRing A]
    [Algebra K M] [Algebra K A] [Module.Finite K M] [Algebra.IsSeparable K M]
    [IsRegularRing A] : IsRegularRing (M ⊗[K] A) := by
  letI : Algebra A (M ⊗[K] A) := rightAlgebra
  let e := Algebra.IsPushout.equiv K A M (M ⊗[K] A)
  letI : Module.Finite A (M ⊗[K] A) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  letI : IsNoetherianRing (M ⊗[K] A) := IsNoetherianRing.of_finite A _
  exact (regularRing_iff _).mp
    (regularRing_separableScalarExtension K M A ((regularRing_iff A).mpr inferInstance))

private theorem geometricallyRegular_of_charZero {K A : Type u}
    [Field K] [CharZero K] [CommRing A] [Algebra K A] [IsRegularRing A] :
    GeometricallyRegular K A := by
  intro M _ _ _
  letI : Algebra.IsSeparable K M := finiteExtension_isSeparable_of_charZero K M
  letI := regular_separable_tensor (K := K) (M := M) (A := A)
  exact ⟨inferInstance, (regularRing_iff _).mpr inferInstance⟩

private theorem exists_derivation_over_powerSeries
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ)
    (B M : Type u) [CommRing B] [IsDomain B] [Field M]
    [Algebra (MvPowerSeries (Fin r) k) B] [Module.Finite (MvPowerSeries (Fin r) k) B]
    [Algebra B M] [IsFractionRing B M]
    [Algebra (MvPowerSeries (Fin r) k) M] [IsScalarTower (MvPowerSeries (Fin r) k) B M]
    [Algebra (FractionRing (MvPowerSeries (Fin r) k)) M]
    [IsScalarTower (MvPowerSeries (Fin r) k) (FractionRing (MvPowerSeries (Fin r) k)) M]
    [Module.Finite (FractionRing (MvPowerSeries (Fin r) k)) M] (f : B)
    (hf : ¬ ∃ x : M, x ^ p = algebraMap B M f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := by
  -- Specialize the coefficient tower to zero polynomial variables.
  let S := MvPowerSeries (Fin r) k
  let S' := CoefficientTowerBase k r 0
  let e : S' ≃+* S := MvPolynomial.isEmptyRingEquiv S (Fin 0)
  letI : Algebra S' B := ((algebraMap S B).comp e.toRingHom).toAlgebra
  letI : Algebra S' S := e.toRingHom.toAlgebra
  letI : IsScalarTower S' S B := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite S' S := RingHom.Finite.of_surjective e.toRingHom e.surjective
  letI : Module.Finite S' B := Module.Finite.trans S B
  have hSB : Function.Injective (algebraMap S' B) := by
    change Function.Injective ((algebraMap S B).comp e.toRingHom)
    apply Function.Injective.comp _ e.injective
    have hSM : Function.Injective (algebraMap S M) := by
      rw [IsScalarTower.algebraMap_eq S (FractionRing S) M]
      exact (algebraMap (FractionRing S) M).injective.comp (IsFractionRing.injective S _)
    rw [IsScalarTower.algebraMap_eq S B M] at hSM
    exact hSM.of_comp (f := algebraMap B M)
  let eK : FractionRing S' ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv e
  letI : Algebra (FractionRing S') M :=
    (IsFractionRing.lift (K := FractionRing S')
      (g := (algebraMap B M).comp (algebraMap S' B))
      ((IsFractionRing.injective B M).comp hSB)).toAlgebra
  letI : Algebra (FractionRing S') (FractionRing S) := eK.toRingHom.toAlgebra
  letI : IsScalarTower (FractionRing S') (FractionRing S) M := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsFractionRing.ringHom_ext (A := S')
    intro a
    change IsFractionRing.lift (K := FractionRing S')
        (g := (algebraMap B M).comp (algebraMap S' B))
        ((IsFractionRing.injective B M).comp hSB)
        (algebraMap S' (FractionRing S') a) =
      algebraMap (FractionRing S) M (eK (algebraMap S' (FractionRing S') a))
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    change algebraMap B M (algebraMap S B (e a)) =
      algebraMap (FractionRing S) M (algebraMap S (FractionRing S) (e a))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  letI : Module.Finite (FractionRing S') (FractionRing S) :=
    RingHom.Finite.of_surjective eK.toRingHom eK.surjective
  letI : Module.Finite (FractionRing S') M :=
    Module.Finite.trans (FractionRing S) M
  exact exists_derivation_ne_zero_of_not_pth_power k p r 0 B hSB M f hf

set_option backward.isDefEq.respectTransparency false in
attribute [local instance 2000] Ring.toIntAlgebra in
attribute [local instance] Polynomial.algebra Algebra.TensorProduct.rightAlgebra in
open FiniteAlgebraCompletion _root_.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion in
private theorem extends_to_completed_polynomial_tensor
    {S B : Type u} [CommRing S] [CommRing B] [Algebra S B]
    [IsNoetherianRing S] [Module.Finite S B] (P : Ideal S[X]) [P.IsPrime]
    (D : Derivation ℤ B B) :
    ∃ E : Derivation ℤ (B ⊗[S] CompletedPolynomialStalk P)
        (B ⊗[S] CompletedPolynomialStalk P),
      ∀ b : B, E (algebraMap B _ b) = algebraMap B _ (D b) := by
  let C := CompletedPolynomialStalk P
  let A := B ⊗[S] C
  let U := C ⊗[S[X]] B[X]
  -- Move the finite extension of constants to the polynomial rings before completing.
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite S B
  let ePoly := Algebra.IsPushout.equiv S S[X] B B[X]
  letI : Module.Finite S[X] B[X] :=
    Module.Finite.of_surjective ePoly.toLinearMap ePoly.surjective
  letI : Algebra B U := ((algebraMap B[X] U).comp (algebraMap B B[X])).toAlgebra
  letI : IsScalarTower B B[X] U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S B[X] U := IsScalarTower.to₁₃₄ S S[X] B[X] U
  letI : IsScalarTower S B U := IsScalarTower.to₁₂₄ S B B[X] U
  letI : IsScalarTower S C U := IsScalarTower.to₁₃₄ S S[X] C U
  letI : Algebra.IsPushout S C B U :=
    (Algebra.IsPushout.comp_iff S S[X] B (S' := B[X]) (T := C)).2 inferInstance
  let eBase : A ≃+* U :=
    (Algebra.TensorProduct.comm S B C).toRingEquiv.trans
      (Algebra.IsPushout.equiv S C B U).toRingEquiv
  let T := (q : PrimesOver P B[X]) → Factor P q
  let e : A ≃+* T := eBase.trans (decomposition (B := B[X]) P).toRingEquiv
  have hBase (b : B) :
      eBase (b ⊗ₜ[S] (1 : C)) = (1 : C) ⊗ₜ[S[X]] Polynomial.C b := by
    change Algebra.IsPushout.equiv S C B U ((1 : C) ⊗ₜ[S] b) = _
    rw [Algebra.IsPushout.equiv_tmul, map_one]
    change (1 : U) * algebraMap B U b = _
    exact one_mul (algebraMap B U b)
  have he (b : B) (q : PrimesOver P B[X]) :
      e (algebraMap B A b) q = algebraMap B[X] (Factor P q) (Polynomial.C b) := by
    change decomposition P (eBase (b ⊗ₜ[S] (1 : C))) q = _
    rw [hBase, decomposition_one_tmul]
  let Dq (q : PrimesOver P B[X]) : Derivation ℤ (Factor P q) (Factor P q) :=
    adicCompletionDerivation (R := Localization.AtPrime q.1.asIdeal)
      (localizationDerivation q.1.asIdeal.primeCompl (polynomialDerivation D))
      (maximalIdeal (Localization.AtPrime q.1.asIdeal))
  have hDq (b : B) (q : PrimesOver P B[X]) :
      Dq q (algebraMap B[X] (Factor P q) (Polynomial.C b)) =
        algebraMap B[X] (Factor P q) (Polynomial.C (D b)) := by
    let L := Localization.AtPrime q.1.asIdeal
    change adicCompletionDerivation _ _ (algebraMap B[X] (Factor P q) (Polynomial.C b)) = _
    rw [IsScalarTower.algebraMap_apply B[X] L (Factor P q) (Polynomial.C b),
      adicCompletionDerivation_algebraMap]
    erw [localizationDerivation_algebraMap (L := L) q.1.asIdeal.primeCompl
      (polynomialDerivation D) (Polynomial.C b)]
    rw [polynomialDerivation_C]
    exact (IsScalarTower.algebraMap_apply B[X] L (Factor P q) (Polynomial.C (D b))).symm
  let delta : T →+ T :=
    { toFun := fun a q => Dq q (a q)
      map_zero' := funext fun q => map_zero (Dq q)
      map_add' := fun a b => funext fun q => map_add (Dq q) (a q) (b q) }
  let E : Derivation ℤ A A := Derivation.mk'
    (e.symm.toAddMonoidHom.comp (delta.comp e.toAddMonoidHom)).toIntLinearMap
    (fun x y => by
      simp only [smul_eq_mul]
      apply e.injective
      rw [e.map_add, e.map_mul, e.map_mul]
      change e (e.symm (delta (e (x * y)))) =
        e x * e (e.symm (delta (e y))) + e y * e (e.symm (delta (e x)))
      simp only [e.apply_symm_apply, e.map_mul]
      funext q
      exact (Dq q).leibniz (e x q) (e y q))
  refine ⟨E, fun b => ?_⟩
  apply e.injective
  funext q
  change e (e.symm (delta (e (algebraMap B A b)))) q = _
  rw [e.apply_symm_apply]
  change Dq q (e (algebraMap B A b) q) = _
  rw [he, he, hDq]

set_option backward.isDefEq.respectTransparency false in
private theorem extends_to_fraction_tensor
    {S B M : Type u} [CommRing S] [CommRing B] [Field M]
    [Algebra S B] [Algebra B M] [Algebra S M] [IsScalarTower S B M]
    [IsNoetherianRing S] [Module.Finite S B] [IsFractionRing B M] [IsDomain B]
    (P : Ideal S[X]) [P.IsPrime] (D : Derivation ℤ B B) :
    ∃ E : Derivation ℤ (M ⊗[S] CompletedPolynomialStalk P)
        (M ⊗[S] CompletedPolynomialStalk P),
      ∀ b : B, E (algebraMap M _ (algebraMap B M b)) =
        algebraMap M _ (algebraMap B M (D b)) := by
  let C := CompletedPolynomialStalk P
  let A := B ⊗[S] C
  let U := M ⊗[B] A
  let V := M ⊗[S] C
  obtain ⟨d, hd⟩ := extends_to_completed_polynomial_tensor P D
  letI : Algebra M U := Algebra.TensorProduct.leftAlgebra
  letI : Algebra A U := rightAlgebra
  letI : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) U :=
    IsLocalization.tensorRight (A := M) (S := A) _
  let d' : Derivation ℤ U U :=
    localizationDerivation (L := U) (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) d
  let e : U ≃ₐ[M] V := cancelBaseChange S B M M C
  let E : Derivation ℤ V V := Derivation.mk'
    (e.toRingEquiv.toAddMonoidHom.comp
      (d'.toLinearMap.toAddMonoidHom.comp e.symm.toRingEquiv.toAddMonoidHom)).toIntLinearMap
    (fun x y => by
      change e (d' (e.symm (x * y))) = x • e (d' (e.symm y)) + y • e (d' (e.symm x))
      simp only [smul_eq_mul, map_mul, Derivation.leibniz, map_add, AlgEquiv.apply_symm_apply])
  refine ⟨E, fun b => ?_⟩
  have h (b : B) : (algebraMap B M b) ⊗ₜ[B] (1 : A) =
      (1 : M) ⊗ₜ[B] (algebraMap B A b) :=
    tmul_one_eq_one_tmul b
  change e (d' (e.symm (algebraMap M V (algebraMap B M b)))) = _
  rw [e.symm.commutes (algebraMap B M b)]
  let i := includeLeftRingHom (R := B) (A := M) (B := A)
  let j := (includeRight (R := B) (A := M) (B := A)).toRingHom
  have h' (b : B) : i (algebraMap B M b) = j (algebraMap B A b) := h b
  erw [h' b, localizationDerivation_algebraMap, hd b, ← h' (D b)]
  exact e.commutes (algebraMap B M (D b))

set_option backward.isDefEq.respectTransparency false in
private theorem exists_derivation_unit_on_radicand
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ)
    (P : Ideal (MvPowerSeries (Fin r) k)[X]) [P.IsPrime]
    (M : Type u) [Field M] [Algebra (FractionRing (MvPowerSeries (Fin r) k)) M]
    [Module.Finite (FractionRing (MvPowerSeries (Fin r) k)) M]
    [Algebra (MvPowerSeries (Fin r) k) M]
    [IsScalarTower (MvPowerSeries (Fin r) k) (FractionRing (MvPowerSeries (Fin r) k)) M]
    [CharP M p] (f : M) (hf : ¬ ∃ x : M, x ^ p = f) :
    ∃ D : Derivation ℤ (M ⊗[MvPowerSeries (Fin r) k] CompletedPolynomialStalk P)
        (M ⊗[MvPowerSeries (Fin r) k] CompletedPolynomialStalk P),
      IsUnit (D (f ⊗ₜ[MvPowerSeries (Fin r) k] 1)) := by
  let S := MvPowerSeries (Fin r) k
  let R := M ⊗[S] CompletedPolynomialStalk P
  letI : CommRing R := Algebra.TensorProduct.instCommRing
  let i := includeLeftRingHom (R := S) (A := M) (B := CompletedPolynomialStalk P)
  letI : IsDomain S := NoZeroDivisors.to_isDomain _
  letI : IsRegularLocalRing S := (CompleteRegularPowerSeries.overField k r).2.1
  obtain ⟨B, hB, hfin, hfrac⟩ := exists_finite_domain_model S (FractionRing S) M
  obtain ⟨den, hden, hmem⟩ := exists_pow_mul_mem B f p (Fact.out : p.Prime).pos
  let c : M := algebraMap B M den
  have hc : c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective B M)).2 hden
  let a : B := ⟨c ^ p * f, hmem⟩
  have ha : ¬ ∃ x : M, x ^ p = algebraMap B M a := by
    rintro ⟨x, hx⟩
    apply hf
    refine ⟨x / c, ?_⟩
    change x ^ p = c ^ p * f at hx
    rw [div_pow, hx, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hc)]
  obtain ⟨d, hd⟩ := exists_derivation_over_powerSeries k p r B M a ha
  obtain ⟨D, hD⟩ := extends_to_fraction_tensor (M := M) P d
  have hunit : IsUnit (D (i (c ^ p * f))) := by
    have hres : D (i (c ^ p * f)) = i (algebraMap B M (d a)) := hD a
    rw [hres]
    exact (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective B M)).2 hd)).map i
  have hpR : (p : R) = 0 := by
    rw [← map_natCast i, CharP.cast_eq_zero M p, map_zero]
  -- Differentiating the denominator's pth power gives zero.
  have hpD : D ((i c) ^ p) = 0 := by
    rw [Derivation.leibniz_pow, nsmul_eq_mul, hpR, zero_mul]
  rw [map_mul, map_pow, Derivation.leibniz, hpD, smul_zero, add_zero, smul_eq_mul] at hunit
  have hDunit : IsUnit (D (i f)) := isUnit_of_mul_isUnit_right (M := R) hunit
  exact ⟨D, hDunit⟩

private theorem regular_adjoinRoot_tensor
    {M A N : Type*} [Field M] [CommRing A] [CommRing N]
    [Algebra M A] [Algebra M N] [IsRegularRing A]
    (p : ℕ) (hp : 1 ≤ p) (a : M)
    (e : AdjoinRoot (X ^ p - C a) ≃ₐ[M] N)
    (D : Derivation ℤ A A) (hD : IsUnit (D (algebraMap M A a))) :
    IsRegularRing (N ⊗[M] A) := by
  let g : A[X] := X ^ p - C (algebraMap M A a)
  letI : IsRegularRing (AdjoinRoot g) := (regularRing_iff _).mp
    (regularRing_quotient_X_pow_sub_C_of_isUnit_derivation
      ((regularRing_iff A).mpr inferInstance) D _ hD p hp)
  let e₁ : (A ⊗[M] AdjoinRoot (X ^ p - C a)) ≃ₐ[A] AdjoinRoot
      (X ^ p - C ((1 : A) ⊗ₜ[M] a)) :=
    AdjoinRoot.tensorAlgEquiv _ _ (by simp)
  let e₂ : (A ⊗[M] M) ≃+* A :=
    (Algebra.TensorProduct.rid M M A).toRingEquiv
  have he₂ : e₂ ((1 : A) ⊗ₜ[M] a) = algebraMap M A a := by
    simp [e₂, Algebra.smul_def]
  let e₁ : (A ⊗[M] AdjoinRoot (X ^ p - C a)) ≃+*
      AdjoinRoot (X ^ p - C (algebraMap M A a)) := by
    exact e₁.toRingEquiv.trans
      (AdjoinRoot.mapRingEquiv e₂ _ _ (by simp [he₂]))
  let e₃ := (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[M] A) e).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (e₁.symm.trans (e₃.trans (Algebra.TensorProduct.comm M A N).toRingEquiv))

private theorem geometricallyRegular_of_charP
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r : ℕ)
    (P : Ideal (MvPowerSeries (Fin r) k)[X]) [P.IsPrime] :
    letI : IsDomain (MvPowerSeries (Fin r) k) := NoZeroDivisors.to_isDomain _
    GeometricallyRegular (FractionRing (MvPowerSeries (Fin r) k)) (GenericConstantsFibre P) := by
  let S := MvPowerSeries (Fin r) k
  letI : IsDomain S := NoZeroDivisors.to_isDomain _
  letI : IsRegularLocalRing S := (CompleteRegularPowerSeries.overField k r).2.1
  let K := FractionRing S
  let A := CompletedPolynomialStalk P
  letI : CharP S p := charP_of_injective_ringHom (f := MvPowerSeries.C)
    MvPowerSeries.C_injective p
  letI : CharP K p := IsFractionRing.charP_of_isFractionRing S p
  letI : IsRegularRing (K ⊗[S] A) := regular_genericConstantsFibre P
  intro F _ _ _
  letI : Algebra S F := ((algebraMap K F).comp (algebraMap S K)).toAlgebra
  letI : IsScalarTower S K F := IsScalarTower.of_algebraMap_eq' rfl
  have hbase : IsRegularRing ((⊥ : IntermediateField K F) ⊗[S] A) := by
    let e := (IntermediateField.botEquiv K F).symm.restrictScalars S
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[S] A)).toRingEquiv
  have hstep (M N : IntermediateField K F) (h : IsSimpleFieldStep p M N)
      (hM : IsRegularRing (M ⊗[S] A)) : IsRegularRing (N ⊗[S] A) := by
    obtain ⟨b, rfl, hb, h⟩ := h
    let E := IntermediateField.adjoin M ({b} : Set F)
    letI : IsScalarTower S M F := IsScalarTower.to₁₃₄ S K M F
    haveI : IsScalarTower S M E := inferInstance
    change IsRegularRing (E ⊗[S] A)
    let R := M ⊗[S] A
    letI : CommRing R := Algebra.TensorProduct.instCommRing
    letI : Algebra M R := Algebra.TensorProduct.leftAlgebra
    let eCancel := (cancelBaseChange S M E E A).toRingEquiv
    suffices hE : IsRegularRing (E ⊗[M] R) by
      letI := hE
      exact IsRegularRing.of_ringEquiv eCancel
    rcases h with hsep | hpow
    · letI : Algebra.IsSeparable M E :=
        (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable M F).2 hsep
      exact regular_separable_tensor (K := M) (M := E) (A := M ⊗[S] A)
    · letI : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
      letI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
      let a : M := ⟨b ^ p, hpow⟩
      have ha : ¬ ∃ x : M, x ^ p = a := by
        rintro ⟨x, hx⟩
        apply hb
        have hxb : (algebraMap M F x) ^ p = b ^ p := by
          rw [← map_pow, hx]
          rfl
        have he : algebraMap M F x = b := (frobenius F p).injective hxb
        exact he ▸ x.property
      obtain ⟨D, hD⟩ := exists_derivation_unit_on_radicand k p r P M a ha
      let hmin := minpoly_eq_X_pow_sub_C_of_pow_mem K F p (Fact.out : p.Prime) M b a hb rfl
      let e : AdjoinRoot (X ^ p - C a) ≃ₐ[M] E :=
        (AdjoinRoot.algEquivOfEq M _ _ hmin.symm).trans
          (IntermediateField.adjoinRootEquivAdjoin M (Algebra.IsIntegral.isIntegral b))
      exact regular_adjoinRoot_tensor p (Fact.out : p.Prime).one_lt.le a e D hD
  have hregular (N : IntermediateField K F)
      (h : Relation.ReflTransGen (IsSimpleFieldStep p) ⊥ N) :
      IsRegularRing (N ⊗[S] A) := by
    induction h with
    | refl => exact hbase
    | tail _ hs ih => exact hstep _ _ hs ih
  have htop := hregular ⊤ (finiteExtension_has_simpleTower K F p (Fact.out : p.Prime))
  let eTop := (IntermediateField.topEquiv (F := K) (E := F)).restrictScalars S
  let e := (Algebra.TensorProduct.congr eTop (AlgEquiv.refl : A ≃ₐ[S] A)).toRingEquiv.trans
    (cancelBaseChange S K F F A).symm.toRingEquiv
  let R := K ⊗[S] A
  letI : CommRing R := Algebra.TensorProduct.instCommRing
  letI : Algebra K R := Algebra.TensorProduct.leftAlgebra
  letI : IsRegularRing (F ⊗[K] R) := IsRegularRing.of_ringEquiv e
  exact ⟨inferInstanceAs (IsNoetherianRing (F ⊗[K] R)),
    (regularRing_iff (F ⊗[K] R)).mpr inferInstance⟩

theorem overField :
    _root_.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants.OverField.{u} := by
  intro k _ r P _
  let S := MvPowerSeries (Fin r) k
  letI : IsDomain S := NoZeroDivisors.to_isDomain _
  letI : IsRegularLocalRing S := (CompleteRegularPowerSeries.overField k r).2.1
  rcases CharP.exists' k with h | ⟨p, hp, hc⟩
  · letI : CharZero S := charZero_of_injective_ringHom (f := MvPowerSeries.C)
      MvPowerSeries.C_injective
    letI : CharZero (FractionRing S) := IsFractionRing.charZero_of_isFractionRing S
    letI := regular_genericConstantsFibre P
    exact geometricallyRegular_of_charZero
  · exact geometricallyRegular_of_charP k p r P


theorem overCompleteDVR :
    _root_.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants.OverCompleteDVR.{u} := by
  intro D _ _ _ _ _ p _ hp r P _
  let S := MvPowerSeries (Fin r) D
  letI : IsDomain S := NoZeroDivisors.to_isDomain _
  letI : IsRegularLocalRing S := (CompleteRegularPowerSeries.overCompleteDVR D (p : D) hp r).2.1
  letI : CharZero S := charZero_of_injective_ringHom (f := MvPowerSeries.C) MvPowerSeries.C_injective
  letI : CharZero (FractionRing S) := IsFractionRing.charZero_of_isFractionRing S
  letI := regular_genericConstantsFibre P
  exact geometricallyRegular_of_charZero

end

end CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants
