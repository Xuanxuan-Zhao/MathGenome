import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PolynomialOverCompleteGRing
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FormalFiberQuotient
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularBaseGenericFormalFibers
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.Localization.BaseChange
import Batteries.Tactic.OpenPrivate

namespace CommutativeAlgebraNotes.Excellence

open Algebra IsLocalRing
open Polynomial (X)
open scoped Polynomial TensorProduct nonZeroDivisors
open _root_.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion (LocalCompletion PrimesOver Factor)
open _root_.Specs.CommutativeAlgebraNotes.PolynomialCompletionsOverRegularConstants
  (CompletedPolynomialStalk)

open _root_.CommutativeAlgebraNotes.Excellence.Specs (GenericFormalFiber)

open private regularFactor from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PolynomialCompletionsOverGenericBase

open private completionTensorEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FormalFiberQuotient

open private completedPrimeDerivation completedPrimeDerivation_algebraMap rebaseIntDerivation
  from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularBaseGenericFormalFibers

universe u

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] Polynomial.algebra FractionRing.liftAlgebra

private theorem regularNoetherian_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsNoetherianRing R ∧ RegularRing R) :
    IsNoetherianRing S ∧ RegularRing S := by
  letI : IsNoetherianRing R := h.1
  letI : IsRegularRing R := (regularRing_iff R).mp h.2
  letI : IsRegularRing S := IsRegularRing.of_ringEquiv e
  exact ⟨inferInstance, (regularRing_iff S).mpr inferInstance⟩

/-- A derivation on an algebra that kills the coefficients extends by
differentiating the right factor after scalar extension. -/
private def tensorDerivation {A C L : Type*} [CommRing A] [CommRing C] [CommRing L]
    [Algebra A C] [Algebra A L] (D : Derivation ℤ C C)
    (hD : ∀ a : A, D (algebraMap A C a) = 0) :
    Derivation L (L ⊗[A] C) (L ⊗[A] C) := by
  let d : C →ₗ[A] C :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun a c => by
        simp [Algebra.smul_def, D.leibniz, hD, smul_eq_mul] }
  let dL := TensorProduct.AlgebraTensorModule.lTensor L L d
  refine Derivation.mk' dL ?_
  have h (l : L) (c : C) : dL (l ⊗ₜ[A] c) = l ⊗ₜ[A] D c := rfl
  intro x y
  simp only [smul_eq_mul]
  induction x using TensorProduct.inductionOn with
  | tmul l c =>
    induction y using TensorProduct.inductionOn with
    | tmul m b =>
      simp only [TensorProduct.tmul_mul_tmul, h, D.leibniz, smul_eq_mul]
      rw [TensorProduct.tmul_add, mul_comm l m]
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, add_mul, map_add, h₁, h₂]; abel
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, add_mul, map_add, h₁, h₂]; abel

/-- When the polynomial variable acts on the scalar factor by alpha, tensoring
over the polynomial ring imposes just the equation X = alpha. -/
private def tensorOverPolynomialEquiv {A C L : Type*} [CommRing A] [CommRing C]
    [CommRing L] [Algebra A C] [Algebra A L] [Algebra A[X] C] [Algebra A[X] L]
    [IsScalarTower A A[X] C] [IsScalarTower A A[X] L] :
    ((L ⊗[A] C) ⧸ Ideal.span
      {(1 : L) ⊗ₜ[A] (algebraMap A[X] C X) - (algebraMap A[X] L X) ⊗ₜ[A] (1 : C)}) ≃ₐ[L]
        L ⊗[A[X]] C := by
  let T := L ⊗[A] C
  let J : Ideal T := Ideal.span
    {(1 : L) ⊗ₜ[A] (algebraMap A[X] C X) - (algebraMap A[X] L X) ⊗ₜ[A] (1 : C)}
  let U := T ⧸ J
  let V := L ⊗[A[X]] C
  let f : T →ₐ[L] V := Algebra.TensorProduct.mapOfCompatibleSMul A[X] A L L C
  have hJ : J ≤ RingHom.ker f := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change f _ = 0
    rw [map_sub]
    change (1 : L) ⊗ₜ[A[X]] (algebraMap A[X] C X) - (algebraMap A[X] L X) ⊗ₜ[A[X]] (1 : C) = 0
    rw [TensorProduct.tmul_one_eq_one_tmul, sub_self]
  let q : T →ₐ[L] U := Ideal.Quotient.mkₐ L J
  let r : C →+* U := q.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[A] T).toRingHom
  letI : Algebra A[X] U := ((algebraMap L U).comp (algebraMap A[X] L)).toAlgebra
  letI := IsScalarTower.of_algebraMap_eq (R := A[X]) (S := L) (A := U) fun _ => rfl
  have hr : r.comp (algebraMap A[X] C) = (algebraMap L U).comp (algebraMap A[X] L) := by
    apply Polynomial.ringHom_ext
    · intro a
      have hC : (Polynomial.C a : A[X]) = algebraMap A A[X] a := rfl
      simp only [RingHom.comp_apply, hC, ← IsScalarTower.algebraMap_apply A A[X]]
      change q ((1 : L) ⊗ₜ[A] algebraMap A C a) = q ((algebraMap A L a) ⊗ₜ[A] (1 : C))
      rw [TensorProduct.tmul_one_eq_one_tmul]
    · have hx : Ideal.Quotient.mk J
          ((1 : L) ⊗ₜ[A] (algebraMap A[X] C X) -
            (algebraMap A[X] L X) ⊗ₜ[A] (1 : C)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      change q ((1 : L) ⊗ₜ[A] algebraMap A[X] C X) =
        q ((algebraMap A[X] L X) ⊗ₜ[A] (1 : C))
      exact sub_eq_zero.mp (by rwa [map_sub] at hx)
  let g := Algebra.TensorProduct.lift (Algebra.ofId L U)
    (⟨r, fun x => DFunLike.congr_fun hr x⟩ : C →ₐ[A[X]] U) (fun _ _ => Commute.all _ _)
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ J f hJ) g ?_ ?_
  · ext x
    simp [g, r, q]
    rfl
  · apply Ideal.Quotient.algHom_ext
    ext x
    change g (1 ⊗ₜ[A[X]] x) = r x
    simp [g]

/-- A surjective local image of a complete Noetherian local ring is complete. -/
private theorem isAdicComplete_of_surjective_local {A B : Type u}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra A B]
    (h : Function.Surjective (algebraMap A B)) :
    IsAdicComplete (maximalIdeal B) B := by
  letI := Module.Finite.of_surjective (Algebra.linearMap A B) h
  let e₁ : A ≃ₐ[A] LocalCompletion A :=
    AlgEquiv.ofBijective (Algebra.ofId A (LocalCompletion A))
      (AdicCompletion.of_bijective (maximalIdeal A) A)
  let e₂ := (Algebra.TensorProduct.rid A B B).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := B) (A₁ := B)) e₁)
  let e := e₂.trans (completionTensorEquiv (maximalIdeal A) B)
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) h,
    ← AdicCompletion.of_bijective_iff]
  convert e.bijective using 1
  funext b
  exact (e.commutes b).symm

/-- A nonzero polynomial prime over zero is a closed point over the fraction
field, and its residue field is finite over that field. -/
private theorem finite_residueField_over_fraction {A : Type u} [CommRing A] [IsDomain A]
    (q : Ideal A[X]) [q.IsPrime] (hq : q ≠ ⊥) (h0 : q.comap Polynomial.C = ⊥) :
    ∃ _ : Algebra (FractionRing A) q.ResidueField,
      IsScalarTower A (FractionRing A) q.ResidueField ∧ Module.Finite (FractionRing A) q.ResidueField := by
  let K := FractionRing A
  let M : Submonoid A[X] := (nonZeroDivisors A).map Polynomial.C
  letI : IsLocalization M K[X] := Polynomial.isLocalization (nonZeroDivisors A) K
  let f : A[X] →+* K[X] := algebraMap A[X] K[X]
  let Q := q.map f
  have hd : Disjoint (M : Set A[X]) (q : Set A[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ h
    have hz : a ∈ q.comap Polynomial.C := h
    rw [h0, Ideal.mem_bot] at hz
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha) hz
  letI : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] q inferInstance hd
  have hQ : q = Q.comap f := (IsLocalization.under_map_of_isPrime_disjoint
    M K[X] (show q.IsPrime from inferInstance) hd).symm
  have hinj : Function.Injective f := Polynomial.map_injective _ (IsFractionRing.injective A K)
  have hQ0 : Q ≠ ⊥ := fun h =>
    hq (by rw [hQ, h, Ideal.comap_bot_of_injective _ hinj])
  letI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ0
  let e : q.ResidueField ≃+* Q.ResidueField :=
    RingEquiv.ofBijective (Ideal.ResidueField.map q Q f hQ)
      ((RingHom.surjectiveOnStalks_of_isLocalization M K[X]).residueFieldMap_bijective q Q hQ)
  letI : Algebra K q.ResidueField := (e.symm.toRingHom.comp (algebraMap K Q.ResidueField)).toAlgebra
  have hcompat (a : A) : e (algebraMap A q.ResidueField a) =
      algebraMap K Q.ResidueField (algebraMap A K a) := by
    change Ideal.ResidueField.map q Q f hQ (algebraMap A q.ResidueField a) = _
    rw [IsScalarTower.algebraMap_apply A A[X], Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply K K[X]]
    simp [f, Polynomial.algebraMap_def]
  letI : IsScalarTower A K q.ResidueField := IsScalarTower.of_algebraMap_eq fun a =>
    e.injective (by rw [hcompat]; exact (e.apply_symm_apply _).symm)
  have hfin : Module.Finite K Q.ResidueField := by
    obtain ⟨g, hg⟩ := (inferInstance : Q.IsPrincipal)
    have hg0 : g ≠ 0 := by
      intro h
      exact hQ0 (by simp [hg, h])
    let m := g * Polynomial.C g.leadingCoeff⁻¹
    have hm : Q = Ideal.span {m} :=
      hg.trans (Ideal.span_singleton_mul_right_unit
        (IsUnit.map Polynomial.C (isUnit_iff_ne_zero.mpr (inv_ne_zero
          (Polynomial.leadingCoeff_ne_zero.mpr hg0)))) g).symm
    letI : Module.Finite K (K[X] ⧸ Q) :=
      hm ▸ (Polynomial.monic_mul_leadingCoeff_inv hg0).finite_quotient
    exact Module.Finite.of_surjective (IsScalarTower.toAlgHom K (K[X] ⧸ Q)
      Q.ResidueField).toLinearMap Q.bijective_algebraMap_quotient_residueField.surjective
  let eK : Q.ResidueField ≃ₐ[K] q.ResidueField :=
    { __ := e.symm, commutes' := fun _ => rfl }
  exact ⟨inferInstance, inferInstance, Module.Finite.of_surjective eK.toLinearMap eK.surjective⟩

private theorem regular_nonzeroPolynomialFibre {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (P q : Ideal A[X]) [P.IsPrime] [q.IsPrime]
    (hq : q ≠ ⊥) (h0 : q.comap Polynomial.C = ⊥)
    (L : Type u) [Field L] [Algebra q.ResidueField L] [Module.Finite q.ResidueField L] :
    letI : Algebra A[X] L := ((algebraMap q.ResidueField L).comp
      (algebraMap A[X] q.ResidueField)).toAlgebra
    IsNoetherianRing (L ⊗[A[X]] CompletedPolynomialStalk P) ∧
      RegularRing (L ⊗[A[X]] CompletedPolynomialStalk P) := by
  let K := FractionRing A
  letI : Algebra A[X] L := ((algebraMap q.ResidueField L).comp
    (algebraMap A[X] q.ResidueField)).toAlgebra
  letI : IsScalarTower A[X] q.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra A L := ((algebraMap q.ResidueField L).comp
    (algebraMap A q.ResidueField)).toAlgebra
  letI : IsScalarTower A q.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A A[X] L := IsScalarTower.to₁₂₄ A A[X] q.ResidueField L
  obtain ⟨aK, hTower, hFinite⟩ := finite_residueField_over_fraction q hq h0
  letI : Algebra K q.ResidueField := aK
  letI : IsScalarTower A K q.ResidueField := hTower
  letI : Module.Finite K q.ResidueField := hFinite
  letI : Algebra K L := ((algebraMap q.ResidueField L).comp (algebraMap K q.ResidueField)).toAlgebra
  letI : IsScalarTower K q.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.to₁₂₄ A K q.ResidueField L
  letI : Module.Finite K L := Module.Finite.trans q.ResidueField L
  let C := CompletedPolynomialStalk P
  let e := Algebra.TensorProduct.cancelBaseChange A K L L C
  obtain ⟨hNoeth, hReg⟩ := regularNoetherian_of_ringEquiv e.toRingEquiv
    (PolynomialCompletionsOverGenericBase.overCompleteLocalDomain A P L)
  letI : IsNoetherianRing (L ⊗[A] C) := hNoeth
  let D := @rebaseIntDerivation A[X] _ _ (Ring.toIntAlgebra A[X])
    ((Polynomial.derivative' (R := A)).restrictScalars ℤ)
  let E : Derivation ℤ C C := completedPrimeDerivation P D
  have hE (a : A) : E (algebraMap A C a) = 0 := by
    rw [IsScalarTower.algebraMap_apply A A[X]]
    exact (completedPrimeDerivation_algebraMap P D (Polynomial.C a)).trans (by
      change algebraMap A[X] C (Polynomial.derivative (Polynomial.C a)) = 0
      simp)
  have hX : E (algebraMap A[X] C X) = 1 := by
    change completedPrimeDerivation P D (algebraMap A[X] (LocalCompletion (Localization.AtPrime P)) X) = _
    rw [completedPrimeDerivation_algebraMap]
    change algebraMap A[X] C (Polynomial.derivative (X : A[X])) = 1
    simp
  let E₀ := @rebaseIntDerivation C _ _ (Ring.toIntAlgebra C) E
  let ε := tensorDerivation (A := A) (L := L) (C := C) E₀ hE
  let d := @rebaseIntDerivation (L ⊗[A] C) _ _ (Ring.toIntAlgebra _) (ε.restrictScalars ℤ)
  let g := (1 : L) ⊗ₜ[A] (algebraMap A[X] C X) - (algebraMap A[X] L X) ⊗ₜ[A] (1 : C)
  have hd : d g = 1 := by
    change ε g = 1
    change ε (_ - _) = 1
    rw [map_sub]
    change ((1 : L) ⊗ₜ[A] E (algebraMap A[X] C X)) -
      ((algebraMap A[X] L X) ⊗ₜ[A] E 1) = 1
    simp [hX, Algebra.TensorProduct.one_def]
  have hquot := regularRing_quotient_span_singleton_of_isUnit_derivation hReg d g
    (by rw [hd]; exact isUnit_one)
  exact regularNoetherian_of_ringEquiv
    (tensorOverPolynomialEquiv (A := A) (C := C) (L := L)).toRingEquiv
    ⟨inferInstance, hquot⟩

/-- Generic formal fibres over a finite domain extension are factors of the
corresponding generic formal fibres before the finite extension. -/
private theorem regular_genericFibre_of_finite {R S : Type u}
    [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) (P : Ideal S) [P.IsPrime]
    (hreg : ∀ (p : Ideal R) [p.IsPrime],
      GeometricallyRegular (FractionRing R) (GenericFormalFiber R (FractionRing R) p))
    (L : Type u) [Field L] [Algebra S L] [Algebra (FractionRing S) L]
    [IsScalarTower S (FractionRing S) L] [Module.Finite (FractionRing S) L] :
    IsNoetherianRing (L ⊗[S] LocalCompletion (Localization.AtPrime P)) ∧
      RegularRing (L ⊗[S] LocalCompletion (Localization.AtPrime P)) := by
  classical
  let p := P.comap (algebraMap R S)
  letI : p.IsPrime := Ideal.IsPrime.comap _
  let C := LocalCompletion (Localization.AtPrime p)
  let B := (j : PrimesOver p S) → Factor p j
  let i : PrimesOver p S := ⟨⟨P, inferInstance⟩, rfl⟩
  letI : Finite (PrimesOver p S) := FiniteAlgebraCompletion.finitePrimes R S p
  letI : Fintype (PrimesOver p S) := Fintype.ofFinite _
  let e : S ⊗[R] C ≃ₐ[S] B :=
    { __ := (Algebra.TensorProduct.comm R S C).toRingEquiv.trans
        (FiniteAlgebraCompletion.decomposition (B := S) p).toRingEquiv
      commutes' s := by
        funext j
        change FiniteAlgebraCompletion.decomposition p ((1 : C) ⊗ₜ[R] s) j = _
        exact FiniteAlgebraCompletion.decomposition_one_tmul p s j }
  let K := FractionRing R
  let F := FractionRing S
  letI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  letI : Algebra K F := FractionRing.liftAlgebra R F
  letI : IsScalarTower R K F := FractionRing.isScalarTower_liftAlgebra R F
  letI : Module.Finite K F := inferInstanceAs (Module.Finite (FractionRing R) (FractionRing S))
  letI : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R F L := IsScalarTower.to₁₃₄ R S F L
  letI : IsScalarTower R K L := IsScalarTower.to₁₂₄ R K F L
  letI : Module.Finite K L := Module.Finite.trans F L
  let eL : (L ⊗[K] (K ⊗[R] C)) ≃ₐ[L] ((j : PrimesOver p S) → L ⊗[S] Factor p j) :=
    (Algebra.TensorProduct.cancelBaseChange R K L L C).trans
      ((Algebra.TensorProduct.cancelBaseChange R S L L C).symm.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans
          (Algebra.TensorProduct.piRight S L L (Factor p))))
  obtain ⟨hN, hR⟩ := regularNoetherian_of_ringEquiv eL.toRingEquiv
    ((hreg p).regular_tensorProduct L)
  letI : IsNoetherianRing ((j : PrimesOver p S) → L ⊗[S] Factor p j) := hN
  letI : IsRegularRing ((j : PrimesOver p S) → L ⊗[S] Factor p j) :=
    (regularRing_iff _).mp hR
  letI : IsRegularRing (L ⊗[S] LocalCompletion (Localization.AtPrime P)) :=
    regularFactor (R := fun j : PrimesOver p S => L ⊗[S] Factor p j) i
  exact ⟨inferInstance, (regularRing_iff _).mpr inferInstance⟩

private theorem regular_genericFibre_of_polynomialNormalization {R S A : Type u}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Algebra S A] [Module.Finite S A]
    (hSA : Function.Injective (algebraMap S A)) (e : R ≃+* S[X])
    (hreg : ∀ (p : Ideal R) [p.IsPrime],
      GeometricallyRegular (FractionRing R) (GenericFormalFiber R (FractionRing R) p))
    (P : Ideal A[X]) [P.IsPrime] (L : Type u) [Field L]
    [Algebra A[X] L] [Algebra (FractionRing A[X]) L]
    [IsScalarTower A[X] (FractionRing A[X]) L] [Module.Finite (FractionRing A[X]) L] :
    IsNoetherianRing (L ⊗[A[X]] CompletedPolynomialStalk P) ∧
      RegularRing (L ⊗[A[X]] CompletedPolynomialStalk P) := by
  letI : Module.Finite S[X] A[X] :=
    Module.Finite.of_surjective (Algebra.IsPushout.equiv S S[X] A A[X]).toLinearMap
      (Algebra.IsPushout.equiv S S[X] A A[X]).surjective
  let f := (algebraMap S[X] A[X]).comp e.toRingHom
  letI : Algebra R A[X] := f.toAlgebra
  letI : Module.Finite R A[X] :=
    ((RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite S[X] A[X])).comp e.finite :
      f.Finite)
  exact regular_genericFibre_of_finite ((Polynomial.map_injective _ hSA).comp e.injective) P hreg L

private theorem regular_genericPolynomialFibre {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (P : Ideal A[X]) [P.IsPrime] (L : Type u) [Field L]
    [Algebra A[X] L] [Algebra (FractionRing A[X]) L]
    [IsScalarTower A[X] (FractionRing A[X]) L] [Module.Finite (FractionRing A[X]) L] :
    IsNoetherianRing (L ⊗[A[X]] CompletedPolynomialStalk P) ∧
      RegularRing (L ⊗[A[X]] CompletedPolynomialStalk P) := by
  have charZeroCase (S : Type u) [CommRing S] [IsDomain S] [IsRegularLocalRing S]
      [CharZero S] [Algebra S A] [Module.Finite S A]
      (hSA : Function.Injective (algebraMap S A)) :
      IsNoetherianRing (L ⊗[A[X]] CompletedPolynomialStalk P) ∧
        RegularRing (L ⊗[A[X]] CompletedPolynomialStalk P) := by
    refine regular_genericFibre_of_polynomialNormalization hSA (RingEquiv.refl S[X]) ?_ P L
    intro p hp
    exact regularBaseGenericFormalFiberCharZero S[X] (FractionRing S[X])
      (regularRing_polynomial S (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime S)) p
  obtain ⟨d, _, h⟩ := CoefficientRings.finitePowerSeriesNormalization A
  rcases h with ⟨_, σ, x, F, _, _, _, _, _, _, hF⟩ | ⟨p, hp, _, _, h⟩
  · obtain ⟨_, _, hRegular, _, _, hinj, _, hFinite, _⟩ := hF
    let k := ResidueField A
    let S := MvPowerSeries (Fin d) k
    letI : IsDomain S := NoZeroDivisors.to_isDomain _
    letI : IsRegularLocalRing S := hRegular
    letI : Algebra S A := F.toAlgebra
    letI : Module.Finite S A := hFinite
    let p := ringChar k
    letI : CharP k p := ringChar.charP k
    rcases CharP.char_is_prime_or_zero k p with hp | hp
    · letI : Fact p.Prime := ⟨hp⟩
      exact regular_genericFibre_of_polynomialNormalization hinj
        (MvPolynomial.uniqueAlgEquiv S (Fin 1)).toRingEquiv
        (fun q _ => regularBaseGenericFormalFiberCharP k p d 1 q) P L
    · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hp
      letI : CharZero S := charZero_of_injective_ringHom MvPowerSeries.C_injective
      exact charZeroCase S hinj
  · obtain ⟨_, _, _, _, D, _, _, _, _, _, _, _, _, _, F, _, _, _, _, _, _, _, hF⟩ := h
    obtain ⟨_, _, hRegular, _, _, hinj, _, hFinite, _⟩ := hF
    let S := MvPowerSeries (Fin (d - 1)) D
    letI : IsDomain S := NoZeroDivisors.to_isDomain _
    letI : IsRegularLocalRing S := hRegular
    letI : Algebra S A := F.toAlgebra
    letI : Module.Finite S A := hFinite
    letI : CharZero S := charZero_of_injective_ringHom MvPowerSeries.C_injective
    exact charZeroCase S hinj

/-- For a surjective algebra map the completed stalk at the source prime base
changes to the completed stalk at the corresponding target prime. -/
private def completedStalkTensorEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [Algebra R S]
    (hsurj : Function.Surjective (algebraMap R S)) (P : Ideal R) [P.IsPrime]
    (Q : Ideal S) [Q.IsPrime] (hP : P = Q.comap (algebraMap R S)) :
    S ⊗[R] LocalCompletion (Localization.AtPrime P) ≃ₐ[S]
      LocalCompletion (Localization.AtPrime Q) := by
  let H := Localization.AtPrime P
  let K := Localization.AtPrime Q
  let C := LocalCompletion H
  letI : Q.LiesOver P := ⟨hP⟩
  letI : Algebra H K := Localization.AtPrime.algebraOfLiesOver P Q
  letI : IsScalarTower R H K := inferInstanceAs
    (letI := Localization.AtPrime.algebraOfLiesOver P Q
     IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q))
  have hf : Function.Surjective (algebraMap H K) := by
    change Function.Surjective (Localization.localRingHom P Q (algebraMap R S) hP)
    subst P
    exact RingHom.surjectiveOnStalks_of_surjective hsurj Q inferInstance
  letI : Module.Finite H K := Module.Finite.of_surjective (Algebra.linearMap H K) hf
  have hM : P.primeCompl.map (algebraMap R S) = Q.primeCompl := by
    subst P
    exact Q.map_primeCompl_comap_of_surjective _ hsurj
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid S P.primeCompl) K := by
    change IsLocalization (P.primeCompl.map (algebraMap R S)) (Localization.AtPrime Q)
    rw [hM]
    infer_instance
  letI : Algebra.IsPushout R S H K :=
    (Algebra.isLocalization_iff_isPushout (T := S) (B := K) P.primeCompl H).mp hloc
  let e := (Algebra.IsPushout.cancelBaseChange R S H K C).symm
  let e₁ : S ⊗[R] C ≃ₐ[S] K ⊗[H] C :=
    AlgEquiv.ofLinearEquiv e (by simp [e, Algebra.TensorProduct.one_def])
      (LinearMap.map_mul_of_map_mul_tmul fun x a y b => by
        simp [e, Algebra.TensorProduct.tmul_mul_tmul])
  let e₂ := completionTensorEquiv (maximalIdeal H) K
  have hm : (maximalIdeal H).map (algebraMap H K) = maximalIdeal K :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hf
  change S ⊗[R] C ≃ₐ[S] AdicCompletion (maximalIdeal K) K
  rw [← hm]
  exact e₁.trans (e₂.restrictScalars S)

/-- The scalar action on a test field is the composite through the residue field. -/
private abbrev testAlgebra {R L : Type u} [CommRing R] [CommRing L]
    (q : Ideal R) [q.IsPrime] [Algebra q.ResidueField L] : Algebra R L :=
  ((algebraMap q.ResidueField L).comp (algebraMap R q.ResidueField)).toAlgebra

private abbrev TestedFibre {R : Type u} [CommRing R] (P q : Ideal R)
    [P.IsPrime] [q.IsPrime] (L : Type u) [Field L] [Algebra q.ResidueField L] :=
  letI := testAlgebra (L := L) q
  L ⊗[R] LocalCompletion (Localization.AtPrime P)

private def goodFormalFibre {R : Type u} [CommRing R] (P q : Ideal R)
    [P.IsPrime] [q.IsPrime] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra q.ResidueField L] [Module.Finite q.ResidueField L],
    IsNoetherianRing (TestedFibre P q L) ∧ RegularRing (TestedFibre P q L)

private theorem goodFormalFibre_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [Algebra R S] (hsurj : Function.Surjective (algebraMap R S))
    (P q : Ideal R) [P.IsPrime] [q.IsPrime] (Q r : Ideal S) [Q.IsPrime] [r.IsPrime]
    (hP : P = Q.comap (algebraMap R S)) (hq : q = r.comap (algebraMap R S))
    (h : goodFormalFibre Q r) : goodFormalFibre P q := by
  intro L _ _ _
  letI : Algebra R L := testAlgebra (L := L) q
  let e : q.ResidueField ≃+* r.ResidueField :=
    RingEquiv.ofBijective (Ideal.ResidueField.map q r (algebraMap R S) hq)
      ((RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective q r hq)
  letI : Algebra r.ResidueField L := ((algebraMap q.ResidueField L).comp e.symm.toRingHom).toAlgebra
  letI : Module.Finite r.ResidueField L :=
    Module.Finite.of_equiv_equiv e (RingEquiv.refl L) (by ext x; simp [RingHom.algebraMap_toAlgebra])
  letI : Algebra S L := testAlgebra (L := L) r
  letI : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap q.ResidueField L (algebraMap R q.ResidueField x) =
      algebraMap q.ResidueField L (e.symm (algebraMap S r.ResidueField (algebraMap R S x)))
    congr 1
    apply e.injective
    rw [e.apply_symm_apply]
    exact Ideal.ResidueField.map_algebraMap q r (algebraMap R S) hq x
  let C := LocalCompletion (Localization.AtPrime P)
  let c := completedStalkTensorEquiv hsurj P Q hP
  let t := (Algebra.TensorProduct.cancelBaseChange R S L L C).symm.trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) c)
  exact regularNoetherian_of_ringEquiv t.symm.toRingEquiv (h L)

private theorem goodFormalFibre_polynomialDomain {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (P q : Ideal A[X]) [P.IsPrime] [q.IsPrime] (h0 : q.comap Polynomial.C = ⊥) :
    goodFormalFibre P q := by
  intro L _ _ _
  by_cases hq : q = ⊥
  · subst q
    let q : Ideal A[X] := ⊥
    let K := FractionRing A[X]
    let F := q.ResidueField
    let e : K ≃ₐ[A[X]] F := FractionRing.algEquiv A[X] F
    letI : Algebra A[X] L := testAlgebra (L := L) q
    letI : Algebra K F := e.toRingHom.toAlgebra
    letI : Algebra K L := ((algebraMap F L).comp e.toRingHom).toAlgebra
    letI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A[X] K L := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap F L _ = algebraMap F L (e (algebraMap A[X] K x))
      rw [e.commutes]
    letI : Module.Finite K F :=
      Module.Finite.of_surjective (Algebra.linearMap K F) e.surjective
    letI : Module.Finite K L := Module.Finite.trans F L
    exact regular_genericPolynomialFibre P L
  · exact regular_nonzeroPolynomialFibre P q hq h0 L

private theorem goodFormalFibre_polynomial {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    (P q : Ideal A[X]) [P.IsPrime] [q.IsPrime] (hqP : q ≤ P) :
    goodFormalFibre P q := by
  let a := q.comap Polynomial.C
  letI : a.IsPrime := Ideal.IsPrime.comap _
  let B := A ⧸ a
  letI : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk a) Ideal.Quotient.mk_surjective
  letI : IsAdicComplete (maximalIdeal B) B :=
    isAdicComplete_of_surjective_local (A := A) (B := B) Ideal.Quotient.mk_surjective
  let f : A[X] →+* B[X] := Polynomial.mapRingHom (Ideal.Quotient.mk a)
  letI : Algebra A[X] B[X] := f.toAlgebra
  have hf : Function.Surjective f := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ q := by
    change RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk a)) ≤ q
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
  let Q := P.map f
  let r := q.map f
  letI : Q.IsPrime := Ideal.map_isPrime_of_surjective hf (hker.trans hqP)
  letI : r.IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hP : P = Q.comap f := by rw [Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot,
      sup_of_le_left (hker.trans hqP)]
  have hr : q = r.comap f := by rw [Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot, sup_of_le_left hker]
  have h0 : r.comap Polynomial.C = ⊥ := by
    apply (Ideal.comap_injective_of_surjective (Ideal.Quotient.mk a) Ideal.Quotient.mk_surjective)
    rw [Ideal.comap_comap, ← Polynomial.mapRingHom_comp_C, ← Ideal.comap_comap, ← hr,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact goodFormalFibre_of_surjective hf P q Q r hP hr (goodFormalFibre_polynomialDomain Q r h0)

/-- Lemma 5.13. Polynomial rings over complete Noetherian local rings are G-rings. -/
theorem polynomial_isGRing_of_completeLocal :
    CommutativeAlgebraNotes.Excellence.Specs.polynomial_isGRing_of_completeLocalType.{u} := by
  intro A _ _ _ _ P _
  let R := A[X]
  let H := Localization.AtPrime P
  let C := LocalCompletion H
  letI : IsNoetherianRing C := P103.Ch07.CompletedNoetherian.completed_noetherian H (maximalIdeal H)
  change RegularMap H C (algebraMap H C)
  refine (regularMap_algebraMap_iff H C).mpr ⟨inferInstance, ?_⟩
  intro q _
  change GeometricallyRegular q.ResidueField (q.Fiber C)
  intro L _ _ _
  let q₀ := q.comap (algebraMap R H)
  letI : q₀.IsPrime := Ideal.IsPrime.comap _
  have hq₀ : q₀ ≤ P := by
    intro x hx
    by_contra h
    exact (‹q.IsPrime›.ne_top) (q.eq_top_of_isUnit_mem hx
      (IsLocalization.map_units H (⟨x, h⟩ : P.primeCompl)))
  let e : q₀.ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective (Ideal.ResidueField.map q₀ q (algebraMap R H) rfl)
      ((RingHom.surjectiveOnStalks_of_isLocalization P.primeCompl H).residueFieldMap_bijective
        q₀ q rfl)
  letI : Algebra q₀.ResidueField L := ((algebraMap q.ResidueField L).comp e.toRingHom).toAlgebra
  letI : Module.Finite q₀.ResidueField L :=
    Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl L) (by ext x; simp [RingHom.algebraMap_toAlgebra])
  letI : Algebra R L := testAlgebra (L := L) q₀
  letI : Algebra H L := testAlgebra (L := L) q
  letI : IsScalarTower H q.ResidueField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R H L := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap q.ResidueField L (e (algebraMap R q₀.ResidueField x)) = _
    rw [show e (algebraMap R q₀.ResidueField x) =
      algebraMap H q.ResidueField (algebraMap R H x) from
        Ideal.ResidueField.map_algebraMap q₀ q (algebraMap R H) rfl x]
    rfl
  let e₁ := Algebra.TensorProduct.equivOfCompatibleSMul H R L L C
  let e₂ := Algebra.TensorProduct.cancelBaseChange H q.ResidueField L L C
  exact regularNoetherian_of_ringEquiv (e₁.trans e₂.symm).toRingEquiv
    (goodFormalFibre_polynomial P q₀ hq₀ L)

end

end CommutativeAlgebraNotes.Excellence
