import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularBaseGenericFormalFibers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivationHypersurface
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivationsOfNonPowers
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.SeparableInseparableTower
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteAlgebraCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteDomainModels
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import Mathlib.RingTheory.TensorProduct.Finite

namespace CommutativeAlgebraNotes.Excellence

open scoped TensorProduct
open Algebra IsLocalRing
open CommutativeAlgebraNotes.Excellence.Specs (GenericFormalFiber)
open Algebra.TensorProduct (cancelBaseChange)

private theorem regularRing_of_equiv {A B : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] (e : A ≃+* B) (h : RegularRing A) : RegularRing B := by
  let : IsRegularRing A := (regularRing_iff A).mp h
  let : IsRegularRing B := IsRegularRing.of_ringEquiv e
  exact (regularRing_iff B).mpr inferInstance

private theorem regularRing_localization {R L : Type*} [CommRing R] [CommRing L]
    [Algebra R L] (U : Submonoid R) [IsLocalization U L]
    (hR : RegularRing R) : RegularRing L := by
  intro q hq
  let q₀ := q.comap (algebraMap R L)
  let : q₀.IsPrime := Ideal.IsPrime.comap _
  let : IsLocalization.AtPrime (Localization.AtPrime q) q₀ :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization U _ q
  let : IsRegularLocalRing (Localization.AtPrime q₀) := hR q₀
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q₀.primeCompl (Localization.AtPrime q₀)
      (Localization.AtPrime q)).toRingEquiv

private theorem scalarExtension_noetherian (K L T : Type*) [Field K] [Field L] [CommRing T]
    [Algebra K L] [Algebra K T] [Module.Finite K L] [IsNoetherianRing T] :
    IsNoetherianRing (L ⊗[K] T) := by
  let : IsNoetherianRing (T ⊗[K] L) := Algebra.FiniteType.isNoetherianRing T _
  exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm K T L).toRingEquiv

private theorem genericFormalFiber_regular (S K : Type*) [CommRing S] [IsDomain S]
    [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K]
    (hS : RegularRing S) (q : Ideal S) [q.IsPrime] :
    IsNoetherianRing (GenericFormalFiber S K q) ∧ RegularRing (GenericFormalFiber S K q) := by
  let A := Localization.AtPrime q
  let C := AdicCompletion (maximalIdeal A) A
  let : IsNoetherianRing C := P103.Ch07.CompletedNoetherian.completed_noetherian A (maximalIdeal A)
  let : Algebra C (K ⊗[S] C) := TensorProduct.rightAlgebra
  let U := Algebra.algebraMapSubmonoid C (nonZeroDivisors S)
  let : IsLocalization U (K ⊗[S] C) := IsLocalization.tensorRight (S := C) K (nonZeroDivisors S)
  exact ⟨IsLocalization.isNoetherianRing U _ inferInstance,
    regularRing_localization U (regularRing_completion A (hS q))⟩

/-- Generic formal fibres of regular Noetherian domains with characteristic-zero
fraction field are geometrically regular. -/
theorem regularBaseGenericFormalFiberCharZero (S K : Type*) [CommRing S] [IsDomain S]
    [IsNoetherianRing S] [Field K] [Algebra S K] [IsFractionRing S K] [CharZero K]
    (hS : RegularRing S) (q : Ideal S) [q.IsPrime] :
    GeometricallyRegular K (GenericFormalFiber S K q) := by
  obtain ⟨hN, hT⟩ := genericFormalFiber_regular S K hS q
  intro L _ _ _
  exact ⟨scalarExtension_noetherian K L _, regularRing_separableScalarExtension K L _ hT⟩


private noncomputable def productDerivation {ι : Type*} {A : ι → Type*}
    [∀ i, CommRing (A i)] (D : ∀ i, Derivation ℤ (A i) (A i)) :
    Derivation ℤ (∀ i, A i) (∀ i, A i) :=
  Derivation.mk' (LinearMap.pi fun i ↦ (D i).toLinearMap.comp (LinearMap.proj i))
    (fun x y ↦ funext fun i ↦ (D i).leibniz (x i) (y i))

private noncomputable def transportDerivation {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (D : Derivation ℤ B B) : Derivation ℤ A A :=
  let l := e.toIntAlgEquiv.toLinearEquiv
  Derivation.mk' (l.symm.toLinearMap.comp (D.toLinearMap.comp l.toLinearMap))
    (fun x y ↦ by
      change e.symm (D (e (x * y))) = x * e.symm (D (e y)) + y * e.symm (D (e x))
      rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        e.symm_apply_apply, e.symm_apply_apply])

open _root_.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion (PrimesOver Factor LocalCompletion)

-- Reuse the underlying additive map when the inferred ℤ-algebra changes.
private def rebaseIntDerivation {A : Type*} [CommRing A] {a b : Algebra ℤ A}
    (D : @Derivation ℤ A A _ _ _ a _ _) : @Derivation ℤ A A _ _ _ b _ _ :=
  let l := @Derivation.toLinearMap ℤ A A _ _ _ a _ _ D
  let l' := @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) A A _ _ b.toModule
    (AddCommGroup.toIntModule A) ⟨l.toFun, l.map_add'⟩ (by
      intro n x
      have h : a = b := Subsingleton.elim _ _
      subst b
      exact @LinearMap.map_smul' ℤ ℤ _ _ (RingHom.id ℤ) A A _ _ a.toModule
        (AddCommGroup.toIntModule A) l n x)
  @Derivation.mk ℤ A A _ _ _ b _ _ l'
    (@Derivation.map_one_eq_zero' ℤ A A _ _ _ a _ _ D)
    (@Derivation.leibniz' ℤ A A _ _ _ a _ _ D)

private noncomputable def completedPrimeDerivation {B : Type*} [CommRing B]
    (q : Ideal B) [q.IsPrime] (D : Derivation ℤ B B) :
    Derivation ℤ (LocalCompletion (Localization.AtPrime q))
      (LocalCompletion (Localization.AtPrime q)) :=
  rebaseIntDerivation (adicCompletionDerivation
    (localizationDerivation (L := Localization.AtPrime q) q.primeCompl D)
    (maximalIdeal (Localization.AtPrime q)))

private theorem completedPrimeDerivation_algebraMap {B : Type*} [CommRing B]
    (q : Ideal B) [q.IsPrime] (D : Derivation ℤ B B) (b : B) :
    completedPrimeDerivation q D (algebraMap B (LocalCompletion (Localization.AtPrime q)) b) =
      algebraMap B (LocalCompletion (Localization.AtPrime q)) (D b) := by
  change adicCompletionDerivation (localizationDerivation q.primeCompl D)
    (maximalIdeal (Localization.AtPrime q))
    (algebraMap B (LocalCompletion (Localization.AtPrime q)) b) = _
  rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime q) _, adicCompletionDerivation_algebraMap,
    localizationDerivation_algebraMap, ← IsScalarTower.algebraMap_apply]

set_option maxHeartbeats 800000 in
private theorem derivation_on_extendedFiber {S B M : Type*} [CommRing S] [CommRing B]
    [Field M] [Algebra S B] [Algebra B M] [Algebra S M] [IsScalarTower S B M]
    [IsDomain B] [IsFractionRing B M] [Module.Finite S B]
    [IsNoetherianRing S] [IsNoetherianRing B] (q : Ideal S) [q.IsPrime]
    (D : Derivation ℤ B B) (f : B) (hf : D f ≠ 0) :
    ∃ δ : Derivation ℤ (GenericFormalFiber S M q) (GenericFormalFiber S M q),
      IsUnit (δ (algebraMap M (GenericFormalFiber S M q) (algebraMap B M f))) := by
  let C := LocalCompletion (Localization.AtPrime q)
  let P := (i : PrimesOver q B) → Factor q i
  let DP : Derivation ℤ P P := rebaseIntDerivation
    (productDerivation (A := fun i ↦ Factor q i)
      (fun i ↦ rebaseIntDerivation (completedPrimeDerivation i.1.asIdeal D)))
  have hDP (b : B) : DP (algebraMap B P b) = algebraMap B P (D b) := by
    funext i
    exact completedPrimeDerivation_algebraMap i.1.asIdeal D b
  let e₀ : (B ⊗[S] C) ≃+* P :=
    (Algebra.TensorProduct.comm S B C).toRingEquiv.trans
      (FiniteAlgebraCompletion.decomposition (B := B) q).toRingEquiv
  let e₁ : (B ⊗[S] C) ≃ₐ[B] P := AlgEquiv.ofRingEquiv (f := e₀) (by
    intro b
    funext i
    exact FiniteAlgebraCompletion.decomposition_one_tmul q b i)
  let e : GenericFormalFiber S M q ≃ₐ[M] (M ⊗[B] P) :=
    (cancelBaseChange S B M M C).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[M] M) e₁)
  let : Algebra P (M ⊗[B] P) := Algebra.TensorProduct.rightAlgebra
  let U := Algebra.algebraMapSubmonoid P (nonZeroDivisors B)
  let : IsLocalization U (M ⊗[B] P) := IsLocalization.tensorRight (S := P) M (nonZeroDivisors B)
  let DU : Derivation ℤ (M ⊗[B] P) (M ⊗[B] P) := rebaseIntDerivation (localizationDerivation U (rebaseIntDerivation DP))
  refine ⟨rebaseIntDerivation (transportDerivation e.toRingEquiv (rebaseIntDerivation DU)), ?_⟩
  change IsUnit (e.symm (DU (e (algebraMap M _ (algebraMap B M f)))))
  have hDU (b : B) : DU (algebraMap P (M ⊗[B] P) (algebraMap B P b)) =
      algebraMap P (M ⊗[B] P) (DP (algebraMap B P b)) :=
    localizationDerivation_algebraMap U (rebaseIntDerivation DP) (algebraMap B P b)
  rw [e.commutes, ← IsScalarTower.algebraMap_apply B M (M ⊗[B] P),
    IsScalarTower.algebraMap_apply B P (M ⊗[B] P), hDU, hDP,
    ← IsScalarTower.algebraMap_apply B P (M ⊗[B] P),
    IsScalarTower.algebraMap_apply B M (M ⊗[B] P)]
  exact ((isUnit_iff_ne_zero.mpr (fun he ↦ hf ((IsFractionRing.injective B M) (he.trans (map_zero _).symm)))).map
    (algebraMap M (M ⊗[B] P))).map e.symm.toRingEquiv.toRingHom


open Polynomial in
private noncomputable def tensorBinomialEquiv {M T : Type*} [Field M] [CommRing T]
    [Algebra M T] (p : ℕ) (a : M) :
    T ⊗[M] AdjoinRoot (X ^ p - C a) ≃+* AdjoinRoot (X ^ p - C (algebraMap M T a)) := by
  let h : M[X] := X ^ p - C a
  let h' : (T ⊗[M] M)[X] := X ^ p - C (1 ⊗ₜ[M] a)
  let eTensor : (T ⊗[M] AdjoinRoot h) ≃ₐ[T] AdjoinRoot h' :=
    AdjoinRoot.tensorAlgEquiv h h' (by simp [h, h'])
  let eCoeff := (Algebra.TensorProduct.rid M T T).toRingEquiv
  let eQuot : AdjoinRoot h' ≃+* AdjoinRoot (X ^ p - C (algebraMap M T a)) :=
    AdjoinRoot.mapRingEquiv eCoeff h' _ (by
      apply Associated.of_eq
      simp [h', eCoeff, Algebra.TensorProduct.rid_tmul, Algebra.smul_def])
  exact eTensor.toRingEquiv.trans eQuot

open Polynomial in
private theorem regularRing_tensor_of_scaledBinomial {M N T : Type*} [Field M] [Field N]
    [CommRing T] [Algebra M N] [Algebra M T] [IsNoetherianRing T]
    (p : ℕ) (hp : 1 ≤ p) (a c : M) (hc : c ≠ 0)
    (eN : AdjoinRoot (X ^ p - C a) ≃ₐ[M] N) (hT : RegularRing T)
    (D : Derivation ℤ T T) (hD : IsUnit (D (algebraMap M T (c ^ p * a)))) :
    RegularRing (N ⊗[M] T) := by
  obtain ⟨eScale, _⟩ := exists_scaled_adjoin_root_equiv M p a c hc
  let eRoot := eScale.trans eN
  let e :=
    ((Algebra.TensorProduct.comm M N T).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[M] T) eRoot.symm)).toRingEquiv.trans
        (tensorBinomialEquiv (T := T) p (c ^ p * a))
  exact regularRing_of_equiv e.symm
    (regularRing_quotient_X_pow_sub_C_of_isUnit_derivation hT D _ hD p hp)

section PositiveCharacteristic

open Polynomial IntermediateField

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r s : ℕ)

local notation "S₀" => CoefficientTowerBase k r s
local notation "K₀" => FractionRing S₀

private theorem nonpower_derivation {B M : Type*} [CommRing B] [IsDomain B]
    [Algebra S₀ B] [Algebra.FiniteType S₀ B] [Field M] [Algebra B M] [IsFractionRing B M]
    [Algebra S₀ M] [Algebra K₀ M] [IsScalarTower S₀ B M] [IsScalarTower S₀ K₀ M]
    [Module.Finite K₀ M] (f : B) (h : ¬ ∃ x : M, x ^ p = algebraMap B M f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := by
  have hSM : Function.Injective (algebraMap S₀ M) := by
    rw [IsScalarTower.algebraMap_eq S₀ K₀ M]
    exact (algebraMap K₀ M).injective.comp (IsFractionRing.injective S₀ K₀)
  have hSB : Function.Injective (algebraMap S₀ B) := by
    intro x y he
    apply hSM
    rw [IsScalarTower.algebraMap_apply S₀ B M, IsScalarTower.algebraMap_apply S₀ B M, he]
  let φ := IsFractionRing.lift (K := K₀) (g := (algebraMap B M).comp (algebraMap S₀ B))
    ((IsFractionRing.injective B M).comp hSB)
  have hφ : φ = algebraMap K₀ M :=
    IsFractionRing.lift_unique _ (fun x ↦ by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply S₀ B M,
        ← IsScalarTower.algebraMap_apply S₀ K₀ M])
  have hAlgebra : φ.toAlgebra = ‹Algebra K₀ M› :=
    Algebra.algebra_ext _ _ (fun x ↦ DFunLike.congr_fun hφ x)
  have hfin : @Module.Finite K₀ M _ _ φ.toAlgebra.toModule := hAlgebra.symm ▸ inferInstance
  have hDetect := exists_derivation_ne_zero_of_not_pth_power
  unfold _root_.Specs.CommutativeAlgebraNotes.DerivationsOfNonPowers.DerivationsDetectNonPowers
    at hDetect
  exact @hDetect k _ p _ _ r s B _ _ _ _ hSB M _ _ _ hfin f h

set_option maxHeartbeats 1000000 in
/-- The inseparable binomial stays regular after scalar extension of the fibre. -/
private theorem regularRing_inseparableStep
    (q : Ideal S₀) [q.IsPrime] [IsNoetherianRing S₀]
    (M : Type*) [Field M] [Algebra K₀ M] [Module.Finite K₀ M]
    [Algebra S₀ M] [IsScalarTower S₀ K₀ M]
    (N : Type*) [Field N] [Algebra M N]
    (a : M) (ha : ¬ ∃ x : M, x ^ p = a)
    (eN : AdjoinRoot (X ^ p - C a) ≃ₐ[M] N)
    [IsNoetherianRing (GenericFormalFiber S₀ M q)] (hT : RegularRing (GenericFormalFiber S₀ M q)) :
    RegularRing (N ⊗[M] GenericFormalFiber S₀ M q) := by
  let T := GenericFormalFiber S₀ M q
  have hp := (Fact.out : p.Prime)
  obtain ⟨B, hB, hfinB, hfrac⟩ := exists_finite_domain_model S₀ K₀ M
  let : IsNoetherianRing B := IsNoetherianRing.of_finite S₀ B
  obtain ⟨c, hc, hf⟩ := exists_pow_mul_mem B a p hp.pos
  let f : B := ⟨_, hf⟩
  have hcM : algebraMap B M c ≠ 0 := fun h ↦ hc ((IsFractionRing.injective B M) (h.trans (map_zero _).symm))
  have hf' : algebraMap B M f = (algebraMap B M c) ^ p * a := rfl
  have hnonpower : ¬ ∃ x : M, x ^ p = algebraMap B M f := by
    rintro ⟨x, hx⟩
    refine ha ⟨x / algebraMap B M c, ?_⟩
    rw [div_pow, hx, hf', mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hcM)]
  obtain ⟨D, hD⟩ := nonpower_derivation k p r s (B := B) (M := M) f hnonpower
  obtain ⟨δ, hδ⟩ := derivation_on_extendedFiber (S := S₀) (B := B) (M := M) q D f hD
  refine regularRing_tensor_of_scaledBinomial (T := T) p hp.one_le a
    (algebraMap B M c) hcM eN hT (rebaseIntDerivation δ) ?_
  change IsUnit (δ (algebraMap M T ((algebraMap B M c) ^ p * a)))
  rw [← hf']
  exact hδ

private theorem extendedGenericFormalFiber_noetherian (q : Ideal S₀) [q.IsPrime]
    (M : Type*) [Field M] [Algebra K₀ M] [Module.Finite K₀ M]
    [Algebra S₀ M] [IsScalarTower S₀ K₀ M] [IsNoetherianRing (GenericFormalFiber S₀ K₀ q)] :
    IsNoetherianRing (GenericFormalFiber S₀ M q) := by
  let : IsNoetherianRing (M ⊗[K₀] GenericFormalFiber S₀ K₀ q) :=
    scalarExtension_noetherian K₀ M (GenericFormalFiber S₀ K₀ q)
  exact isNoetherianRing_of_ringEquiv _
    (cancelBaseChange S₀ K₀ M M (LocalCompletion (Localization.AtPrime q))).toRingEquiv

set_option maxHeartbeats 1000000 in
private theorem regularRing_simpleFieldStep (q : Ideal S₀) [q.IsPrime] [IsNoetherianRing S₀]
    [IsNoetherianRing (GenericFormalFiber S₀ K₀ q)]
    {L : Type*} [Field L] [Algebra K₀ L] [Module.Finite K₀ L]
    [Algebra S₀ L] [IsScalarTower S₀ K₀ L] [CharP K₀ p]
    (M N : IntermediateField K₀ L) (h : IsSimpleFieldStep p M N)
    (hM : RegularRing (GenericFormalFiber S₀ M q)) : RegularRing (GenericFormalFiber S₀ N q) := by
  obtain ⟨b, rfl, hb, hbp⟩ := h
  let : IsScalarTower S₀ M L := IsScalarTower.of_algebraMap_eq (fun x ↦ by
    rw [IsScalarTower.algebraMap_apply S₀ K₀ M, ← IsScalarTower.algebraMap_apply K₀ M L,
      ← IsScalarTower.algebraMap_apply S₀ K₀ L])
  let N' := IntermediateField.adjoin M ({b} : Set L)
  let T := GenericFormalFiber S₀ M q
  let : IsNoetherianRing T := extendedGenericFormalFiber_noetherian k r s q M
  have hInt : IsIntegral M b := IsIntegral.of_finite M b
  let : Module.Finite M N' := IntermediateField.adjoin.finiteDimensional hInt
  have hN : RegularRing (N' ⊗[M] T) := by
    rcases hbp with hs | hpow
    · let : Algebra.IsSeparable M N' := (isSeparable_adjoin_simple_iff_isSeparable M L).mpr hs
      exact regularRing_separableScalarExtension M N' T hM
    · let a : M := ⟨b ^ p, hpow⟩
      have hp := (Fact.out : p.Prime)
      let : CharP L p := charP_of_injective_algebraMap (algebraMap K₀ L).injective p
      have ha : ¬ ∃ x : M, x ^ p = a := by
        rintro ⟨x, hx⟩
        have he : (x : L) = b := frobenius_inj L p
          (show (x : L) ^ p = b ^ p from congrArg ((↑) : M → L) hx)
        exact hb (he ▸ x.property)
      have hm := minpoly_eq_X_pow_sub_C_of_pow_mem K₀ L p hp M b a hb rfl
      let eN : AdjoinRoot (X ^ p - C a) ≃ₐ[M] N' :=
        (AdjoinRoot.algEquivOfEq M _ _ hm.symm).trans (adjoinRootEquivAdjoin M hInt)
      exact regularRing_inseparableStep k p r s q M N' a ha eN hM
  let : IsNoetherianRing (N' ⊗[M] T) := scalarExtension_noetherian M N' T
  change RegularRing (GenericFormalFiber S₀ N' q)
  exact regularRing_of_equiv
    (cancelBaseChange S₀ M N' N' (LocalCompletion (Localization.AtPrime q))).toRingEquiv hN

include p in
set_option maxHeartbeats 1000000 in
/-- Generic formal fibres of a finite-variable polynomial ring over a
finite-variable power-series ring over a field of positive characteristic. -/
theorem regularBaseGenericFormalFiberCharP (q : Ideal S₀) [q.IsPrime] :
    GeometricallyRegular K₀ (GenericFormalFiber S₀ K₀ q) := by
  let : IsRegularLocalRing (MvPowerSeries (Fin r) k) :=
    (CompleteRegularPowerSeries.overField k r).2.1
  have hS : RegularRing S₀ := regularRing_mvPolynomial _ _
    (AdvCommAlg.CohenMacaulay.regularLocal_localization_atPrime _)
  obtain ⟨hN, hT⟩ := genericFormalFiber_regular S₀ K₀ hS q
  let Completion := LocalCompletion (Localization.AtPrime q)
  intro L _ _ _
  refine ⟨scalarExtension_noetherian K₀ L (GenericFormalFiber S₀ K₀ q), ?_⟩
  let : Algebra S₀ L := ((algebraMap K₀ L).comp (algebraMap S₀ K₀)).toAlgebra
  let : IsScalarTower S₀ K₀ L := IsScalarTower.of_algebraMap_eq' rfl
  let : CharP K₀ p := charP_of_injective_algebraMap (IsFractionRing.injective S₀ K₀) p
  have hbot : RegularRing (GenericFormalFiber S₀ (⊥ : IntermediateField K₀ L) q) :=
    regularRing_of_equiv (Algebra.TensorProduct.congr
      ((IntermediateField.botEquiv K₀ L).symm.restrictScalars S₀)
      (AlgEquiv.refl : Completion ≃ₐ[S₀] Completion)).toRingEquiv hT
  have tower := finiteExtension_has_simpleTower K₀ L p (Fact.out : p.Prime)
  have hAll {N : IntermediateField K₀ L}
      (h : Relation.ReflTransGen (IsSimpleFieldStep p) ⊥ N) :
      RegularRing (GenericFormalFiber S₀ N q) := by
    induction h with
    | refl => exact hbot
    | tail _ h ih => exact regularRing_simpleFieldStep k p r s q _ _ h ih
  have htop := hAll tower
  let : IsNoetherianRing (GenericFormalFiber S₀ (⊤ : IntermediateField K₀ L) q) :=
    extendedGenericFormalFiber_noetherian k r s q _
  let eTop : GenericFormalFiber S₀ (⊤ : IntermediateField K₀ L) q ≃ₐ[S₀]
      GenericFormalFiber S₀ L q :=
    Algebra.TensorProduct.congr ((IntermediateField.topEquiv (F := K₀) (E := L)).restrictScalars S₀)
      (AlgEquiv.refl : Completion ≃ₐ[S₀] Completion)
  exact regularRing_of_equiv
    (eTop.toRingEquiv.trans (cancelBaseChange S₀ K₀ L L Completion).symm.toRingEquiv) htop

end PositiveCharacteristic

end CommutativeAlgebraNotes.Excellence
