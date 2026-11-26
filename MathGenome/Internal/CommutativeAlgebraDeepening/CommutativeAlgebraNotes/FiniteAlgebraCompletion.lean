import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

open scoped TensorProduct
open Ideal IsLocalRing TensorProduct AdicCompletion
open Specs.CommutativeAlgebraNotes.FiniteAlgebraCompletion

namespace CommutativeAlgebraNotes.FiniteAlgebraCompletion

universe u v

theorem finitePrimes : FinitePrimes.{u, v} := by
  intro A B _ _ _ _ p _
  let : IsArtinianRing (p.Fiber B) := isArtinian_of_tower p.ResidueField inferInstance
  let e := PrimeSpectrum.preimageHomeomorphFiber A B ⟨p, inferInstance⟩
  refine Finite.of_injective (fun q : PrimesOver p B ↦ e ⟨q.1, ?_⟩) ?_
  · exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext q.2)
  · intro q q' h
    have hval := congrArg (fun x ↦ x.1) (e.injective h)
    exact Subtype.ext hval

section Product

variable {S ι : Type*} [CommRing S] {T : ι → Type*} [∀ i, CommRing (T i)]
variable (I : Ideal S) (J : ∀ i, Ideal (T i)) (f : ∀ i, S →+* T i)
variable (hf : ∀ i, I.map (f i) ≤ J i)

/-- Surjective simultaneous approximations with cofinal kernels identify the inverse limits. -/
private theorem completionProduct_bijective
    (hsurj : ∀ n : ℕ, Function.Surjective (fun s : S ↦ fun i ↦
      Ideal.Quotient.mk (J i ^ n) (f i s)))
    (k : ℕ → ℕ) (hk : Monotone k) (hkn : ∀ n, n ≤ k n)
    (hker : ∀ n, ∀ s : S, (∀ i, f i s ∈ J i ^ k n) → s ∈ I ^ n) :
    Function.Bijective (fun x : AdicCompletion I S ↦ fun i ↦
      completionMap I (J i) (f i) (hf i) x) := by
  have hsub {n : ℕ} {a b : S}
      (e : ∀ i, Ideal.Quotient.mk (J i ^ k n) (f i a) =
        Ideal.Quotient.mk (J i ^ k n) (f i b)) :
      Ideal.Quotient.mk (I ^ n) a = Ideal.Quotient.mk (I ^ n) b := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).2
    apply hker
    intro i
    rw [map_sub]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 (e i)
  constructor
  · intro x y hxy
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (k n) x)
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (k n) y)
    have hh (i : ι) := congrArg (fun z : (i : ι) → AdicCompletion (J i) (T i) ↦
      AdicCompletion.evalₐ (J i) (k n) (z i)) hxy
    have he : ∀ i, Ideal.Quotient.mk (J i ^ k n) (f i a) =
        Ideal.Quotient.mk (J i ^ k n) (f i b) := by
      intro i
      simpa only [eval_completionMap, ← ha, ← hb, quotientPowMap_mk] using hh i
    rw [← factorPow_eval I x (hkn n), ← factorPow_eval I y (hkn n), ← ha, ← hb]
    exact hsub he
  · intro y
    choose a ha using fun n : ℕ ↦ hsurj (k n) (fun i ↦ AdicCompletion.evalₐ (J i) (k n) (y i))
    have ha' (n : ℕ) (i : ι) :
        Ideal.Quotient.mk (J i ^ k n) (f i (a n)) = AdicCompletion.evalₐ (J i) (k n) (y i) :=
      congrFun (ha n) i
    let c : AdicCauchySequence I S := ⟨a, by
      intro m n hmn
      change ((Submodule.Quotient.mk (p := I ^ m • ⊤)) (a m)) =
        Submodule.Quotient.mk (a n)
      rw [show (I ^ m • ⊤ : Ideal S) = I ^ m from Ideal.mul_top _]
      apply hsub
      intro i
      have h := congrArg (Ideal.Quotient.factorPow (J i) (hk hmn)) (ha' n i)
      exact (ha' m i).trans ((factorPow_eval (J i) (y i) (hk hmn)).symm.trans h.symm)⟩
    refine ⟨AdicCompletion.mk I S c, funext fun i ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_⟩
    rw [eval_completionMap, AdicCompletion.evalₐ_mk, quotientPowMap_mk]
    have h := congrArg (Ideal.Quotient.factorPow (J i) (hkn n)) (ha' n i)
    exact h.trans (factorPow_eval (J i) (y i) (hkn n))

end Product

section Tensor

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

local notation "J" => Ideal.map (algebraMap R S) I

private def completionQuotientEquiv (n : ℕ) :
    (S ⧸ (I ^ n • ⊤ : Submodule R S)) ≃+
      (S ⧸ (J ^ n • ⊤ : Ideal S)) :=
  (Submodule.quotEquivOfEq _ _ (show (I ^ n • ⊤ : Submodule R S) =
    (J ^ n • ⊤ : Ideal S).restrictScalars R by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow, Ideal.smul_top_eq_map])).toAddEquiv.trans
    (Submodule.Quotient.restrictScalarsEquiv R (J ^ n • ⊤ : Ideal S)).toAddEquiv

private lemma completionQuotientEquiv_mk (n : ℕ) (x : S) :
    completionQuotientEquiv (S := S) I n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := rfl

private lemma completionQuotientEquiv_transition {m n : ℕ} (hmn : m ≤ n)
    (x : S ⧸ (I ^ n • ⊤ : Submodule R S)) :
    transitionMap J S hmn (completionQuotientEquiv I n x) =
      completionQuotientEquiv I m (transitionMap I S hmn x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private def toRingCompletion : AdicCompletion I S →+ AdicCompletion J S where
  toFun x := ⟨fun n ↦ completionQuotientEquiv I n (x.val n), fun hmn ↦ by
    rw [completionQuotientEquiv_transition, x.property hmn]⟩
  map_zero' := Subtype.ext (funext fun n ↦ map_zero (completionQuotientEquiv I n))
  map_add' x y := Subtype.ext (funext fun n ↦
    map_add (completionQuotientEquiv I n) (x.val n) (y.val n))

private lemma toRingCompletion_bijective :
    Function.Bijective (toRingCompletion (S := S) I) := by
  constructor
  · intro x y h
    exact Subtype.ext (funext fun n ↦ (completionQuotientEquiv I n).injective
      (congrArg (fun z : AdicCompletion J S ↦ z.val n) h))
  · intro y
    refine ⟨⟨fun n ↦ (completionQuotientEquiv I n).symm (y.val n), ?_⟩, ?_⟩
    · intro m n hmn
      apply (completionQuotientEquiv I m).injective
      rw [← completionQuotientEquiv_transition I hmn, AddEquiv.apply_symm_apply,
        AddEquiv.apply_symm_apply, y.property hmn]
    · exact Subtype.ext (funext fun n ↦ AddEquiv.apply_symm_apply _ _)

private noncomputable def tensorCompletion : (AdicCompletion I R ⊗[R] S) →ₐ[R]
    AdicCompletion J S :=
  Algebra.TensorProduct.lift
    { __ := completionMap I J (algebraMap R S) le_rfl
      commutes' r := completionMap_of I J _ le_rfl r }
    (Algebra.ofId S (AdicCompletion J S) |>.restrictScalars R)
    (fun _ _ ↦ Commute.all _ _)

private lemma tensorCompletion_tmul (x : AdicCompletion I R) (y : S) :
    tensorCompletion I (x ⊗ₜ[R] y) =
      completionMap I J (algebraMap R S) le_rfl x * AdicCompletion.of J S y :=
  rfl

private lemma tensorCompletion_eq (x : AdicCompletion I R ⊗[R] S) :
    tensorCompletion I x = toRingCompletion I (AdicCompletion.ofTensorProduct I S x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [tensorCompletion_tmul, map_mul, eval_completionMap, evalₐ_of, evalₐ_mk,
      quotientPowMap_mk, ← map_mul, AdicCompletion.ofTensorProduct_tmul,
      ← AdicCompletion.factor_eval_eq_evalₐ J _ (le_of_eq (Ideal.mul_top _))]
    change Ideal.Quotient.mk (J ^ n) (algebraMap R S (a.val n) * y) =
      Ideal.Quotient.factor (show (J ^ n • ⊤ : Ideal S) ≤ J ^ n from Ideal.mul_le_left)
        (completionQuotientEquiv I n
        ((AdicCompletion.mk I R a • AdicCompletion.of I S y).val n))
    rw [AdicCompletion.smul_eval]
    change _ = Ideal.Quotient.factor (show (J ^ n • ⊤ : Ideal S) ≤ J ^ n from Ideal.mul_le_left)
        (completionQuotientEquiv I n
      (Ideal.Quotient.mk (I ^ n • ⊤) (a.val n) • Submodule.Quotient.mk y))
    rw [AdicCompletion.mk_smul_mk, ← Submodule.Quotient.mk_smul, completionQuotientEquiv_mk]
    exact congrArg (Ideal.Quotient.mk (J ^ n)) (Algebra.smul_def (a.val n) y).symm

/-- Transport the finite-module comparison through a finite free presentation,
so the ring and the module can belong to different universes. -/
private lemma ofTensorProduct_bijective {M : Type v} [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (AdicCompletion.ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := LinearMap.quotKerEquivOfSurjective f hf
  let upper := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (AdicCompletion I R) (AdicCompletion I R)) e
  let lower := AdicCompletion.congr I e
  have naturality : (AdicCompletion.ofTensorProduct I M) ∘ upper =
      lower ∘ AdicCompletion.ofTensorProduct I ((Fin n → R) ⧸ LinearMap.ker f) := by
    funext x
    exact (LinearMap.congr_fun (AdicCompletion.ofTensorProduct_naturality I e.toLinearMap) x).symm
  have h : Function.Bijective ((AdicCompletion.ofTensorProduct I M) ∘ upper) := by
    rw [naturality]
    exact lower.bijective.comp
      (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I _)
  convert h.comp upper.symm.bijective using 1
  funext x
  exact congrArg (AdicCompletion.ofTensorProduct I M) (upper.apply_symm_apply x).symm

private lemma tensorCompletion_bijective [IsNoetherianRing R] [Module.Finite R S] :
    Function.Bijective (tensorCompletion (S := S) I) := by
  rw [show ⇑(tensorCompletion (S := S) I) =
      toRingCompletion I ∘ AdicCompletion.ofTensorProduct I S from funext (tensorCompletion_eq I)]
  exact (toRingCompletion_bijective I).comp
    (ofTensorProduct_bijective I)

end Tensor

section Localization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (p : Ideal A) [p.IsPrime]

local notation "Aₚ" => Localization.AtPrime p
local notation "Uₚ" => Algebra.algebraMapSubmonoid B p.primeCompl
local notation "Bₚ" => Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
local notation "𝔪" => maximalIdeal (Localization.AtPrime p)
local notation "𝔞" => Ideal.map
  (algebraMap (Localization.AtPrime p) (Localization (Algebra.algebraMapSubmonoid B p.primeCompl)))
  (maximalIdeal (Localization.AtPrime p))

private abbrev extendedPrime (q : PrimesOver p B) : Ideal Bₚ :=
  q.1.asIdeal.map (algebraMap B Bₚ)

private instance extendedPrime_isPrime (q : PrimesOver p B) :
    (extendedPrime p q).IsPrime :=
  IsLocalization.AtPrime.isPrime_map_of_liesOver B p Bₚ q.1.asIdeal

private instance extendedPrime_liesOver (q : PrimesOver p B) :
    (extendedPrime p q).LiesOver 𝔪 :=
  IsLocalization.AtPrime.liesOver_map_of_liesOver p Aₚ Bₚ q.1.asIdeal

private lemma comap_extendedPrime (q : PrimesOver p B) :
    (extendedPrime p q).comap (algebraMap B Bₚ) = q.1.asIdeal :=
  IsLocalization.under_map_of_isPrime_disjoint Uₚ Bₚ inferInstance
    (Ideal.disjoint_primeCompl_of_liesOver q.1.asIdeal p)

private lemma primeCompl_le (q : PrimesOver p B) : Uₚ ≤ q.1.asIdeal.primeCompl :=
  fun _ h ↦ Set.disjoint_left.mp (Ideal.disjoint_primeCompl_of_liesOver q.1.asIdeal p) h

private noncomputable instance localizedAlgebra (q : PrimesOver p B) :
    Algebra Bₚ (Localization.AtPrime q.1.asIdeal) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe Bₚ _ Uₚ q.1.asIdeal.primeCompl (primeCompl_le p q)

private instance localizedTower (q : PrimesOver p B) :
    IsScalarTower B Bₚ (Localization.AtPrime q.1.asIdeal) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le Bₚ _ Uₚ q.1.asIdeal.primeCompl
    (primeCompl_le p q)

private instance localizedAtPrime (q : PrimesOver p B) :
    IsLocalization.AtPrime (Localization.AtPrime q.1.asIdeal) (extendedPrime p q) := by
  let T := Localization.AtPrime q.1.asIdeal
  let N := q.1.asIdeal.primeCompl
  have := IsLocalization.isLocalization_of_submonoid_le Bₚ T Uₚ N (primeCompl_le p q)
  apply IsLocalization.isLocalization_of_is_exists_mul_mem (S := T) (N.map (algebraMap B Bₚ))
  · rintro _ ⟨b, hb, rfl⟩
    intro hb'
    apply hb
    change b ∈ Ideal.comap (algebraMap B Bₚ) (extendedPrime p q) at hb'
    rwa [comap_extendedPrime] at hb'
  · intro x
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj Uₚ (x : Bₚ)
    refine ⟨algebraMap B Bₚ s, b, ?_, ?_⟩
    · intro hb
      have hb' := Ideal.mem_map_of_mem (algebraMap B Bₚ) hb
      change (x : Bₚ) * algebraMap B Bₚ s = algebraMap B Bₚ b at hs
      rw [← hs] at hb'
      have hprime : (extendedPrime p q).IsPrime := inferInstance
      exact (hprime.mul_mem_iff_mem_or_mem.mp hb').elim x.prop
        (fun h ↦ hprime.ne_top ((extendedPrime p q).eq_top_of_isUnit_mem h
          (IsLocalization.map_units Bₚ s)))
    · exact hs.symm.trans (mul_comm _ _)

private lemma baseMap_eq (q : PrimesOver p B) :
    (algebraMap Bₚ (Localization.AtPrime q.1.asIdeal)).comp (algebraMap Aₚ Bₚ) =
      algebraMap Aₚ (Localization.AtPrime q.1.asIdeal) := by
  apply IsLocalization.ringHom_ext p.primeCompl
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A Aₚ Bₚ,
    IsScalarTower.algebraMap_eq A B Bₚ, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq B Bₚ, ← IsScalarTower.algebraMap_eq A B,
    ← IsScalarTower.algebraMap_eq A Aₚ]

private lemma map_extended_maximal_le (q : PrimesOver p B) :
    Ideal.map (algebraMap Bₚ (Localization.AtPrime q.1.asIdeal)) 𝔞 ≤
      maximalIdeal (Localization.AtPrime q.1.asIdeal) := by
  rw [Ideal.map_map, baseMap_eq]
  exact map_maximal_le p q

variable [Module.Finite A B]

private instance extendedPrime_isMaximal (q : PrimesOver p B) :
    (extendedPrime p q).IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ (by
    rw [← Ideal.over_def (extendedPrime p q) 𝔪]
    infer_instance)

omit [Module.Finite A B] in
private lemma extendedPrime_injective :
    Function.Injective (extendedPrime (B := B) p) := by
  intro q q' h
  apply Subtype.ext
  apply PrimeSpectrum.ext
  rw [← comap_extendedPrime p q, ← comap_extendedPrime p q', h]

private lemma extendedPrime_surjective_maximal {P : Ideal Bₚ} [P.IsMaximal] :
    ∃ q : PrimesOver p B, extendedPrime p q = P := by
  have h := IsLocalization.AtPrime.mem_primesOver_of_isPrime (Rₚ := Aₚ) (Q := P)
  let : P.LiesOver 𝔪 := h.2
  have hp := IsLocalization.AtPrime.liesOver_comap_of_liesOver (S := B) p Aₚ P
  exact ⟨⟨⟨P.comap (algebraMap B Bₚ), Ideal.IsPrime.under B P⟩, hp.over.symm⟩,
    IsLocalization.map_under Uₚ Bₚ P⟩

private lemma radical_eq_iInf :
    Ideal.radical 𝔞 = ⨅ q : PrimesOver p B, extendedPrime p q := by
  rw [Ideal.radical_eq_sInf]
  apply le_antisymm
  · refine le_iInf fun q ↦ sInf_le ⟨?_, inferInstance⟩
    exact Ideal.map_le_iff_le_comap.mpr (Ideal.over_def (extendedPrime p q) 𝔪).le
  · refine le_sInf fun P hP ↦ ?_
    let : P.IsPrime := hP.2
    have hPm : P.under Aₚ = 𝔪 :=
      le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.under Aₚ P).ne_top)
        (Ideal.map_le_iff_le_comap.mp hP.1)
    have hmax : (P.under Aₚ).IsMaximal := by rw [hPm]; infer_instance
    let : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under P hmax
    obtain ⟨q, rfl⟩ := extendedPrime_surjective_maximal (p := p) (P := P)
    exact iInf_le _ q

private lemma extendedPrime_pairwise :
    Pairwise (Function.onFun IsCoprime (extendedPrime (B := B) p)) := by
  intro q q' ne
  exact Ideal.isCoprime_of_isMaximal (I := extendedPrime p q) (J := extendedPrime p q')
    (fun h ↦ ne (extendedPrime_injective p h))

private lemma iInf_extendedPrime_pow (n : ℕ) [Finite (PrimesOver p B)] :
    (⨅ q : PrimesOver p B, extendedPrime p q ^ n) =
      (⨅ q : PrimesOver p B, extendedPrime p q) ^ n := by
  classical
  let := Fintype.ofFinite (PrimesOver p B)
  have eq (a : ℕ) : (∏ q, extendedPrime p q ^ a) =
      ⨅ q : PrimesOver p B, extendedPrime p q ^ a := by
    rw [← iInf_univ, ← Finset.coe_univ]
    exact Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (fun q _ q' _ ne ↦ (extendedPrime_pairwise p ne).pow)
  have eq' : (∏ q, extendedPrime p q) = ⨅ q : PrimesOver p B, extendedPrime p q := by
    simpa only [pow_one] using eq 1
  rw [← eq n, ← eq', Finset.prod_pow]

private lemma localQuotient_surjective [Finite (PrimesOver p B)] (n : ℕ) :
    Function.Surjective (fun s : Bₚ ↦ fun q : PrimesOver p B ↦
      Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime q.1.asIdeal) ^ n)
        (algebraMap Bₚ (Localization.AtPrime q.1.asIdeal) s)) := by
  intro y
  let e (q : PrimesOver p B) :=
    IsLocalization.AtPrime.equivQuotMaximalIdealPow (extendedPrime p q)
      (Localization.AtPrime q.1.asIdeal) n
  obtain ⟨s, hs⟩ := Ideal.pi_quotient_surjective
    (I := fun q : PrimesOver p B ↦ extendedPrime p q ^ n)
    (fun q q' ne ↦ (extendedPrime_pairwise p ne).pow)
    (fun q ↦ (e q).symm (y q))
  refine ⟨s, funext fun q ↦ ?_⟩
  have h := congrArg (e q) (hs q)
  simpa only [e, IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
    AlgEquiv.apply_symm_apply] using h

private lemma localCompletion_bijective [IsNoetherianRing B] :
    Function.Bijective (fun x : AdicCompletion 𝔞 Bₚ ↦ fun q : PrimesOver p B ↦
      completionMap 𝔞 (maximalIdeal (Localization.AtPrime q.1.asIdeal))
        (algebraMap Bₚ (Localization.AtPrime q.1.asIdeal)) (map_extended_maximal_le p q) x) := by
  let : Finite (PrimesOver p B) := finitePrimes A B p
  obtain ⟨d, hd⟩ := Ideal.exists_pow_le_of_le_radical_of_fg (I := Ideal.radical 𝔞) (J := 𝔞)
    (le_refl _) (Ideal.fg_of_isNoetherianRing _)
  apply completionProduct_bijective
    (hsurj := localQuotient_surjective p) (k := fun n ↦ (d + 1) * n)
  · exact fun _ _ h ↦ Nat.mul_le_mul_left _ h
  · intro n
    rw [Nat.add_mul, one_mul]
    exact Nat.le_add_left _ _
  · intro n s hs
    have hj : s ∈ ⨅ q : PrimesOver p B, extendedPrime p q ^ ((d + 1) * n) := by
      refine Ideal.mem_iInf.mpr fun q ↦ ?_
      rw [← IsLocalization.AtPrime.under_maximalIdeal_pow (extendedPrime p q)
        (Localization.AtPrime q.1.asIdeal)]
      exact hs q
    rw [iInf_extendedPrime_pow, ← radical_eq_iInf p] at hj
    apply Ideal.pow_right_mono hd n
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (Nat.mul_le_mul_right n (Nat.le_succ d)) hj

private noncomputable def localizeTensor :
    (LocalCompletion Aₚ ⊗[A] B) ≃ₐ[Aₚ] (LocalCompletion Aₚ ⊗[Aₚ] Bₚ) :=
  (Algebra.TensorProduct.cancelBaseChange A Aₚ Aₚ (LocalCompletion Aₚ) B).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl (Localization.tensorRightAlgEquiv p.primeCompl B))

omit [Module.Finite A B] in
private lemma localizeTensor_tmul (x : LocalCompletion Aₚ) (b : B) :
    localizeTensor p (x ⊗ₜ[A] b) = x ⊗ₜ[Aₚ] algebraMap B Bₚ b := by
  simp [localizeTensor]

private noncomputable def localProductMap :
    AdicCompletion 𝔞 Bₚ →+* ((q : PrimesOver p B) → Factor p q) :=
  RingHom.pi fun q ↦ completionMap 𝔞 (maximalIdeal (Localization.AtPrime q.1.asIdeal))
    (algebraMap Bₚ (Localization.AtPrime q.1.asIdeal)) (map_extended_maximal_le p q)

omit [Module.Finite A B] in
private lemma comparison_eq (z : LocalCompletion Aₚ ⊗[A] B) :
    comparison p z = localProductMap p (tensorCompletion 𝔪 (localizeTensor p z)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x b =>
    funext q
    let C := Localization.AtPrime q.1.asIdeal
    let nC := maximalIdeal C
    have hbase :
        fromBaseCompletion p q x =
          completionMap 𝔞 nC (algebraMap Bₚ C) (map_extended_maximal_le p q)
            (completionMap 𝔪 𝔞 (algebraMap Aₚ Bₚ) le_rfl x) := by
      apply AdicCompletion.ext_evalₐ
      intro n
      change AdicCompletion.evalₐ nC n
        (completionMap 𝔪 nC (algebraMap Aₚ C) (map_maximal_le p q) x) =
          AdicCompletion.evalₐ nC n
            (completionMap 𝔞 nC (algebraMap Bₚ C) (map_extended_maximal_le p q)
              (completionMap 𝔪 𝔞 (algebraMap Aₚ Bₚ) le_rfl x))
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ 𝔪 n x)
      simp only [eval_completionMap, ← hr, quotientPowMap_mk]
      exact congrArg (Ideal.Quotient.mk (nC ^ n)) (RingHom.congr_fun (baseMap_eq p q) r).symm
    rw [localizeTensor_tmul, tensorCompletion_tmul]
    change fromBaseCompletion p q x * AdicCompletion.of nC C (algebraMap B C b) =
      completionMap 𝔞 nC (algebraMap Bₚ C) (map_extended_maximal_le p q)
        (completionMap 𝔪 𝔞 (algebraMap Aₚ Bₚ) le_rfl x *
          AdicCompletion.of 𝔞 Bₚ (algebraMap B Bₚ b))
    rw [map_mul, completionMap_of, ← IsScalarTower.algebraMap_apply B Bₚ C, hbase]


end Localization

theorem comparison_bijective : CanonicalDecomposition.{u, v} := by
  intro A B _ _ _ _ _ _ p _
  rw [show ⇑(comparison (B := B) p) =
    localProductMap (B := B) p ∘ tensorCompletion (maximalIdeal (Localization.AtPrime p)) ∘
      localizeTensor (B := B) p from funext (comparison_eq p)]
  exact (localCompletion_bijective p).comp
    ((tensorCompletion_bijective _).comp (localizeTensor p).bijective)

/-- The canonical algebra equivalence to the product of completed prime local rings. -/
noncomputable def decomposition {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [IsNoetherianRing A] [IsNoetherianRing B] (p : Ideal A) [p.IsPrime] :
    (LocalCompletion (Localization.AtPrime p) ⊗[A] B) ≃ₐ[Localization.AtPrime p]
      ((q : PrimesOver p B) → Factor p q) :=
  AlgEquiv.ofBijective (comparison p) (comparison_bijective A B p)

section Coordinates

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [IsNoetherianRing A] [IsNoetherianRing B] (p : Ideal A) [p.IsPrime]

@[simp]
theorem decomposition_tmul (x : LocalCompletion (Localization.AtPrime p)) (b : B)
    (q : PrimesOver p B) :
    decomposition p (x ⊗ₜ[A] b) q =
      fromBaseCompletion p q x * algebraMap B (Factor p q) b :=
  rfl

theorem decomposition_tmul_one (x : LocalCompletion (Localization.AtPrime p))
    (q : PrimesOver p B) :
    decomposition p (x ⊗ₜ[A] (1 : B)) q = fromBaseCompletion p q x := by
  rw [decomposition_tmul, map_one, mul_one]

theorem decomposition_one_tmul (b : B) (q : PrimesOver p B) :
    decomposition p ((1 : LocalCompletion (Localization.AtPrime p)) ⊗ₜ[A] b) q =
      algebraMap B (Factor p q) b := by
  rw [decomposition_tmul, map_one, one_mul]

end Coordinates

end CommutativeAlgebraNotes.FiniteAlgebraCompletion
