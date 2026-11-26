import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ComparePolynomialLocalCompletions

namespace CommutativeAlgebraNotes.PolynomialLocalCompletion

open IsLocalRing

private theorem ker_evalₐ (R : Type*) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  ext x
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (n := n) I.fg_of_isNoetherianRing, LinearMap.mem_ker]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (Ideal.mul_top _).le]
  exact map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R (Ideal.mul_top _)).injective

private theorem ker_polynomialMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) :
    RingHom.ker (Polynomial.mapRingHom f) = (RingHom.ker f).map Polynomial.C := by
  ext p
  rw [Ideal.mem_map_C_iff, RingHom.mem_ker]
  change p.map f = 0 ↔ _
  rw [Polynomial.ext_iff]
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, RingHom.mem_ker]

private theorem comap_map_of_common_quotient
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (J : Ideal A)
    (hg : Function.Surjective g) (hgf : Function.Surjective (g.comp f))
    (hJ : RingHom.ker (g.comp f) ≤ J) (hK : RingHom.ker g ≤ J.map f) :
    (J.map f).comap f = J := by
  have h₁ := Ideal.comap_map_of_surjective' g hg (J.map f)
  have h₂ := Ideal.comap_map_of_surjective' (g.comp f) hgf J
  rw [sup_eq_left.mpr hK] at h₁
  rw [sup_eq_left.mpr hJ] at h₂
  rw [← h₁, Ideal.comap_comap, Ideal.map_map, h₂]

private theorem surjective_quotientMap_of_common_quotient
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (J : Ideal A)
    (hgf : Function.Surjective (g.comp f)) (hK : RingHom.ker g ≤ J.map f) :
    Function.Surjective (Ideal.quotientMap (J.map f) f Ideal.le_comap_map) := by
  intro y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := hgf (g b)
  refine ⟨Ideal.Quotient.mk J a, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply hK
  simp only [RingHom.mem_ker, map_sub, sub_eq_zero]
  exact ha

section PolynomialQuotients

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (P : Ideal (Polynomial R))
variable (hP : maximalIdeal R ≤ P.comap Polynomial.C)
include hP

private theorem polynomialTruncation (n : ℕ) :
    ((P ^ n).map (coefficientMap R)).comap (coefficientMap R) = P ^ n ∧
      Function.Surjective
        (Ideal.quotientMap ((P ^ n).map (coefficientMap R))
          (coefficientMap R) Ideal.le_comap_map) := by
  let m := maximalIdeal R
  -- Both polynomial rings reduce to the polynomial ring over R modulo m ^ n.
  let g := Polynomial.mapRingHom (AdicCompletion.evalₐ m n).toRingHom
  have hcomp : g.comp (coefficientMap R) = Polynomial.mapRingHom (Ideal.Quotient.mk (m ^ n)) := by
    dsimp only [g, coefficientMap]
    rw [Polynomial.mapRingHom_comp]
    congr 1
  have hg : Function.Surjective g :=
    Polynomial.map_surjective _ (AdicCompletion.surjective_evalₐ m n)
  have hgf : Function.Surjective (g.comp (coefficientMap R)) := by
    rw [hcomp]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hle : (m ^ n).map (Polynomial.C : R →+* Polynomial R) ≤ P ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hP) n
  have hJ : RingHom.ker (g.comp (coefficientMap R)) ≤ P ^ n := by
    rw [hcomp, ker_polynomialMap, Ideal.mk_ker]
    exact hle
  have hK : RingHom.ker g ≤ (P ^ n).map (coefficientMap R) := by
    dsimp only [g]
    rw [ker_polynomialMap, ker_evalₐ, Ideal.map_map,
      ← Polynomial.mapRingHom_comp_C, ← Ideal.map_map]
    exact Ideal.map_mono hle
  exact ⟨comap_map_of_common_quotient _ g _ hg hgf hJ hK,
    surjective_quotientMap_of_common_quotient _ g _ hgf hK⟩

/-- The extended ideal contracts to the original ideal. -/
theorem extendedIdeal_comap :
    (extendedIdeal P).comap (coefficientMap R) = P := by
  simpa using (polynomialTruncation P hP 1).1

/-- The canonical isomorphism on polynomial quotients at each power. -/
noncomputable def quotientEquiv (n : ℕ) :
    (Polynomial R ⧸ P ^ n) ≃+* (Polynomial (Completion R) ⧸ extendedIdeal P ^ n) :=
  (RingEquiv.ofBijective
      (Ideal.quotientMap ((P ^ n).map (coefficientMap R)) (coefficientMap R) Ideal.le_comap_map)
      ⟨Ideal.quotientMap_injective' (polynomialTruncation P hP n).1.le,
        (polynomialTruncation P hP n).2⟩).trans
    (Ideal.quotEquivOfEq (Ideal.map_pow _ _ _))

@[simp]
theorem quotientEquiv_mk (n : ℕ) (p : Polynomial R) :
    quotientEquiv P hP n (Ideal.Quotient.mk (P ^ n) p) =
      Ideal.Quotient.mk (extendedIdeal P ^ n) (coefficientMap R p) := rfl

/-- The extended polynomial prime is prime. -/
theorem extendedIdeal_isPrime [P.IsPrime] : (extendedIdeal P).IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  have e := quotientEquiv P hP 1
  rw [pow_one, pow_one] at e
  exact e.symm.toMulEquiv.isDomain

omit hP in
theorem primeComparison : Specs.primeComparison := by
  intro R _ _ _ P _ hP
  exact ⟨extendedIdeal_isPrime P hP, extendedIdeal_comap P hP⟩

omit hP in
theorem quotientComparison : Specs.quotientComparison := by
  intro R _ _ _ P _ hP n
  exact ⟨quotientEquiv P hP n, quotientEquiv_mk P hP n⟩

end PolynomialQuotients

section Localization

variable {A B : Type*} [CommRing A] [CommRing B]
  (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
  (f : A →+* B) (hf : P = Q.comap f)

include hf in
private theorem map_primeComplement_quotient
    {I : Ideal A} {J : Ideal B} (hJ : J ≤ Q)
    (e : (A ⧸ I) ≃+* (B ⧸ J))
    (he : ∀ x, e (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x)) :
    (P.primeCompl.map (Ideal.Quotient.mk I)).map e.toMonoidHom =
      Q.primeCompl.map (Ideal.Quotient.mk J) := by
  have hmem (a : A) : a ∈ P ↔ f a ∈ Q :=
    SetLike.ext_iff.mp hf a
  ext y
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨f a, fun h => ha ((hmem a).mpr h), (he a).symm⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨u, hu⟩ := e.surjective (Ideal.Quotient.mk J b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    have hd : f a - b ∈ J :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ((he a).symm.trans hu)
    have ha : a ∈ P.primeCompl := by
      intro ha
      apply hb
      simpa using Q.sub_mem ((hmem a).mp ha) (hJ hd)
    exact ⟨_, ⟨a, ha, rfl⟩, hu⟩

private theorem localizedQuotientEquiv
    (n : ℕ) (e : (A ⧸ P ^ n) ≃+* (B ⧸ Q ^ n))
    (he : ∀ x, e (Ideal.Quotient.mk (P ^ n) x) = Ideal.Quotient.mk (Q ^ n) (f x)) :
    ∃ E : (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P) ^ n) ≃+*
        (Localization.AtPrime Q ⧸ maximalIdeal (Localization.AtPrime Q) ^ n),
      ∀ x : Localization.AtPrime P, E (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk _ (Localization.localRingHom P Q f hf x) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P) ^ 0) :=
      (Ideal.Quotient.subsingleton_iff).mpr (by simp)
    have : Subsingleton (Localization.AtPrime Q ⧸ maximalIdeal (Localization.AtPrime Q) ^ 0) :=
      (Ideal.Quotient.subsingleton_iff).mpr (by simp)
    let g : (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P) ^ 0) →+* _ :=
      Ideal.quotientMap (maximalIdeal (Localization.AtPrime Q) ^ 0)
        (Localization.localRingHom P Q f hf) (by simp)
    exact ⟨RingEquiv.ofBijective g ⟨fun _ _ _ => Subsingleton.elim _ _,
      fun _ => ⟨0, Subsingleton.elim _ _⟩⟩, fun _ => Subsingleton.elim _ _⟩
  let Aₚ := Localization.AtPrime P
  let Bₚ := Localization.AtPrime Q
  let I := (P ^ n).map (algebraMap A Aₚ)
  let J := (Q ^ n).map (algebraMap B Bₚ)
  have hI : I = maximalIdeal Aₚ ^ n := by
    dsimp only [I]
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  have hJ : J = maximalIdeal Bₚ ^ n := by
    dsimp only [J]
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  have h : (Algebra.algebraMapSubmonoid (A ⧸ P ^ n) P.primeCompl).map e.toMonoidHom =
      Algebra.algebraMapSubmonoid (B ⧸ Q ^ n) Q.primeCompl :=
    map_primeComplement_quotient P Q f hf (Ideal.pow_le_self hn) e he
  -- A quotient of a localization is a localization of the quotient.
  let E := IsLocalization.ringEquivOfRingEquiv
    (M := Algebra.algebraMapSubmonoid (A ⧸ P ^ n) P.primeCompl)
    (T := Algebra.algebraMapSubmonoid (B ⧸ Q ^ n) Q.primeCompl)
    (Aₚ ⧸ I) (Bₚ ⧸ J) e h
  refine ⟨(Ideal.quotEquivOfEq hI.symm).trans (E.trans (Ideal.quotEquivOfEq hJ)), ?_⟩
  have hLoc : E.toRingHom.comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk J).comp (Localization.localRingHom P Q f hf) := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro x
    change E (algebraMap (A ⧸ P ^ n) (Aₚ ⧸ I) (Ideal.Quotient.mk (P ^ n) x)) = _
    calc
      _ = algebraMap (B ⧸ Q ^ n) (Bₚ ⧸ J) (e (Ideal.Quotient.mk (P ^ n) x)) :=
        IsLocalization.ringEquivOfRingEquiv_eq (S := Aₚ ⧸ I) (Q := Bₚ ⧸ J) h _
      _ = _ := by
        rw [he]
        change Ideal.Quotient.mk J (algebraMap B Bₚ (f x)) =
          Ideal.Quotient.mk J (Localization.localRingHom P Q f hf (algebraMap A Aₚ x))
        rw [Localization.localRingHom_to_map]
  intro x
  change Ideal.quotEquivOfEq hJ (E (Ideal.Quotient.mk I x)) = _
  have hx := RingHom.congr_fun hLoc x
  change E (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J _ at hx
  rw [hx]
  rfl

end Localization

section InverseLimit

variable {A B : Type*} [CommRing A] [CommRing B]
  (I : Ideal A) (J : Ideal B)

private theorem factorPow_evalₐ {n m : ℕ} (hmn : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x (Ideal.mul_top (I ^ n)).le,
    ← AdicCompletion.factor_eval_eq_evalₐ I x (Ideal.mul_top (I ^ m)).le]
  change Ideal.Quotient.factorPow I hmn
      (Submodule.factor (Ideal.mul_top (I ^ n)).le (x.val n)) =
    Submodule.factor (Ideal.mul_top (I ^ m)).le (x.val m)
  rw [← x.property hmn]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val n)
  rw [← ha]
  rfl

variable (e : ∀ n : ℕ, (A ⧸ I ^ n) ≃+* (B ⧸ J ^ n))

private theorem quotientEquiv_factorPow (f : A →+* B)
    (he : ∀ n a, e n (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk (J ^ n) (f a))
    {n m : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (e n x) = e m (Ideal.Quotient.factorPow I hmn x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he]
  exact (he m a).symm

private noncomputable def mapInverseLimit
    (he : ∀ {n m : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (e n x) = e m (Ideal.Quotient.factorPow I hmn x)) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (fun hmn => RingHom.ext fun x => (he hmn _).trans (congrArg _ (factorPow_evalₐ I hmn x)))

@[simp]
private theorem evalₐ_mapInverseLimit
    (he : ∀ {n m : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n),
      Ideal.Quotient.factorPow J hmn (e n x) = e m (Ideal.Quotient.factorPow I hmn x))
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (mapInverseLimit I J e he x) =
      e n (AdicCompletion.evalₐ I n x) := by
  exact AdicCompletion.evalₐ_liftRingHom J _
    (fun hmn => RingHom.ext fun y => (he hmn _).trans (congrArg _ (factorPow_evalₐ I hmn y))) n x

private theorem inverseLimitEquiv (f : A →+* B)
    (he : ∀ n a, e n (Ideal.Quotient.mk (I ^ n) a) = Ideal.Quotient.mk (J ^ n) (f a)) :
    ∃ E : AdicCompletion I A ≃+* AdicCompletion J B,
      ∀ x, E (algebraMap A _ x) = algebraMap B _ (f x) := by
  have h := @quotientEquiv_factorPow A B _ _ I J e f he
  have hi {n m : ℕ} (hmn : m ≤ n) (x : B ⧸ J ^ n) :
      Ideal.Quotient.factorPow I hmn ((e n).symm x) =
        (e m).symm (Ideal.Quotient.factorPow J hmn x) := by
    apply (e m).injective
    rw [RingEquiv.apply_symm_apply, ← h hmn, RingEquiv.apply_symm_apply]
  let E : AdicCompletion I A ≃+* AdicCompletion J B :=
    { mapInverseLimit I J e h with
      invFun := mapInverseLimit J I (fun n => (e n).symm) hi
      left_inv := fun x => AdicCompletion.ext_evalₐ fun n => by
        change AdicCompletion.evalₐ I n
          (mapInverseLimit J I (fun n => (e n).symm) hi (mapInverseLimit I J e h x)) = _
        simp
      right_inv := fun x => AdicCompletion.ext_evalₐ fun n => by
        change AdicCompletion.evalₐ J n
          (mapInverseLimit I J e h (mapInverseLimit J I (fun n => (e n).symm) hi x)) = _
        simp }
  refine ⟨E, fun x => AdicCompletion.ext_evalₐ fun n => ?_⟩
  change AdicCompletion.evalₐ J n (mapInverseLimit I J e h (AdicCompletion.of I A x)) =
    AdicCompletion.evalₐ J n (AdicCompletion.of J B (f x))
  simpa using he n x

end InverseLimit

theorem completionComparison : Specs.completionComparison := by
  intro R _ _ _ P _ hP
  let hp := extendedIdeal_isPrime P hP
  have hc := (extendedIdeal_comap P hP).symm
  refine ⟨hp, hc, ?_⟩
  have h n := localizedQuotientEquiv P (extendedIdeal P) (coefficientMap R) hc n
    (quotientEquiv P hP n) (quotientEquiv_mk P hP n)
  choose e he using h
  exact inverseLimitEquiv _ _ e _ he

end CommutativeAlgebraNotes.PolynomialLocalCompletion
