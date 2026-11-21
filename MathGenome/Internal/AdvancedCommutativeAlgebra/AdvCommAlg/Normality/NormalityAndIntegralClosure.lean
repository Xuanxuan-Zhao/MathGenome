import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.TotalQuotientProduct
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.NormalityAndIntegralClosure
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.Polynomial.Lifts

/-! SN-04: normality, integral closure in total fractions, and the finite
product of normal domains. The index set of the product is the complete set
of minimal primes, so the construction includes the zero ring. -/
universe u v w
namespace AdvCommAlg.Normality

section Transport
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
  [IsNoetherianRing R] [IsNoetherianRing S]

theorem isNormal_of_equiv (e : R ≃+* S) (h : IsNormal R) : IsNormal S := by
  intro p
  let q : PrimeSpectrum R := PrimeSpectrum.comap e.toRingHom p
  let f := Localization.localRingEquiv q.asIdeal p.asIdeal e rfl
  have hq := h q
  let := hq.1
  let := hq.2
  exact ⟨f.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end Transport

section Products
variable {ι : Type u} {B : ι → Type v} [Finite ι]
  [∀ i, CommRing (B i)] [∀ i, IsNoetherianRing (B i)] [∀ i, IsDomain (B i)]

theorem isNormal_pi_iff : IsNormal (∀ i, B i) ↔ ∀ i, IsIntegrallyClosed (B i) := by
  constructor
  · intro h i
    apply IsIntegrallyClosed.of_localization_maximal
    intro q _ hq
    let p : PrimeSpectrum (∀ i, B i) :=
      PrimeSpectrum.comap (Pi.evalRingHom B i) ⟨q, hq.isPrime⟩
    let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q)
    let : IsIntegrallyClosed (Localization.AtPrime (q.comap (Pi.evalRingHom B i))) := (h p).2
    exact IsIntegrallyClosed.of_equiv e
  · intro h p
    obtain ⟨i, q, rfl⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
    let e := RingEquiv.ofBijective (Localization.AtPrime.mapPiEvalRingHom q.asIdeal)
      (Localization.AtPrime.mapPiEvalRingHom_bijective q.asIdeal)
    let := h i
    let : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
        q.asIdeal.primeCompl_le_nonZeroDivisors
    exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

end Products

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- A prime whose local ring is a domain contains at most one minimal prime. -/
lemma minimalPrime_eq_of_localization_domain (m : Ideal A) [m.IsPrime]
    [IsDomain (Localization.AtPrime m)] (p q : MinimalPrime A)
    (hp : p.val ≤ m) (hq : q.val ≤ m) : p = q := by
  have H (r : MinimalPrime A) (hr : r.val ≤ m) :
      r.val.map (algebraMap A (Localization.AtPrime m)) = ⊥ := by
    have hd : Disjoint (m.primeCompl : Set A) (r.val : Set A) := by
      exact Set.disjoint_left.mpr (fun _ hx hy => hx (hr hy))
    have hu := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl
      (Localization.AtPrime m) r.property.isPrime hd
    change (r.val.map (algebraMap A (Localization.AtPrime m))).comap
      (algebraMap A (Localization.AtPrime m)) = r.val at hu
    have hm : r.val.map (algebraMap A (Localization.AtPrime m)) ∈
        minimalPrimes (Localization.AtPrime m) := by
      change _ ∈ (⊥ : Ideal (Localization.AtPrime m)).minimalPrimes
      rw [← Ideal.map_bot (f := algebraMap A (Localization.AtPrime m)),
        IsLocalization.minimalPrimes_map m.primeCompl]
      change (r.val.map (algebraMap A (Localization.AtPrime m))).comap
        (algebraMap A (Localization.AtPrime m)) ∈ minimalPrimes A
      rw [hu]
      exact r.property
    simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using hm
  apply Subtype.ext
  have hd (r : MinimalPrime A) (hr : r.val ≤ m) :
      Disjoint (m.primeCompl : Set A) (r.val : Set A) :=
    Set.disjoint_left.mpr (fun _ hx hy => hx (hr hy))
  rw [← IsLocalization.under_map_of_isPrime_disjoint m.primeCompl
      (Localization.AtPrime m) p.property.isPrime (hd p hp),
    ← IsLocalization.under_map_of_isPrime_disjoint m.primeCompl
      (Localization.AtPrime m) q.property.isPrime (hd q hq), H p hp, H q hq]

theorem minimalPrimes_pairwise_coprime_of_normal (h : IsNormal A) :
    Pairwise (Function.onFun IsCoprime (fun p : MinimalPrime A => p.val)) := by
  intro p q hpq
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hn
  obtain ⟨m, hm, hpm⟩ := (p.val ⊔ q.val).exists_le_maximal hn
  let := hm
  let := (h ⟨m, hm.isPrime⟩).1
  exact hpq (minimalPrime_eq_of_localization_domain A m p q
    (le_sup_left.trans hpm) (le_sup_right.trans hpm))

/-- The simultaneous quotient map to all reduced irreducible components. -/
abbrev minimalComponentMap : A →+* (∀ p : MinimalPrime A, A ⧸ p.val) :=
  RingHom.pi fun p => Ideal.Quotient.mk p.val

lemma minimalComponentMap_injective [IsReduced A] :
    Function.Injective (minimalComponentMap A) := by
  apply (RingHom.injective_iff_ker_eq_bot (minimalComponentMap A)).mpr
  apply le_antisymm _ bot_le
  intro a ha
  have ham : a ∈ sInf (minimalPrimes A) := by
    apply Ideal.mem_sInf.mpr
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun ha ⟨p, hp⟩)
  rw [Ideal.sInf_minimalPrimes] at ham
  exact (show IsNilpotent a from ham).eq_zero

lemma minimalComponentMap_surjective_of_coprime
    (h : Pairwise (Function.onFun IsCoprime (fun p : MinimalPrime A => p.val))) :
    Function.Surjective (minimalComponentMap A) := by
  let := finite_minimalPrime_family A
  intro x
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective h x
  exact ⟨a, funext ha⟩

theorem exists_minimalComponentEquiv_of_normal [IsReduced A] (h : IsNormal A) :
    ∃ e : A ≃+* (∀ p : MinimalPrime A, A ⧸ p.val),
      (∀ (a : A) (p : MinimalPrime A), e a p = Ideal.Quotient.mk p.val a) ∧
      ∀ p : MinimalPrime A, IsIntegrallyClosed (A ⧸ p.val) := by
  let := finite_minimalPrime_family A
  let e := RingEquiv.ofBijective (minimalComponentMap A)
    ⟨minimalComponentMap_injective A, minimalComponentMap_surjective_of_coprime A
      (minimalPrimes_pairwise_coprime_of_normal A h)⟩
  exact ⟨e, fun _ _ => rfl, isNormal_pi_iff.mp (isNormal_of_equiv e h)⟩

/-- In any algebra, an idempotent is integral: it satisfies `X²-X`. -/
lemma isIntegral_of_idempotent {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] {x : B} (hx : x * x = x) : IsIntegral R x := by
  refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C (1 : R)),
    Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
  simpa only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_C, map_one, mul_sub, mul_one, sub_eq_zero] using hx

/-- Integrally closed total fractions contain the coordinate idempotents;
these separate each pair of minimal primes. -/
theorem minimalPrimes_pairwise_coprime_of_integral_totalQuotient [IsReduced A]
    (h : ∀ z : TotalQuotientRing A, IsIntegral A z →
      ∃ a : A, algebraMap A (TotalQuotientRing A) a = z) :
    Pairwise (Function.onFun IsCoprime (fun p : MinimalPrime A => p.val)) := by
  classical
  obtain ⟨e, he, _⟩ := existsUnique_totalQuotientEquiv A
  intro p q hpq
  let z := e.symm (Pi.single p (1 : MinimalFraction A p))
  have hz : z * z = z := by
    apply e.injective
    ext r
    by_cases hr : r = p
    · subst hr; simp [z]
    · simp [z, Pi.single_eq_of_ne hr]
  obtain ⟨a, ha⟩ := h z (isIntegral_of_idempotent hz)
  have H (r : MinimalPrime A) :
      algebraMap (A ⧸ r.val) (MinimalFraction A r) (Ideal.Quotient.mk r.val a) =
        Pi.single p (1 : MinimalFraction A p) r := by
    rw [← he a r, ha]
    exact congrFun (e.apply_symm_apply _) r
  have hap : Ideal.Quotient.mk p.val a = 1 := by
    apply IsFractionRing.injective (A ⧸ p.val) (MinimalFraction A p)
    simpa using H p
  have haq : Ideal.Quotient.mk q.val a = 0 := by
    apply IsFractionRing.injective (A ⧸ q.val) (MinimalFraction A q)
    simpa [Pi.single_eq_of_ne hpq.symm] using H q
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.eq_top_of_isUnit_mem _ (x := (1 : A)) ?_ isUnit_one
  have hpa : 1 - a ∈ p.val := Ideal.Quotient.eq_zero_iff_mem.mp (by simp [hap])
  have hqa : a ∈ q.val := Ideal.Quotient.eq_zero_iff_mem.mp haq
  simpa using (p.val ⊔ q.val).add_mem
    ((show p.val ≤ p.val ⊔ q.val from le_sup_left) hpa)
    ((show q.val ≤ p.val ⊔ q.val from le_sup_right) hqa)

/-- An integral element of a component field, supported in just that
coordinate, is integral over `A`. Lift its monic equation and multiply by
`X` to annihilate all the other coordinates. -/
lemma isIntegral_single_minimalFraction (p : MinimalPrime A)
    {z : MinimalFraction A p} (hz : IsIntegral (A ⧸ p.val) z) :
    IsIntegral A (Pi.single p z : ∀ q : MinimalPrime A, MinimalFraction A q) := by
  classical
  obtain ⟨f, hf, hfz⟩ := hz
  obtain ⟨F, hF, _, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts f).mpr
      (fun _ => Ideal.Quotient.mk_surjective _)) hf
  refine ⟨Polynomial.X * F, Polynomial.monic_X.mul hFm, ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_pi_apply]
  funext q
  change Polynomial.aeval (Pi.single p z q) (Polynomial.X * F) = 0
  rw [map_mul, Polynomial.aeval_X]
  by_cases hqp : q = p
  · subst q
    simp only [Pi.single_eq_same]
    have hroot : Polynomial.aeval z F = 0 := by
      rw [Polynomial.aeval_def, IsScalarTower.algebraMap_eq A (A ⧸ p.val)
        (MinimalFraction A p), ← Polynomial.eval₂_map, Ideal.Quotient.algebraMap_eq, hF]
      exact hfz
    rw [hroot, mul_zero]
  · rw [Pi.single_eq_of_ne hqp, zero_mul]

/-- Integral closure in the total quotient ring passes to each minimal
component, with its specified fraction field. -/
theorem minimalComponent_integrallyClosed_of_integral_totalQuotient [IsReduced A]
    (h : ∀ z : TotalQuotientRing A, IsIntegral A z →
      ∃ a : A, algebraMap A (TotalQuotientRing A) a = z)
    (p : MinimalPrime A) : IsIntegrallyClosed (A ⧸ p.val) := by
  classical
  obtain ⟨e, he, _⟩ := existsUnique_totalQuotientEquiv A
  have heA : ∀ a : A, e (algebraMap A (TotalQuotientRing A) a) =
      algebraMap A (∀ q : MinimalPrime A, MinimalFraction A q) a := by
    intro a
    ext q
    exact he a q
  let eA : TotalQuotientRing A ≃ₐ[A] (∀ q : MinimalPrime A, MinimalFraction A q) :=
    AlgEquiv.ofRingEquiv (f := e) heA
  apply (isIntegrallyClosed_iff (MinimalFraction A p)).mpr
  intro z hz
  have hzQ := (isIntegral_single_minimalFraction A p hz).map eA.symm
  obtain ⟨a, ha⟩ := h _ hzQ
  refine ⟨Ideal.Quotient.mk p.val a, ?_⟩
  rw [← he a p, ha]
  exact (congrFun (eA.apply_symm_apply (Pi.single p z)) p).trans (Pi.single_eq_same p z)

/-- A normal ring contains all its integral total fractions. -/
theorem integral_totalQuotient_of_normal [IsReduced A] (h : IsNormal A)
    (z : TotalQuotientRing A) (hz : IsIntegral A z) :
    ∃ a : A, algebraMap A (TotalQuotientRing A) a = z := by
  classical
  obtain ⟨eA, heA, hc⟩ := exists_minimalComponentEquiv_of_normal A h
  obtain ⟨e, he, _⟩ := existsUnique_totalQuotientEquiv A
  have hzcomp (p : MinimalPrime A) :
      IsIntegral (A ⧸ p.val) (e z p) := by
    exact hz.map_of_comp_eq (Ideal.Quotient.mk p.val)
      ((Pi.evalRingHom (fun q => MinimalFraction A q) p).comp e.toRingHom)
      (by ext a; exact (he a p).symm)
  have hccomp (p : MinimalPrime A) : ∃ b : A ⧸ p.val,
      algebraMap (A ⧸ p.val) (MinimalFraction A p) b = e z p := by
    let := hc p
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hzcomp p)
  choose b hb using hccomp
  obtain ⟨a, ha⟩ := eA.surjective b
  refine ⟨a, e.injective ?_⟩
  ext p
  rw [he, ← heA, ha]
  exact hb p

/-- The product decomposition obtained from integral closure gives local
integrally closed domains at every prime. -/
theorem isNormal_of_integral_totalQuotient [IsReduced A]
    (h : ∀ z : TotalQuotientRing A, IsIntegral A z →
      ∃ a : A, algebraMap A (TotalQuotientRing A) a = z) : IsNormal A := by
  let := finite_minimalPrime_family A
  let e := RingEquiv.ofBijective (minimalComponentMap A)
    ⟨minimalComponentMap_injective A, minimalComponentMap_surjective_of_coprime A
      (minimalPrimes_pairwise_coprime_of_integral_totalQuotient A h)⟩
  have hn : IsNormal (∀ p : MinimalPrime A, A ⧸ p.val) :=
    isNormal_pi_iff.mpr (minimalComponent_integrallyClosed_of_integral_totalQuotient A h)
  exact isNormal_of_equiv e.symm hn

/-- SN-04: normality is equivalent to integral closure in total fractions. -/
theorem isNormal_iff_integral_totalQuotient [IsReduced A] :
    IsNormal A ↔ ∀ z : TotalQuotientRing A, IsIntegral A z →
      ∃ a : A, algebraMap A (TotalQuotientRing A) a = z :=
  ⟨integral_totalQuotient_of_normal A, isNormal_of_integral_totalQuotient A⟩

/-- The same equivalence with Mathlib's total-fraction integral closure predicate. -/
theorem isNormal_iff_isIntegrallyClosed [IsReduced A] :
    IsNormal A ↔ IsIntegrallyClosed A := by
  rw [isNormal_iff_integral_totalQuotient, isIntegrallyClosed_iff (TotalQuotientRing A)]

/-- SN-04: the finite product of integrally closed domains, together with
the matching fraction fields in the total quotient product. -/
theorem exists_normal_product_decomposition [IsReduced A] (h : IsNormal A) :
    Finite (MinimalPrime A) ∧
    ∃ e : A ≃+* (∀ p : MinimalPrime A, A ⧸ p.val),
      (∀ p : MinimalPrime A, IsDomain (A ⧸ p.val) ∧ IsIntegrallyClosed (A ⧸ p.val)) ∧
      (∀ (a : A) (p : MinimalPrime A), e a p = Ideal.Quotient.mk p.val a) ∧
      ∃ eQ : TotalQuotientRing A ≃+* (∀ p : MinimalPrime A, MinimalFraction A p),
        ∀ (a : A) (p : MinimalPrime A),
          eQ (algebraMap A (TotalQuotientRing A) a) p =
            algebraMap (A ⧸ p.val) (MinimalFraction A p) (e a p) := by
  obtain ⟨e, he, hc⟩ := exists_minimalComponentEquiv_of_normal A h
  obtain ⟨eQ, heQ, _⟩ := existsUnique_totalQuotientEquiv A
  exact ⟨finite_minimalPrime_family A, e, fun p => ⟨inferInstance, hc p⟩,
    he, eQ, fun a p => (heQ a p).trans (congrArg _ (he a p).symm)⟩

/-- The converse applies to every finite decomposition into normal domains. -/
theorem isNormal_of_product_decomposition (ι : Type v) [Finite ι]
    (B : ι → Type w) [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, IsIntegrallyClosed (B i)] (e : A ≃+* (∀ i, B i)) : IsNormal A := by
  let : ∀ i, IsNoetherianRing (B i) := fun i =>
    isNoetherianRing_of_surjective A (B i) ((Pi.evalRingHom B i).comp e.toRingHom)
      ((Function.surjective_eval i).comp e.surjective)
  exact isNormal_of_equiv e.symm (isNormal_pi_iff.mpr (fun _ => inferInstance))

/-- The zero ring gives the empty product, with no artificial nontriviality
assumption on the ambient ring. -/
theorem exists_empty_product_decomposition [Subsingleton A] :
    IsEmpty (MinimalPrime A) ∧
    ∃ e : A ≃+* (∀ p : MinimalPrime A, A ⧸ p.val),
      (∀ (a : A) (p : MinimalPrime A), e a p = Ideal.Quotient.mk p.val a) ∧
      ∀ p : MinimalPrime A, IsDomain (A ⧸ p.val) ∧ IsIntegrallyClosed (A ⧸ p.val) := by
  have : IsReduced A := ⟨fun _ _ => Subsingleton.elim _ _⟩
  obtain ⟨_, e, hc, he, _⟩ := exists_normal_product_decomposition A (isNormal_of_subsingleton A)
  exact ⟨minimalPrimes_empty_of_subsingleton A, e, he, hc⟩

end AdvCommAlg.Normality
