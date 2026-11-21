import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.ReducednessCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.TotalQuotientProduct
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.Submodule

/-! SN-04, total quotient product (paper.tex:4104–4130).

Prime avoidance identifies the primes of the total quotient ring with the
minimal primes of `A`. Its dimension is at most zero, and Noetherianity makes
it Artinian. Chinese remainders for the extended minimal primes then give the
product, with each field identified canonically with `Frac(A/p)`.
The constructions allow the empty family, so no nontriviality assumption is used.
-/
universe u
namespace AdvCommAlg.Normality
variable (A : Type u) [CommRing A] [IsNoetherianRing A]

theorem finite_minimalPrime_family : Finite (MinimalPrime A) :=
  (minimalPrimes.finite_of_isNoetherianRing A).to_subtype

theorem nonZeroDivisors_iff_avoids_minimalPrimes [IsReduced A] (a : A) :
    a ∈ nonZeroDivisors A ↔ ∀ p ∈ minimalPrimes A, a ∉ p := by
  constructor
  · intro ha p hp hap
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hap hp ha
  · intro ha
    apply mem_nonZeroDivisors_iff_right.mpr
    intro b hab
    have hb : b ∈ sInf (minimalPrimes A) := by
      apply Ideal.mem_sInf.mpr
      intro p hp
      exact (hp.isPrime.mem_or_mem (hab ▸ p.zero_mem)).resolve_right (ha p hp)
    rw [Ideal.sInf_minimalPrimes] at hb
    exact (show IsNilpotent b from hb).eq_zero

/-- Primes disjoint from all nonzerodivisors are precisely the minimal primes. -/
lemma prime_disjoint_nonZeroDivisors_iff [IsReduced A] (p : Ideal A) [p.IsPrime] :
    Disjoint (nonZeroDivisors A : Set A) (p : Set A) ↔ p ∈ minimalPrimes A := by
  constructor
  · intro hd
    have hsub : (p : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A) := by
      intro a ha
      have hn : a ∉ nonZeroDivisors A := fun h => Set.disjoint_left.mp hd h ha
      have hx := mt (nonZeroDivisors_iff_avoids_minimalPrimes A a).mpr hn
      push Not at hx
      obtain ⟨q, hq, haq⟩ := hx
      exact Set.mem_biUnion hq haq
    obtain ⟨q, hq, hpq⟩ :=
      (Ideal.subset_union_prime_finite (minimalPrimes.finite_of_isNoetherianRing A)
        (⊥ : Ideal A) ⊥ (fun q hq _ _ => hq.isPrime)).mp hsub
    have hqp : q ≤ p := hq.2 ⟨inferInstance, bot_le⟩ hpq
    exact le_antisymm hpq hqp ▸ hq
  · intro hp
    exact (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp).symm

theorem totalQuotient_zeroDimensional [IsReduced A] :
    Ring.KrullDimLE 0 (TotalQuotientRing A) := by
  apply Ring.KrullDimLE.mk₀
  intro P hP
  have := hP
  let p := P.comap (algebraMap A (TotalQuotientRing A))
  apply Ideal.isMaximal_def.mpr
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨hP.ne_top, ?_⟩
  intro J hJ hPJ
  obtain ⟨Q, hQ, hJQ⟩ := J.exists_le_maximal hJ
  have hQmin : Q.comap (algebraMap A (TotalQuotientRing A)) ∈ minimalPrimes A := by
    have := hQ.isPrime
    exact (prime_disjoint_nonZeroDivisors_iff A _).mp
      ((IsLocalization.isPrime_iff_isPrime_disjoint (nonZeroDivisors A)
        (TotalQuotientRing A) Q).mp hQ.isPrime).2
  have hQp : Q.comap (algebraMap A (TotalQuotientRing A)) ≤ p :=
    hQmin.2 ⟨inferInstance, bot_le⟩ (Ideal.comap_mono (hPJ.trans hJQ))
  have hQP : Q ≤ P := by
    rw [← IsLocalization.map_under (nonZeroDivisors A) (TotalQuotientRing A) Q,
      ← IsLocalization.map_under (nonZeroDivisors A) (TotalQuotientRing A) P]
    exact Ideal.map_mono hQp
  exact hJQ.trans hQP

theorem totalQuotient_artinian [IsReduced A] : IsArtinianRing (TotalQuotientRing A) := by
  let := totalQuotient_zeroDimensional A
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- The prime of the total quotient ring over a minimal prime of `A`. -/
def minimalComponentIdeal (p : MinimalPrime A) : Ideal (TotalQuotientRing A) :=
  p.val.map (algebraMap A (TotalQuotientRing A))

lemma minimalComponentIdeal_under (p : MinimalPrime A) :
    (minimalComponentIdeal A p).comap (algebraMap A (TotalQuotientRing A)) = p.val :=
  IsLocalization.under_map_of_isPrime_disjoint (nonZeroDivisors A)
    (TotalQuotientRing A) p.property.isPrime
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.property).symm

instance minimalComponentIdeal_isPrime (p : MinimalPrime A) :
    (minimalComponentIdeal A p).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (nonZeroDivisors A)
    (TotalQuotientRing A) p.val p.property.isPrime
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes p.property).symm

instance minimalComponentIdeal_isMaximal [IsReduced A] (p : MinimalPrime A) :
    (minimalComponentIdeal A p).IsMaximal := by
  let := totalQuotient_zeroDimensional A
  exact (minimalComponentIdeal_isPrime A p).isMaximal'

lemma minimalComponentIdeal_injective : Function.Injective (minimalComponentIdeal A) := by
  intro p q h
  apply Subtype.ext
  simpa only [minimalComponentIdeal_under] using
    congrArg (Ideal.comap (algebraMap A (TotalQuotientRing A))) h

lemma minimalComponentIdeal_pairwise [IsReduced A] :
    Pairwise (Function.onFun IsCoprime (minimalComponentIdeal A)) := by
  intro p q hpq
  exact Ideal.isCoprime_iff_sup_eq.mpr
    ((minimalComponentIdeal_isMaximal A p).coprime_of_ne
      (minimalComponentIdeal_isMaximal A q)
      (fun h => hpq (minimalComponentIdeal_injective A h)))

lemma iInf_minimalComponentIdeal [IsReduced A] :
    (⨅ p : MinimalPrime A, minimalComponentIdeal A p) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors A) x
  have ha : a ∈ sInf (minimalPrimes A) := by
    apply Ideal.mem_sInf.mpr
    intro p hp
    have hxp : x ∈ minimalComponentIdeal A ⟨p, hp⟩ :=
      (Ideal.mem_iInf.mp hx) ⟨p, hp⟩
    have hma : algebraMap A (TotalQuotientRing A) a ∈ minimalComponentIdeal A ⟨p, hp⟩ := by
      rw [← hxs]
      exact Ideal.mul_mem_right _ _ hxp
    change a ∈ (minimalComponentIdeal A ⟨p, hp⟩).comap
      (algebraMap A (TotalQuotientRing A)) at hma
    rwa [minimalComponentIdeal_under] at hma
  rw [Ideal.sInf_minimalPrimes] at ha
  have ha0 : a = 0 := (show IsNilpotent a from ha).eq_zero
  have hx0 : x * algebraMap A (TotalQuotientRing A) s = 0 := by simpa [ha0] using hxs
  exact (IsLocalization.map_units (TotalQuotientRing A) s).mul_left_eq_zero.mp hx0

/-- The universal map from total fractions to the residue field of a minimal prime. -/
noncomputable def totalQuotientToResidue [IsReduced A] (p : MinimalPrime A) :
    TotalQuotientRing A →+* p.val.ResidueField :=
  IsLocalization.lift (M := nonZeroDivisors A) (g := algebraMap A p.val.ResidueField)
    (fun s => isUnit_iff_ne_zero.mpr (by
      rw [Ne, Ideal.algebraMap_residueField_eq_zero]
      exact (nonZeroDivisors_iff_avoids_minimalPrimes A s.val).mp s.property p.val p.property))

@[simp] lemma totalQuotientToResidue_algebraMap [IsReduced A] (p : MinimalPrime A) (a : A) :
    totalQuotientToResidue A p (algebraMap A (TotalQuotientRing A) a) =
      algebraMap A p.val.ResidueField a :=
  IsLocalization.lift_eq _ a

lemma minimalComponentIdeal_le_ker [IsReduced A] (p : MinimalPrime A) :
    minimalComponentIdeal A p ≤ RingHom.ker (totalQuotientToResidue A p) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change totalQuotientToResidue A p (algebraMap A (TotalQuotientRing A) a) = 0
  rw [totalQuotientToResidue_algebraMap, Ideal.algebraMap_residueField_eq_zero]
  exact ha

/-- Each Artinian factor of the total quotient ring is the residue field of its minimal prime. -/
noncomputable def minimalComponentResidueEquiv [IsReduced A] (p : MinimalPrime A) :
    (TotalQuotientRing A ⧸ minimalComponentIdeal A p) ≃+* p.val.ResidueField := by
  let P := minimalComponentIdeal A p
  let B := TotalQuotientRing A ⧸ P
  letI : Field B := Ideal.Quotient.field P
  let f : B →+* p.val.ResidueField :=
    Ideal.Quotient.lift P (totalQuotientToResidue A p) (minimalComponentIdeal_le_ker A p)
  let g : A →+* B := (Ideal.Quotient.mk P).comp (algebraMap A (TotalQuotientRing A))
  have hg : ∀ a : A, g a = 0 ↔ a ∈ p.val := by
    intro a
    change Ideal.Quotient.mk P (algebraMap A (TotalQuotientRing A) a) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change a ∈ P.comap (algebraMap A (TotalQuotientRing A)) ↔ _
    rw [minimalComponentIdeal_under]
  have hzero : p.val ≤ RingHom.ker g := fun a ha => (hg a).mpr ha
  have hunits : p.val.primeCompl ≤ (IsUnit.submonoid B).comap g :=
    fun a ha => isUnit_iff_ne_zero.mpr (fun h => ha ((hg a).mp h))
  let k : p.val.ResidueField →+* B := Ideal.ResidueField.lift p.val g hzero hunits
  have hfk : f.comp k = RingHom.id p.val.ResidueField := by
    apply Ideal.ResidueField.ringHom_ext
    ext a
    change f (k (algebraMap A p.val.ResidueField a)) = algebraMap A p.val.ResidueField a
    dsimp only [k]
    rw [Ideal.ResidueField.lift_algebraMap p.val g hzero hunits a]
    change totalQuotientToResidue A p (algebraMap A (TotalQuotientRing A) a) = _
    exact totalQuotientToResidue_algebraMap A p a
  exact RingEquiv.ofBijective f ⟨RingHom.injective f,
    fun y => ⟨k y, RingHom.congr_fun hfk y⟩⟩

@[simp] lemma minimalComponentResidueEquiv_mk [IsReduced A] (p : MinimalPrime A)
    (x : TotalQuotientRing A) :
    minimalComponentResidueEquiv A p (Ideal.Quotient.mk _ x) =
      totalQuotientToResidue A p x := rfl

/-- The fraction field of `A/p` is the residue field at `p`. -/
noncomputable def minimalResidueFractionEquiv (p : MinimalPrime A) :
    p.val.ResidueField ≃+* MinimalFraction A p :=
  (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ p.val))
    p.val.ResidueField (MinimalFraction A p)).toRingEquiv

@[simp] lemma minimalResidueFractionEquiv_algebraMap (p : MinimalPrime A) (a : A) :
    minimalResidueFractionEquiv A p (algebraMap A p.val.ResidueField a) =
      algebraMap (A ⧸ p.val) (MinimalFraction A p) (Ideal.Quotient.mk p.val a) := by
  change (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ p.val))
    p.val.ResidueField (MinimalFraction A p))
      (algebraMap (A ⧸ p.val) p.val.ResidueField (Ideal.Quotient.mk p.val a)) = _
  exact (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ p.val))
    p.val.ResidueField (MinimalFraction A p)).commutes _

/-- Chinese remainders over the distinct maximal ideals of the zero-dimensional
reduced total quotient ring. The compatibility on `A` makes this isomorphism canonical. -/
theorem existsUnique_totalQuotientEquiv [IsReduced A] :
    ∃! e : TotalQuotientRing A ≃+* (∀ p : MinimalPrime A, MinimalFraction A p),
      ∀ (a : A) (p : MinimalPrime A),
        e (algebraMap A (TotalQuotientRing A) a) p =
          algebraMap (A ⧸ p.val) (MinimalFraction A p) (Ideal.Quotient.mk p.val a) := by
  classical
  let := finite_minimalPrime_family A
  letI := Fintype.ofFinite (MinimalPrime A)
  let e0 : TotalQuotientRing A ≃+*
      (TotalQuotientRing A ⧸ ⨅ p : MinimalPrime A, minimalComponentIdeal A p) :=
    (RingEquiv.quotientBot (TotalQuotientRing A)).symm.trans
      (Ideal.quotEquivOfEq (iInf_minimalComponentIdeal A).symm)
  let e1 := e0.trans (Ideal.quotientInfRingEquivPiQuotient
    (minimalComponentIdeal A) (minimalComponentIdeal_pairwise A))
  let ef := fun p : MinimalPrime A =>
    (minimalComponentResidueEquiv A p).trans (minimalResidueFractionEquiv A p)
  let e := e1.trans (RingEquiv.piCongrRight ef)
  have he : ∀ (a : A) (p : MinimalPrime A),
      e (algebraMap A (TotalQuotientRing A) a) p =
        algebraMap (A ⧸ p.val) (MinimalFraction A p) (Ideal.Quotient.mk p.val a) := by
    intro a p
    change minimalResidueFractionEquiv A p
      (minimalComponentResidueEquiv A p
        ((Ideal.quotientInfRingEquivPiQuotient (minimalComponentIdeal A)
          (minimalComponentIdeal_pairwise A)) (e0 (algebraMap A (TotalQuotientRing A) a)) p)) = _
    simp only [e0, RingEquiv.trans_apply, RingEquiv.quotientBot_symm_mk,
      Ideal.quotEquivOfEq_mk, Ideal.quotientInfRingEquivPiQuotient_mk_apply,
      minimalComponentResidueEquiv_mk, totalQuotientToResidue_algebraMap,
      minimalResidueFractionEquiv_algebraMap]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply RingEquiv.toRingHom_injective
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  ext a p
  exact (he' a p).trans (he a p).symm

/-- The canonical field of a minimal component is the localization at that prime. -/
theorem exists_localization_minimalPrime_equiv [IsReduced A] (p : MinimalPrime A) :
    ∃ e : Localization.AtPrime p.val ≃+* MinimalFraction A p,
      ∀ a : A, e (algebraMap A (Localization.AtPrime p.val) a) =
        algebraMap (A ⧸ p.val) (MinimalFraction A p) (Ideal.Quotient.mk p.val a) := by
  let L := Localization.AtPrime p.val
  letI := (isField_localization_minimalPrime A ⟨p.val, p.property.isPrime⟩ p.property).toField
  let e : L ≃+* p.val.ResidueField :=
    RingEquiv.ofBijective (algebraMap L p.val.ResidueField)
      ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩
  let e' : p.val.ResidueField ≃+* MinimalFraction A p :=
    (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ p.val))
      p.val.ResidueField (MinimalFraction A p)).toRingEquiv
  refine ⟨e.trans e', ?_⟩
  intro a
  change e' (algebraMap L p.val.ResidueField (algebraMap A L a)) = _
  rw [← IsScalarTower.algebraMap_apply A L p.val.ResidueField]
  change e' (algebraMap (A ⧸ p.val) p.val.ResidueField (Ideal.Quotient.mk p.val a)) = _
  exact (IsLocalization.algEquiv (nonZeroDivisors (A ⧸ p.val))
    p.val.ResidueField (MinimalFraction A p)).commutes _

omit [IsNoetherianRing A] in
theorem minimalPrimes_empty_of_subsingleton [Subsingleton A] : IsEmpty (MinimalPrime A) := by
  refine ⟨fun p => p.property.isPrime.ne_top ?_⟩
  exact Subsingleton.elim _ _

omit [IsNoetherianRing A] in
theorem minimalFraction_product_subsingleton [Subsingleton A] :
    Subsingleton (∀ p : MinimalPrime A, MinimalFraction A p) := by
  let := minimalPrimes_empty_of_subsingleton A
  infer_instance

end AdvCommAlg.Normality
