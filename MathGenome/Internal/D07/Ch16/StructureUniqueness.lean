import MathGenome.Internal.Specs.D07.Ch16.StructureUniqueness
import MathGenome.Internal.D07.Ch16.StructureExistence
import MathGenome.Internal.D07.Ch16.FreeGenerators
import MathGenome.Internal.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
import MathGenome.Internal.D07.Ch16.StructureUniquenessInvariantFactorAlignment

universe u v w
noncomputable section
namespace D07.Ch16.StructureUniqueness
open Specs.D07.Ch16.StructureUniqueness
open Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment (Cyclic)
namespace Filtration
export D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants
  (primaryMembership layerDimension exponentMultiplicity)
end Filtration

theorem intrinsicFiltration : IntrinsicFiltration.{u,v} :=
  ⟨Filtration.layerDimension, Filtration.exponentMultiplicity⟩

theorem canonicalAlignment : CanonicalAlignment.{u} :=
  ⟨D07.Ch16.StructureUniquenessInvariantFactorAlignment.exponentAlignment,
   D07.Ch16.StructureUniquenessInvariantFactorAlignment.columnProperties,
   D07.Ch16.StructureUniquenessInvariantFactorAlignment.reconstruction,
   D07.Ch16.StructureUniquenessInvariantFactorAlignment.chainUniqueness,
   D07.Ch16.StructureUniquenessInvariantFactorAlignment.emptyCase⟩

section FreeRank
variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The quotient by the intrinsic torsion submodule is the displayed free
part, for every decomposition, including free rank zero. -/
def torsionQuotientEquiv (r s : ℕ) (d : Fin s → R) (hd : ∀ i, d i ≠ 0)
    (E : M ≃ₗ[R] ((Fin r → R) × (∀ i, Cyclic R (d i)))) :
    (M ⧸ Submodule.torsion R M) ≃ₗ[R] (Fin r → R) := by
  let f : M →ₗ[R] (Fin r → R) := (LinearMap.fst R _ _).comp E.toLinearMap
  have hf : Function.Surjective f := fun y => ⟨E.symm (y, 0), by simp [f]⟩
  have hk : f.ker = Submodule.torsion R M := by
    ext x
    change f x = 0 ↔ x ∈ Submodule.torsion R M
    rw [Submodule.mem_torsion_iff]
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := @D07.Ch16.StructureExistence.quotientProduct_torsion
        R _ _ (Fin s) _ d hd (E x).2
      refine ⟨a, E.injective ?_⟩
      change E ((a : R) • x) = E 0
      rw [map_smul, map_zero]
      exact Prod.ext (by change (a : R) • f x = 0; rw [hx, smul_zero]) ha
    · rintro ⟨a, ha⟩
      change (a : R) • x = 0 at ha
      have h : (a : R) • f x = 0 := by rw [← map_smul, ha, map_zero]
      funext i
      exact (mul_eq_zero.mp (congrFun h i)).resolve_left (nonZeroDivisors.coe_ne_zero a)
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)

end FreeRank

theorem freeRankUniqueness : FreeRankUniqueness.{u,v} := by
  intro R _ _ M _ _ r s r' s' d d' hd hd' E E'
  exact D07.Ch16.FreeGenerators.finiteFreeRankInvariant R r r'
    ((torsionQuotientEquiv r s d hd E).symm.trans
      (torsionQuotientEquiv r' s' d' hd' E'))

/-- Counting a prime/exponent pair is counting a finite coordinate fiber. -/
lemma elementaryData_count {R : Type u} [CommRing R] {t : ℕ}
    (q : Fin t → R) (e : Fin t → ℕ) (p : R) (k : ℕ)
    [DecidableEq (Associates R × ℕ)] :
    (elementaryData q e).count (Associates.mk p, k) =
      Nat.card {i : Fin t // Associated p (q i) ∧ e i = k} := by
  classical
  simp only [elementaryData, Multiset.count_map, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _
  simp [Prod.mk.injEq, Associates.mk_eq_mk_iff_associated, eq_comm]

/-- The consecutive intrinsic layer dimensions determine every fiber, without
normalizing prime representatives in either input decomposition. -/
lemma elementaryData_eq {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (r t r' t' : ℕ)
    (q : Fin t → R) (e : Fin t → ℕ) (q' : Fin t' → R) (e' : Fin t' → ℕ)
    (hq : ∀ i, Prime (q i) ∧ 0 < e i) (hq' : ∀ i, Prime (q' i) ∧ 0 < e' i)
    (E : M ≃ₗ[R] ((Fin r → R) × (∀ i, Cyclic R (q i ^ e i))))
    (E' : M ≃ₗ[R] ((Fin r' → R) × (∀ i, Cyclic R (q' i ^ e' i)))) :
    elementaryData q e = elementaryData q' e' := by
  classical
  have hcount (p : R) (hp : Prime p) (k : ℕ) (hk : 0 < k) :
      (elementaryData q e).count (Associates.mk p, k) =
        (elementaryData q' e').count (Associates.mk p, k) := by
    rw [elementaryData_count, elementaryData_count]
    exact (Filtration.exponentMultiplicity R M r t q e hq E p hp.irreducible k hk).symm.trans
      (Filtration.exponentMultiplicity R M r' t' q' e' hq' E' p hp.irreducible k hk)
  apply Multiset.ext.mpr
  intro a
  by_cases h : a ∈ elementaryData q e ∨ a ∈ elementaryData q' e'
  · rcases h with h | h
    · obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h
      rw [← hi]
      exact hcount (q i) (hq i).1 (e i) (hq i).2
    · obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp h
      rw [← hi]
      exact hcount (q' i) (hq' i).1 (e' i) (hq' i).2
  · rw [Multiset.count_eq_zero.mpr (fun ha => h (Or.inl ha)),
      Multiset.count_eq_zero.mpr (fun ha => h (Or.inr ha))]

theorem primaryUniqueness : PrimaryUniqueness.{u,v} := by
  intro R _ _ _ M _ _ _ r t r' t' q e q' e' hq hq' E E'
  have h := elementaryData_eq r t r' t' q e q' e' hq hq' E E'
  refine ⟨freeRankUniqueness R M r t r' t' _ _
    (fun i => pow_ne_zero _ (hq i).1.ne_zero)
    (fun i => pow_ne_zero _ (hq' i).1.ne_zero) E E', ?_, h⟩
  simpa [elementaryData] using congrArg Multiset.card h

/-- The filtration count with an arbitrary finite coordinate index. -/
lemma indexedExponentMultiplicity {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {ι : Type w} [Fintype ι]
    (r : ℕ) (q : ι → R) (e : ι → ℕ)
    (hq : ∀ i, Prime (q i) ∧ 0 < e i)
    (E : M ≃ₗ[R] ((Fin r → R) × (∀ i, Cyclic R (q i ^ e i))))
    (p : R) (hp : Irreducible p) (k : ℕ) (hk : 1 ≤ k) :
    letI := Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants.residueField p hp
    Module.finrank (R ⧸ Ideal.span {p})
      (Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants.primaryLayer p k M) -
    Module.finrank (R ⧸ Ideal.span {p})
      (Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants.primaryLayer p (k+1) M) =
      Nat.card {i : ι // Associated p (q i) ∧ e i = k} := by
  classical
  let a := (Fintype.equivFin ι).symm
  let V := (LinearEquiv.piCongrLeft R (fun i => Cyclic R (q i ^ e i)) a).symm
  exact (Filtration.exponentMultiplicity R M r (Fintype.card ι)
    (fun i => q (a i)) (fun i => e (a i)) (fun i => hq (a i))
    (E.trans ((LinearEquiv.refl R _).prodCongr V)) p hp k hk).trans
      (Nat.card_congr (Equiv.subtypeEquiv a (fun _ => Iff.rfl)))

namespace Alignment
open Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment
  (PrimeData PositiveData HasElementaryDivisors positiveMultiplicities width column)

lemma associated_iff_eq {R : Type u} [CommRing R] {s : Finset R}
    (hs : PrimeData s) (p q : s) : Associated (p : R) (q : R) ↔ p = q := by
  constructor
  · intro h
    by_contra hn
    exact hs.2 p.property q.property (fun he => hn (Subtype.ext he)) h
  · rintro rfl
    exact Associated.refl _

lemma sortedExponent_positive {R : Type u} {s : Finset R} {E : R → Multiset ℕ}
    (hE : PositiveData s E) (p : s) (j : Fin (E p).card) :
    0 < ((E p).sort (· ≤ ·)).getD j.val 0 := by
  have hj : j.val < ((E p).sort (· ≤ ·)).length := by simp
  rw [List.getD_eq_getElem _ _ hj]
  exact hE p p.property _ ((Multiset.mem_sort _).mp (List.getElem_mem hj))

lemma sortedExponent_count (A : Multiset ℕ) (k : ℕ) :
    Nat.card {j : Fin A.card // (A.sort (· ≤ ·)).getD j.val 0 = k} = A.count k := by
  classical
  let f : Fin A.card → ℕ := fun j => (A.sort (· ≤ ·)).getD j.val 0
  have hf : List.ofFn f = A.sort (· ≤ ·) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [f, List.getD]
  calc
    _ = (Finset.univ.val.map f).count k := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def,
        Finset.filter_val, Multiset.count_map]
      congr 1
      apply Multiset.filter_congr
      intro j _
      exact eq_comm
    _ = A.count k := by rw [Fin.univ_val_map, hf, Multiset.sort_eq]

/-- For canonical column data, the filtration recovers precisely the original
positive exponent multiset at each representative prime. -/
lemma canonicalMultiplicity {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (r : ℕ) (s : Finset R) (E : R → Multiset ℕ)
    (hs : PrimeData s) (hE : PositiveData s E)
    (F : M ≃ₗ[R] ((Fin r → R) × ((p : s) → (j : Fin (E p).card) →
      Cyclic R ((p : R) ^ ((E p).sort (· ≤ ·)).getD j.val 0))))
    (p : s) (k : ℕ) (hk : 1 ≤ k) :
    letI := Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants.residueField
      (p : R) (hs.1 p p.property).irreducible
    Module.finrank (R ⧸ Ideal.span {(p : R)})
      (Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants.primaryLayer (p : R) k M) -
    Module.finrank (R ⧸ Ideal.span {(p : R)})
      (Specs.D07.Ch16.StructureUniquenessPrimaryFiltrationInvariants.primaryLayer (p : R) (k+1) M) =
      (E p).count k := by
  classical
  let J := (p : s) × Fin (E p).card
  let q : J → R := fun x => x.1.val
  let e : J → ℕ := fun x => ((E x.1).sort (· ≤ ·)).getD x.2.val 0
  let V := (LinearEquiv.piCurry R (fun (p : s) (j : Fin (E p).card) =>
    Cyclic R ((p : R) ^ ((E p).sort (· ≤ ·)).getD j.val 0))).symm
  have h := indexedExponentMultiplicity r q e
    (fun i => ⟨hs.1 i.1 i.1.property, sortedExponent_positive hE i.1 i.2⟩)
    (F.trans ((LinearEquiv.refl R _).prodCongr V)) p
    (hs.1 p p.property).irreducible k hk
  apply h.trans
  change Nat.card {i : J // Associated (p : R) i.1.val ∧ e i = k} = _
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single p]
  · simpa only [associated_iff_eq hs, e, true_and, ite_true,
      Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter] using
      sortedExponent_count (E p) k
  · intro b _ hbp
    simp only [associated_iff_eq hs, Ne.symm hbp, false_and, ite_false, Finset.sum_const_zero]
  · simp

/-- Chain uniqueness and CRT give the canonical elementary coordinates for
any input chain; the input is not required to carry a factorization witness. -/
lemma chainCanonicalEquiv {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (s : Finset R) (E : R → Multiset ℕ)
    (hs : PrimeData s) (hE : PositiveData s E)
    (n : ℕ) (d : Fin n → R) (hd : ∀ i, d i ≠ 0 ∧ ¬IsUnit (d i))
    (hc : ∀ i j, i ≤ j → d i ∣ d j) (he : HasElementaryDivisors s E d) :
    Nonempty (((i : Fin n) → Cyclic R (d i)) ≃ₗ[R]
      ((p : s) → (j : Fin (E p).card) →
        Cyclic R ((p : R) ^ ((E p).sort (· ≤ ·)).getD j.val 0))) := by
  obtain ⟨hn, ha⟩ := D07.Ch16.StructureUniquenessInvariantFactorAlignment.chainUniqueness
    R s E hs hE n d hd hc he
  subst n
  let U := LinearEquiv.piCongrRight (R := R) (fun i =>
    Submodule.quotEquivOfEq _ _ (Ideal.span_singleton_eq_span_singleton.mpr (ha i)))
  exact ⟨U.trans (Classical.choice
    (D07.Ch16.StructureUniquenessInvariantFactorAlignment.reconstruction R s E hs hE))⟩

section Support
open UniqueFactorizationMonoid
variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [NormalizationMonoid R] [DecidableEq R]

noncomputable def primeSupport {n : ℕ} (d : Fin n → R) : Finset R := by
  classical
  exact Finset.univ.biUnion fun i => (normalizedFactors (d i)).toFinset

lemma mem_primeSupport {n : ℕ} (d : Fin n → R) (p : R) :
    p ∈ primeSupport d ↔ ∃ i, p ∈ normalizedFactors (d i) := by
  classical
  simp only [primeSupport, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Multiset.mem_toFinset]

lemma support_primeData {n m : ℕ} (d : Fin n → R) (d' : Fin m → R) :
    PrimeData (primeSupport d ∪ primeSupport d') := by
  classical
  have hnorm (p : R) (hp : p ∈ primeSupport d ∪ primeSupport d') :
      Prime p ∧ normalize p = p := by
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨i, hi⟩ := (mem_primeSupport d p).mp hp
      exact ⟨prime_of_normalized_factor p hi, normalize_normalized_factor p hi⟩
    · obtain ⟨i, hi⟩ := (mem_primeSupport d' p).mp hp
      exact ⟨prime_of_normalized_factor p hi, normalize_normalized_factor p hi⟩
  refine ⟨fun p hp => (hnorm p hp).1, ?_⟩
  intro p hp q hq hpq ha
  apply hpq
  have h := normalize_eq_normalize_iff_associated.mpr ha
  rwa [(hnorm p hp).2, (hnorm q hq).2] at h

omit [IsDomain R] [IsPrincipalIdealRing R] [NormalizationMonoid R] [DecidableEq R] in
lemma positiveData {n : ℕ} (s : Finset R) (d : Fin n → R) :
    PositiveData s (fun p => positiveMultiplicities p d) := by
  intro p _ e he
  change e ∈ ((List.ofFn fun i => multiplicity p (d i)).filter (· != 0)) at he
  have := (List.mem_filter.mp he).2
  exact Nat.pos_of_ne_zero (by simpa using this)

lemma elementaryDivisors_on_support {n : ℕ} (s : Finset R) (d : Fin n → R)
    (hd : ∀ i, d i ≠ 0) (hs : primeSupport d ⊆ s) :
    HasElementaryDivisors s (fun p => positiveMultiplicities p d) d := by
  refine ⟨fun _ _ => rfl, ?_⟩
  intro q hq ha i
  apply multiplicity_eq_zero_of_not_dvd
  intro hdiv
  obtain ⟨p, hp, hqp⟩ := exists_mem_normalizedFactors_of_dvd (hd i) hq.irreducible hdiv
  exact ha p (hs ((mem_primeSupport d p).mpr ⟨i, hp⟩)) hqp

end Support
end Alignment

/-- Uniqueness of the entire ordered invariant-factor list follows by
recovering its positive prime-exponent lists from the intrinsic filtration. -/
theorem invariantFactorUniqueness : InvariantFactorUniqueness.{u,v} := by
  classical
  intro R _ _ _ M _ _ _ r n r' n' d d' hd hd' hc hc' F F'
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := R)
  let s := Alignment.primeSupport d ∪ Alignment.primeSupport d'
  let E : R → Multiset ℕ := fun p =>
    Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment.positiveMultiplicities p d
  let E' : R → Multiset ℕ := fun p =>
    Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment.positiveMultiplicities p d'
  have hs := Alignment.support_primeData d d'
  have hE := Alignment.positiveData s d
  have hE' := Alignment.positiveData s d'
  have he := Alignment.elementaryDivisors_on_support s d (fun i => (hd i).1)
    Finset.subset_union_left
  have he' := Alignment.elementaryDivisors_on_support s d' (fun i => (hd' i).1)
    Finset.subset_union_right
  obtain ⟨U⟩ := Alignment.chainCanonicalEquiv s E hs hE n d hd hc he
  obtain ⟨U'⟩ := Alignment.chainCanonicalEquiv s E' hs hE' n' d' hd' hc' he'
  have hEE' (p : s) : E p = E' p := by
    apply Multiset.ext.mpr
    intro k
    by_cases hk : k = 0
    · subst k
      rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
      · intro h
        exact (Nat.lt_irrefl 0) (hE' p p.property 0 h)
      · intro h
        exact (Nat.lt_irrefl 0) (hE p p.property 0 h)
    · exact (Alignment.canonicalMultiplicity r s E hs hE
        (F.trans ((LinearEquiv.refl R _).prodCongr U)) p k (Nat.pos_of_ne_zero hk)).symm.trans
        (Alignment.canonicalMultiplicity r' s E' hs hE'
          (F'.trans ((LinearEquiv.refl R _).prodCongr U')) p k (Nat.pos_of_ne_zero hk))
  have he'' : Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment.HasElementaryDivisors
      s E d' := by
    refine ⟨fun p hp => (he'.1 p hp).trans (hEE' ⟨p,hp⟩).symm, he'.2⟩
  obtain ⟨hn, ha⟩ := D07.Ch16.StructureUniquenessInvariantFactorAlignment.chainUniqueness
    R s E hs hE n d hd hc he
  obtain ⟨hn', ha'⟩ := D07.Ch16.StructureUniquenessInvariantFactorAlignment.chainUniqueness
    R s E hs hE n' d' hd' hc' he''
  have hr := freeRankUniqueness R M r n r' n' d d'
    (fun i => (hd i).1) (fun i => (hd' i).1) F F'
  refine ⟨hr, hn.trans hn'.symm, ?_⟩
  intro i
  apply (ha i).trans
  have hcast : Fin.cast hn' (Fin.cast (hn.trans hn'.symm) i) = Fin.cast hn i := Fin.ext rfl
  simpa only [hcast] using (ha' (Fin.cast (hn.trans hn'.symm) i)).symm


/-- Transport from finite direct sums explicitly, so the theorem applies to
the upstream structure theorem's representation without changing its objects. -/
theorem directSumPrimaryUniqueness : DirectSumPrimaryUniqueness.{u,v} := by
  intro R _ _ _ M _ _ _ r t r' t' q e q' e' hq hq' F F'
  let U := DirectSum.linearEquivFunOnFintype R (Fin t) (fun i => Cyclic R (q i ^ e i))
  let U' := DirectSum.linearEquivFunOnFintype R (Fin t') (fun i => Cyclic R (q' i ^ e' i))
  obtain ⟨hr, ht, he⟩ := primaryUniqueness R M r t r' t' q e q' e' hq hq'
    (F.trans ((LinearEquiv.refl R _).prodCongr U))
    (F'.trans ((LinearEquiv.refl R _).prodCongr U'))
  refine ⟨hr, ht, he, ?_⟩
  simpa only [elementaryData, Multiset.map_map, Function.comp_apply, Associates.mk_pow] using
    congrArg (Multiset.map (fun a : Associates R × ℕ => a.1 ^ a.2)) he

theorem directSumInvariantFactorUniqueness : DirectSumInvariantFactorUniqueness.{u,v} := by
  intro R _ _ _ M _ _ _ r n r' n' d d' hd hd' hc hc' F F'
  let U := DirectSum.linearEquivFunOnFintype R (Fin n) (fun i => Cyclic R (d i))
  let U' := DirectSum.linearEquivFunOnFintype R (Fin n') (fun i => Cyclic R (d' i))
  exact invariantFactorUniqueness R M r n r' n' d d' hd hd' hc hc'
    (F.trans ((LinearEquiv.refl R _).prodCongr U))
    (F'.trans ((LinearEquiv.refl R _).prodCongr U'))

end D07.Ch16.StructureUniqueness
