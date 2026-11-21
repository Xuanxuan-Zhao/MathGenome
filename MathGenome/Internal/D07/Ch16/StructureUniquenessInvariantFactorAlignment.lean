import MathGenome.Internal.Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment
import MathGenome.Internal.D07.Ch09.CrtFiniteInteger
import MathGenome.Internal.D07.Ch10.UfdGcd
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.Algebra.Equiv

universe u
namespace D07.Ch16.StructureUniquenessInvariantFactorAlignment
open Specs.D07.Ch16.StructureUniquenessInvariantFactorAlignment
open scoped BigOperators

lemma padded_length (n : ℕ) (A : Multiset ℕ) (h : A.card ≤ n) :
    (padded n A).length = n := by
  simp [padded, Nat.sub_add_cancel h]

lemma padded_sorted (n : ℕ) (A : Multiset ℕ) : (padded n A).SortedLE := by
  apply List.sortedLE_append.mpr
  refine ⟨List.sortedLE_replicate _, (Multiset.pairwise_sort _ _).sortedLE, ?_⟩
  intro a ha b _
  have : a = 0 := (List.mem_replicate.mp ha).2
  simp [this]

lemma padded_positive (n : ℕ) (A : Multiset ℕ) (h : ∀ e ∈ A, 0 < e) :
    (((padded n A).filter (· != 0) : List ℕ) : Multiset ℕ) = A := by
  have hf : (A.sort (· ≤ ·)).filter (· != 0) = A.sort (· ≤ ·) := by
    apply List.filter_eq_self.mpr
    intro a ha
    simpa using (h a ((Multiset.mem_sort _).mp ha)).ne'
  simp [padded, List.filter_append, hf]

lemma ofFn_exponent {R : Type u} (s : Finset R) (E : R → Multiset ℕ)
    (p : R) (hp : p ∈ s) :
    List.ofFn (exponent s E p) = padded (width s E) (E p) := by
  have hl := padded_length (width s E) (E p) (Finset.le_sup (f := fun p => (E p).card) hp)
  apply List.ext_getElem
  · simpa using hl.symm
  · intro i hi hj
    simp [exponent, List.getD, hj]

theorem exponentAlignment : ExponentAlignment.{u} := by
  intro R s E h p hp
  have hf := ofFn_exponent s E p hp
  constructor
  · apply List.sortedLE_ofFn_iff.mp
    rw [hf]
    exact padded_sorted _ _
  · rw [hf]
    exact padded_positive _ _ (h p hp)

theorem emptyCase : EmptyCase.{u} := by
  intro R s E
  constructor
  · intro h p hp
    apply Multiset.card_eq_zero.mp
    have := Finset.le_sup (f := fun p => (E p).card) hp
    change (E p).card ≤ width s E at this
    omega
  · intro h
    apply le_antisymm _ (Nat.zero_le _)
    exact Finset.sup_le fun p hp => by simp [h p hp]


lemma multiplicity_column_mem {R : Type u} [CommRing R] [IsDomain R]
    (s : Finset R) (E : R → Multiset ℕ) (hs : PrimeData s)
    {p : R} (hp : p ∈ s) (i : Fin (width s E)) :
    multiplicity p (column s E i) = exponent s E p i := by
  apply multiplicity_eq_of_emultiplicity_eq_some
  exact D07.Ch10.UfdGcd.emultiplicity_product_of_mem s _ hs.1 hs.2 hp

lemma multiplicity_column_absent {R : Type u} [CommRing R] [IsDomain R]
    (s : Finset R) (E : R → Multiset ℕ) (hs : PrimeData s)
    {p : R} (hp : Prime p) (habs : ∀ q ∈ s, ¬Associated p q)
    (i : Fin (width s E)) : multiplicity p (column s E i) = 0 := by
  apply multiplicity_eq_of_emultiplicity_eq_some
  exact D07.Ch10.UfdGcd.emultiplicity_product_of_absent s _ hs.1 hp habs

lemma column_ne_zero {R : Type u} [CommRing R] [IsDomain R]
    (s : Finset R) (E : R → Multiset ℕ) (hs : PrimeData s)
    (i : Fin (width s E)) : column s E i ≠ 0 :=
  D07.Ch10.UfdGcd.primePowerProduct_ne_zero s _ hs.1

lemma column_not_isUnit {R : Type u} [CommRing R] [IsDomain R]
    (s : Finset R) (E : R → Multiset ℕ) (hs : PrimeData s)
    (hE : PositiveData s E) (i : Fin (width s E)) : ¬IsUnit (column s E i) := by
  classical
  have hne : s.Nonempty := by
    by_contra hn
    have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have : width s E = 0 := by simp [width, hz]
    exact (Nat.not_lt_zero i.val) (this ▸ i.isLt)
  obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup s hne (fun p => (E p).card)
  change width s E = (E p).card at he
  have hi : i.val < ((E p).sort (· ≤ ·)).length := by simp [← he]
  have hexp : 0 < exponent s E p i := by
    simp only [exponent, padded, he, Nat.sub_self, List.replicate_zero, List.nil_append]
    rw [List.getD_eq_getElem _ _ hi]
    exact hE p hp _ ((Multiset.mem_sort _).mp (List.getElem_mem hi))
  have hd : p ∣ column s E i :=
    (dvd_pow_self p hexp.ne').trans (Finset.dvd_prod_of_mem _ hp)
  intro hu
  exact (hs.1 p hp).not_isUnit (isUnit_of_dvd_unit hd hu)

theorem columnProperties : ColumnProperties.{u} := by
  intro R _ _ _ s E hs hE
  refine ⟨fun i => ⟨column_ne_zero s E hs i, column_not_isUnit s E hs hE i⟩,
    ?_, ?_⟩
  · intro i j hij
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    exact pow_dvd_pow p ((exponentAlignment R s E hE p hp).1 hij)
  · constructor
    · intro p hp
      unfold positiveMultiplicities
      simp_rw [multiplicity_column_mem s E hs hp]
      exact (exponentAlignment R s E hE p hp).2
    · intro p hp habs i
      exact multiplicity_column_absent s E hs hp habs i


lemma count_zero_add_positive_length (l : List ℕ) :
    l.count 0 + (l.filter (· != 0)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : a = 0 <;> simp_all <;> omega

lemma sorted_eq_of_positive_filter {l k : List ℕ}
    (hl : l.SortedLE) (hk : k.SortedLE) (hlen : l.length = k.length)
    (hf : ((l.filter (· != 0) : List ℕ) : Multiset ℕ) =
      ((k.filter (· != 0) : List ℕ) : Multiset ℕ)) : l = k := by
  apply List.Perm.eq_of_sortedLE hl hk
  apply List.perm_iff_count.mpr
  intro a
  have hc := congrArg (Multiset.count a) hf
  simp only [Multiset.coe_count] at hc
  by_cases ha : a = 0
  · subst a
    have hfLen := congrArg Multiset.card hf
    simp only [Multiset.coe_card] at hfLen
    have h1 := count_zero_add_positive_length l
    have h2 := count_zero_add_positive_length k
    omega
  · simpa only [List.count_filter (p := (· != 0)) (a := a) (by simpa using ha)] using hc

lemma chain_width {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (s : Finset R) (E : R → Multiset ℕ) (hs : PrimeData s)
    (n : ℕ) (d : Fin n → R) (hd : ∀ i, d i ≠ 0 ∧ ¬IsUnit (d i))
    (hchain : ∀ i j, i ≤ j → d i ∣ d j) (hdata : HasElementaryDivisors s E d) :
    n = width s E := by
  classical
  have hupper : width s E ≤ n := by
    apply Finset.sup_le
    intro p hp
    rw [← hdata.1 p hp]
    change (List.filter (· != 0) (List.ofFn fun i => multiplicity p (d i))).length ≤ n
    exact (List.length_filter_le _ _).trans_eq List.length_ofFn
  apply le_antisymm _ hupper
  by_cases hn : n = 0
  · omega
  let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor (hd i0).2 (hd i0).1
  have hqP : Prime q := hq.prime
  have hex : ∃ p ∈ s, Associated q p := by
    by_contra habs
    have hz := hdata.2 q hqP (by simpa only [not_exists, not_and] using habs) i0
    have hpos := multiplicity_pos_of_dvd hqd (FiniteMultiplicity.of_prime_left hqP (hd i0).1)
    omega
  obtain ⟨p, hp, hqp⟩ := hex
  have hpdiv (i : Fin n) : p ∣ d i :=
    hqp.symm.dvd.trans (hqd.trans (hchain i0 i (by exact Fin.mk_le_mk.mpr (Nat.zero_le _))))
  have hfilter : (List.ofFn fun i => multiplicity p (d i)).filter (· != 0) =
      List.ofFn fun i => multiplicity p (d i) := by
    apply List.filter_eq_self.mpr
    intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    simpa using (multiplicity_pos_of_dvd (hpdiv i)
      (FiniteMultiplicity.of_prime_left (hs.1 p hp) (hd i).1)).ne'
  have hcard : (E p).card = n := by
    rw [← hdata.1 p hp]
    simp [positiveMultiplicities, hfilter]
  exact hcard ▸ Finset.le_sup (f := fun p => (E p).card) hp

lemma chain_exponent {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (s : Finset R) (E : R → Multiset ℕ) (hs : PrimeData s) (hE : PositiveData s E)
    (d : Fin (width s E) → R) (hd : ∀ i, d i ≠ 0 ∧ ¬IsUnit (d i))
    (hchain : ∀ i j, i ≤ j → d i ∣ d j) (hdata : HasElementaryDivisors s E d)
    {p : R} (hp : p ∈ s) (i : Fin (width s E)) :
    multiplicity p (d i) = exponent s E p i := by
  have hmono : Monotone (fun i => multiplicity p (d i)) := by
    intro i j hij
    exact (UniqueFactorizationMonoid.dvd_iff_multiplicity_le (hd i).1 (hd j).1).mp
      (hchain i j hij) p (hs.1 p hp)
  have heq := sorted_eq_of_positive_filter hmono.sortedLE_ofFn
    (exponentAlignment R s E hE p hp).1.sortedLE_ofFn
    (by simp) ((hdata.1 p hp).trans (exponentAlignment R s E hE p hp).2.symm)
  have hh := congrArg (fun l : List ℕ => l.getD i.val 0) heq
  simpa using hh

theorem chainUniqueness : ChainUniqueness.{u} := by
  intro R _ _ _ s E hs hE n d hd hchain hdata
  have h := chain_width s E hs n d hd hchain hdata
  subst n
  refine ⟨rfl, ?_⟩
  intro i
  apply (UniqueFactorizationMonoid.associated_iff_multiplicity_eq
    (hd i).1 (column_ne_zero s E hs i)).mpr
  intro q hq
  by_cases hex : ∃ p ∈ s, Associated q p
  · obtain ⟨p, hp, hqp⟩ := hex
    simp_rw [← multiplicity_eq_of_associated_left hqp]
    exact (chain_exponent s E hs hE d hd hchain hdata hp i).trans
      (multiplicity_column_mem s E hs hp i).symm
  · have habs : ∀ p ∈ s, ¬Associated q p := by
      simpa only [not_exists, not_and] using hex
    rw [hdata.2 q hq habs i, multiplicity_column_absent s E hs hq habs i]


noncomputable def columnCRT {R : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (s : Finset R) (E : R → Multiset ℕ)
    (hs : PrimeData s) (i : Fin (width s E)) :
    Cyclic R (column s E i) ≃ₗ[R]
      ((p : s) → Cyclic R ((p : R) ^ exponent s E p i)) := by
  classical
  apply Classical.choice
  let I : s → Ideal R := fun p => Ideal.span {(p : R) ^ exponent s E p i}
  have hI : ∀ p q : s, p ≠ q →
      Specs.D07.Ch09.Comaximal.comaximalPredicateValue (I p) (I q) := by
    intro p q hpq
    apply Ideal.isCoprime_iff_sup_eq.mp
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    apply IsCoprime.pow
    apply (hs.1 p p.property).coprime_iff_not_dvd.mpr
    intro hdvd
    exact hs.2 p.property q.property (fun he => hpq (Subtype.ext he))
      (((hs.1 p p.property).irreducible.dvd_irreducible_iff_associated
        (hs.1 q q.property).irreducible).mp hdvd)
  obtain ⟨hinter, e, he⟩ := D07.Ch09.CrtFiniteInteger.finiteCRT R s I hI
  have hprod : (∏ p : s, I p) = Ideal.span {column s E i} := by
    change (∏ p : s, Ideal.span {(p : R) ^ exponent s E p i}) = _
    rw [Ideal.prod_span_singleton]
    exact congrArg (fun a : R => Ideal.span {a})
      (Finset.prod_coe_sort s (fun p => p ^ exponent s E p i))
  have ht : (⨅ p : s, I p) = Ideal.span {column s E i} := hinter.trans hprod
  let e' := (Ideal.quotEquivOfEq ht.symm).trans e
  exact ⟨(AlgEquiv.ofRingEquiv (R := R) (f := e') (fun r => by
    ext p
    exact he r p)).toLinearEquiv⟩

lemma prefix_getD (m : ℕ) (l : List ℕ) (i : ℕ) (hi : i < m) :
    (List.replicate m 0 ++ l).getD i 0 = 0 := by
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD]

lemma suffix_getD (m : ℕ) (l : List ℕ) (i : ℕ) :
    (List.replicate m 0 ++ l).getD (m + i) 0 = l.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

noncomputable def cyclicCongr {R : Type u} [CommRing R] {a b : R} (h : a = b) :
    Cyclic R a ≃ₗ[R] Cyclic R b := by
  subst b
  exact LinearEquiv.refl _ _

noncomputable def removeZeroPrefix {R : Type u} [CommRing R]
    (p : R) (m : ℕ) (A : Multiset ℕ) :
    ((i : Fin (m + A.card)) →
      Cyclic R (p ^ (List.replicate m 0 ++ A.sort (· ≤ ·)).getD i.val 0)) ≃ₗ[R]
    ((j : Fin A.card) → Cyclic R (p ^ (A.sort (· ≤ ·)).getD j.val 0)) := by
  let M : Fin (m + A.card) → Type u := fun i =>
    Cyclic R (p ^ (List.replicate m 0 ++ A.sort (· ≤ ·)).getD i.val 0)
  have hsub (i : Fin m) : Subsingleton (M (finSumFinEquiv (Sum.inl i))) := by
    dsimp [M]
    rw [prefix_getD m _ i.val i.isLt, pow_zero]
    exact Ideal.Quotient.subsingleton_iff.mpr (by simp)
  letI : ∀ i : Fin m, Subsingleton (M (finSumFinEquiv (Sum.inl i))) := hsub
  letI : Unique ((i : Fin m) → M (finSumFinEquiv (Sum.inl i))) := Unique.mk' _
  let e := (LinearEquiv.piCongrLeft R M finSumFinEquiv).symm |>.trans
    ((LinearEquiv.sumPiEquivProdPi R (Fin m) (Fin A.card)
      (fun z => M (finSumFinEquiv z))).trans LinearEquiv.uniqueProd)
  exact e.trans (LinearEquiv.piCongrRight (R := R) (fun j : Fin A.card =>
    cyclicCongr (congrArg (fun t => p ^ t) (suffix_getD m (A.sort (· ≤ ·)) j.val))))

noncomputable def paddedModuleEquiv {R : Type u} [CommRing R]
    (p : R) (n : ℕ) (A : Multiset ℕ) (h : A.card ≤ n) :
    ((i : Fin n) → Cyclic R (p ^ (padded n A).getD i.val 0)) ≃ₗ[R]
    ((j : Fin A.card) → Cyclic R (p ^ (A.sort (· ≤ ·)).getD j.val 0)) := by
  generalize hk : n - A.card = k
  have hn : n = k + A.card := by omega
  subst n
  unfold padded
  rw [Nat.add_sub_cancel_right]
  exact removeZeroPrefix p k A

noncomputable def transposeLinearEquiv {R : Type u} [CommRing R]
    {ι κ : Type*} (M : ι → κ → Type*) [∀ i j, AddCommGroup (M i j)]
    [∀ i j, Module R (M i j)] :
    ((i : ι) → (j : κ) → M i j) ≃ₗ[R] ((j : κ) → (i : ι) → M i j) where
  toFun f j i := f i j
  invFun f i j := f j i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem reconstruction : Reconstruction.{u} := by
  intro R _ _ _ s E hs _
  classical
  let e1 : ((i : Fin (width s E)) → Cyclic R (column s E i)) ≃ₗ[R]
      ((i : Fin (width s E)) → (p : s) → Cyclic R ((p : R) ^ exponent s E p i)) :=
    LinearEquiv.piCongrRight (fun i => columnCRT s E hs i)
  let e2 : ((i : Fin (width s E)) → (p : s) → Cyclic R ((p : R) ^ exponent s E p i)) ≃ₗ[R]
      ((p : s) → (i : Fin (width s E)) → Cyclic R ((p : R) ^ exponent s E p i)) :=
    transposeLinearEquiv _
  let e3 : ((p : s) → (i : Fin (width s E)) → Cyclic R ((p : R) ^ exponent s E p i)) ≃ₗ[R]
      ((p : s) → (j : Fin (E p).card) →
        Cyclic R ((p : R) ^ ((E p).sort (· ≤ ·)).getD j.val 0)) :=
    LinearEquiv.piCongrRight (fun p : s =>
      paddedModuleEquiv (p : R) (width s E) (E p)
        (Finset.le_sup (f := fun p => (E p).card) p.property))
  exact ⟨e1.trans (e2.trans e3)⟩

end D07.Ch16.StructureUniquenessInvariantFactorAlignment
