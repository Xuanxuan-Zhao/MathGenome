import MathGenome.Internal.Specs.D07.Ch07.ClassificationDataConversion
import Mathlib.Tactic.Ext
import Mathlib.Data.ZMod.QuotientRing

namespace D07.Ch07.ClassificationDataConversion

@[simp] theorem row_length (E : ElementaryData) (p : ℕ) :
    (row E p).length = (E p).card := by simp [row]

@[simp] theorem row_multiset (E : ElementaryData) (p : ℕ) :
    (row E p : Multiset ℕ) = E p := by simp [row]

theorem row_sorted (E : ElementaryData) (p : ℕ) :
    (row E p).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _

theorem row_positive {E : ElementaryData} (hE : IsElementary E) (p : ℕ) :
    ∀ e ∈ row E p, 0 < e := by
  intro e he
  exact (hE p e (by simpa [row] using he)).2

theorem row_length_le_width (E : ElementaryData) (p : ℕ) :
    (row E p).length ≤ width E := by
  rw [row_length]
  by_cases hp : p ∈ E.support
  · exact Finset.le_sup (f := fun p => (E p).card) hp
  · simp [Finsupp.notMem_support_iff.mp hp]

theorem pad_length {r : ℕ} {l : List ℕ} (h : l.length ≤ r) :
    (pad r l).length = r := by simp [pad]; omega

theorem pad_sorted {r : ℕ} {l : List ℕ} (h : l.Pairwise (· ≤ ·)) :
    (pad r l).Pairwise (· ≤ ·) := by
  simp only [pad, List.pairwise_append]
  exact ⟨by simp, h, by simp⟩

theorem filter_pad {r : ℕ} {l : List ℕ} (h : ∀ e ∈ l, 0 < e) :
    (pad r l).filter (· != 0) = l := by
  simp only [pad, List.filter_append]
  have hl : l.filter (· != 0) = l := List.filter_eq_self.mpr (by
    intro e he; simpa using (h e he).ne')
  simp [hl]

theorem pad_filter {l : List ℕ} (h : l.Pairwise (· ≤ ·)) :
    pad l.length (l.filter (· != 0)) = l := by
  induction l with
  | nil => simp [pad]
  | cons a l ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
    by_cases hz : a = 0
    · subst a
      have hlen := List.length_filter_le (fun x : ℕ => x != 0) l
      have heq : (l.length + 1 - (l.filter (· != 0)).length) =
          (l.length - (l.filter (· != 0)).length) + 1 := by omega
      simpa [pad, heq, List.replicate_succ, ih ht] using
        congrArg (List.cons 0) (ih ht)
    · have hp : ∀ e ∈ a :: l, (e != 0) = true := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · simp [hz]
        · have hae := ha e he
          have he0 : e ≠ 0 := by omega
          simp [he0]
      rw [List.filter_eq_self.mpr hp]
      simp [pad]

@[simp] theorem split_apply (d : List ℕ) (p : ℕ) :
    split d p = ((d.map fun n => n.factorization p).filter (· != 0) : Multiset ℕ) := by
  induction d with
  | nil => simp [split]
  | cons a d ih =>
    simp only [split, List.foldr_cons, Finsupp.add_apply, Finsupp.mapRange_apply,
      List.map_cons, List.filter_cons]
    change (if a.factorization p = 0 then 0 else {a.factorization p}) + split d p = _
    rw [ih]
    by_cases h : a.factorization p = 0 <;> simp [h]

theorem split_normalized : Specs.SplitNormalized := by
  intro d _ p e he
  rw [split_apply] at he
  simp only [Multiset.mem_coe, List.mem_filter, List.mem_map, bne_iff_ne] at he
  obtain ⟨⟨n, hn, rfl⟩, he⟩ := he
  exact ⟨Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr he), Nat.pos_of_ne_zero he⟩

theorem valuation_sorted {d : List ℕ} (hd : IsInvariant d) (p : ℕ) :
    (d.map fun n => n.factorization p).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map]
  exact hd.2.imp_of_mem (fun ha hb hab =>
    (Nat.factorization_le_iff_dvd (by have := hd.1 _ ha; omega)
      (by have := hd.1 _ hb; omega)).mpr hab p)

theorem row_split {d : List ℕ} (hd : IsInvariant d) (p : ℕ) :
    row (split d) p = (d.map fun n => n.factorization p).filter (· != 0) := by
  unfold row
  rw [split_apply]
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ ((valuation_sorted hd p).filter _)

theorem recover_rows : Specs.RecoverRows := by
  intro d hd p
  rw [row_split hd p]
  have h := pad_filter (valuation_sorted hd p)
  simpa using h

@[simp] theorem column_apply (E : ElementaryData) (i p : ℕ) :
    column E i p = exponent E p i := rfl

theorem prime_of_support {E : ElementaryData} (hE : IsElementary E) {p : ℕ}
    (hp : p ∈ E.support) : Nat.Prime p := by
  have hne : E p ≠ 0 := Finsupp.mem_support_iff.mp hp
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero hne
  exact (hE p e he).1

theorem column_support_subset (E : ElementaryData) (i : ℕ) :
    (column E i).support ⊆ E.support := Finsupp.support_onFinset_subset

theorem column_prime {E : ElementaryData} (hE : IsElementary E) (i : ℕ) :
    ∀ p ∈ (column E i).support, Nat.Prime p :=
  fun _ hp => prime_of_support hE (column_support_subset E i hp)

theorem column_pos {E : ElementaryData} (hE : IsElementary E) (i : ℕ) :
    0 < (column E i).prod (· ^ ·) := by
  apply Nat.prod_pow_pos_of_zero_notMem_support
  intro h
  exact Nat.not_prime_zero (column_prime hE i 0 h)

theorem column_factorization {E : ElementaryData} (hE : IsElementary E) (i : ℕ) :
    ((column E i).prod (· ^ ·)).factorization = column E i :=
  Nat.factorization_prod_pow_eq_self (column_prime hE i)

@[simp] theorem recombine_length (E : ElementaryData) :
    (recombine E).length = width E := by simp [recombine]

theorem recombine_getD (E : ElementaryData) {i : ℕ} (hi : i < width E) :
    (recombine E).getD i 1 = (column E i).prod (· ^ ·) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [recombine]

theorem column_valuations : Specs.ColumnValuations := by
  intro E hE i hi p
  rw [recombine_getD E hi, column_factorization hE, column_apply]

theorem map_range_getD (l : List ℕ) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem l 0 hi'

theorem recombine_valuation_row {E : ElementaryData} (hE : IsElementary E) (p : ℕ) :
    (recombine E).map (fun n => n.factorization p) = pad (width E) (row E p) := by
  have hlen := pad_length (row_length_le_width E p)
  apply List.ext_getElem (by simpa using hlen.symm)
  intro i hi hj
  have hiw : i < width E := by simpa using hi
  rw [List.getElem_map]
  have hi' : i < (recombine E).length := by simpa using hi
  rw [← List.getD_eq_getElem _ 1 hi', column_valuations E hE i hiw p]
  exact List.getD_eq_getElem _ _ hj

theorem split_recombine : Specs.SplitRecombine := by
  intro E hE
  ext p
  rw [split_apply, recombine_valuation_row hE p, filter_pad (row_positive hE p), row_multiset]

theorem exponent_mono (E : ElementaryData) (p : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j < width E) : exponent E p i ≤ exponent E p j := by
  have hlen := pad_length (row_length_le_width E p)
  unfold exponent
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact (pad_sorted (r := width E) (row_sorted E p)).rel_get_of_le hij

theorem recombine_chain {E : ElementaryData} (hE : IsElementary E) :
    (recombine E).Pairwise (· ∣ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hiw : i < width E := by simpa using hi
  have hjw : j < width E := by simpa using hj
  rw [← List.getD_eq_getElem _ 1 hi, ← List.getD_eq_getElem _ 1 hj,
    recombine_getD E hiw, recombine_getD E hjw]
  apply (Nat.factorization_le_iff_dvd (column_pos hE i).ne' (column_pos hE j).ne').mp
  rw [column_factorization hE, column_factorization hE]
  intro p
  exact exponent_mono E p hij.le hjw

theorem exists_full_row (E : ElementaryData) (hw : 0 < width E) :
    ∃ p ∈ E.support, (row E p).length = width E := by
  have hs : E.support.Nonempty := by
    by_contra h
    have hz : E.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [width, hz] at hw
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup E.support hs (fun p => (E p).card)
  exact ⟨p, hp, by simpa [width] using heq.symm⟩

theorem recombine_nontrivial {E : ElementaryData} (hE : IsElementary E)
    {i : ℕ} (hi : i < width E) : 2 ≤ (column E i).prod (· ^ ·) := by
  obtain ⟨p, hp, hlen⟩ := exists_full_row E (by omega)
  have hip : i < (row E p).length := by omega
  have hpos : 0 < exponent E p i := by
    unfold exponent pad
    rw [hlen, Nat.sub_self, List.replicate_zero, List.nil_append,
      List.getD_eq_getElem _ _ hip]
    exact row_positive hE p _ (List.getElem_mem hip)
  have hne : (column E i).prod (· ^ ·) ≠ 1 := by
    intro heq
    have hval := congrArg (fun n : ℕ => n.factorization p) heq
    rw [column_factorization hE i] at hval
    simp only [column_apply, Nat.factorization_one, Finsupp.zero_apply] at hval
    omega
  have := column_pos hE i
  omega

theorem recombine_normalized : Specs.RecombineNormalized := by
  intro E hE
  refine ⟨?_, recombine_chain hE⟩
  intro n hn
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
  exact recombine_nontrivial hE (List.mem_range.mp hi)

theorem split_width_le (d : List ℕ) : width (split d) ≤ d.length := by
  apply Finset.sup_le
  intro p _
  rw [split_apply, Multiset.coe_card]
  exact (List.length_filter_le _ _).trans_eq (List.length_map _)

theorem split_width {d : List ℕ} (hd : IsInvariant d) : width (split d) = d.length := by
  apply le_antisymm (split_width_le d)
  cases d with
  | nil => simp
  | cons a d =>
    have ha : 2 ≤ a := hd.1 a List.mem_cons_self
    obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
    have hpos : ∀ n ∈ a :: d, n.factorization p ≠ 0 := by
      intro n hn
      have hn0 : n ≠ 0 := by have := hd.1 n hn; omega
      have hpn : p ∣ n := by
        rcases List.mem_cons.mp hn with rfl | hn
        · exact hpa
        · exact hpa.trans ((List.pairwise_cons.mp hd.2).1 n hn)
      exact Finsupp.mem_support_iff.mp (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
    have hfilter : ((a :: d).map fun n => n.factorization p).filter (· != 0) =
        (a :: d).map (fun n => n.factorization p) := by
      apply List.filter_eq_self.mpr
      intro e he
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
      simp [hpos n hn]
    have hlen : (split (a :: d) p).card = (a :: d).length := by
      rw [split_apply, hfilter, Multiset.coe_card, List.length_map]
    have hmem : p ∈ (split (a :: d)).support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      rw [hz] at hlen
      simp at hlen
    exact hlen ▸ Finset.le_sup (f := fun p => (split (a :: d) p).card) hmem

theorem recombine_split : Specs.RecombineSplit := by
  intro d hd
  have hE := split_normalized d hd
  apply List.ext_getElem (by simp [split_width hd])
  intro i hi hj
  have hiw : i < width (split d) := by simpa using hi
  rw [← List.getD_eq_getElem _ 1 (by simpa using hi), recombine_getD _ hiw]
  have hd0 : d[i] ≠ 0 := by
    have hn := hd.1 (d[i]) (List.getElem_mem hj)
    omega
  apply Nat.factorization_inj (column_pos hE i).ne' hd0
  rw [column_factorization hE i]
  ext p
  change (pad (width (split d)) (row (split d) p)).getD i 0 = (d[i]).factorization p
  rw [split_width hd, recover_rows d hd p, List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem boundaries : Specs.Boundaries := by
  constructor
  · rfl
  · simp [recombine, width]

theorem column_crt : Specs.ColumnCRT := by
  classical
  intro E hE i
  have hc : Pairwise (fun p q : E.support =>
      Nat.Coprime (p.val ^ exponent E p.val i) (q.val ^ exponent E q.val i)) := by
    intro p q hpq
    exact Nat.coprime_pow_primes _ _ (prime_of_support hE p.property)
      (prime_of_support hE q.property) (fun h => hpq (Subtype.ext h))
  have hprod : (column E i).prod (· ^ ·) =
      ∏ p : E.support, p.val ^ exponent E p.val i := by
    rw [Finsupp.prod_of_support_subset (column E i) (column_support_subset E i)
      (· ^ ·) (by intros; simp)]
    simp only [column_apply]
    exact (Finset.prod_coe_sort E.support (fun p => p ^ exponent E p i)).symm
  rw [hprod]
  exact ⟨(ZMod.prodEquivPi _ hc).toAddEquiv⟩

/-- Changing the finite length by equality does not change a dependent product. -/
noncomputable def finPiCongr (A : ℕ → Type*) [∀ i, Add (A i)] {m n : ℕ} (h : m = n) :
    ((i : Fin m) → A i.val) ≃+ ((i : Fin n) → A i.val) := by
  subst n
  exact AddEquiv.refl _

/-- A leading zero exponent contributes only the trivial group. -/
noncomputable def zeroConsRowEquiv (p : ℕ) (l : List ℕ) :
    ((i : Fin (0 :: l).length) → ZMod (p ^ (0 :: l).getD i 0)) ≃+
    ((i : Fin l.length) → ZMod (p ^ l.getD i 0)) where
  toFun f j := f j.succ
  invFun f := Fin.cases 0 f
  left_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hs : Subsingleton (ZMod (p ^ (0 :: l).getD (↑(0 : Fin (0 :: l).length)) 0)) := by
        simpa using (inferInstance : Subsingleton (ZMod 1))
      exact hs.elim _ _
    · rfl
  right_inv f := rfl
  map_add' _ _ := rfl

noncomputable def zerosRowEquiv (p k : ℕ) (l : List ℕ) :
    ((i : Fin (List.replicate k 0 ++ l).length) →
      ZMod (p ^ (List.replicate k 0 ++ l).getD i 0)) ≃+
    ((i : Fin l.length) → ZMod (p ^ l.getD i 0)) := by
  induction k with
  | zero => exact AddEquiv.refl _
  | succ k ih =>
    simpa only [List.replicate_succ, List.cons_append] using
      (zeroConsRowEquiv p (List.replicate k 0 ++ l)).trans ih

noncomputable def paddedRowEquiv (p r : ℕ) (l : List ℕ) (h : l.length ≤ r) :
    ((i : Fin r) → ZMod (p ^ (pad r l).getD i 0)) ≃+
    ((i : Fin l.length) → ZMod (p ^ l.getD i 0)) :=
  (finPiCongr (fun i => ZMod (p ^ (pad r l).getD i 0)) (pad_length h).symm).trans
    (zerosRowEquiv p (r - l.length) l)

noncomputable def swapPi {α β : Type*} (A : α → β → Type*) [∀ a b, Add (A a b)] :
    ((a : α) → (b : β) → A a b) ≃+ ((b : β) → (a : α) → A a b) where
  toFun f b a := f a b
  invFun f a b := f b a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem group_preservation : Specs.GroupPreservation := by
  classical
  intro E hE
  let ec (i : ℕ) := Classical.choice (column_crt E hE i)
  let e₁ : InvariantGroup (recombine E) ≃+
      ((i : Fin (recombine E).length) → (p : E.support) →
        ZMod (p.val ^ exponent E p.val i.val)) :=
    AddEquiv.piCongrRight (fun i =>
      (ZMod.ringEquivCongr (recombine_getD E (by simpa using i.isLt))).toAddEquiv |>.trans (ec i))
  let e₂ := finPiCongr (fun i => (p : E.support) →
    ZMod (p.val ^ exponent E p.val i)) (recombine_length E)
  exact ⟨e₁.trans e₂ |>.trans (swapPi _) |>.trans
    (AddEquiv.piCongrRight (fun p => paddedRowEquiv p.val (width E)
      (row E p.val) (row_length_le_width E p.val)))⟩

theorem split_group_preservation : Specs.SplitGroupPreservation := by
  intro d hd
  have h := group_preservation (split d) (split_normalized d hd)
  rwa [recombine_split d hd] at h

theorem normalized_data_equivalence : Specs.NormalizedDataEquivalence := by
  refine ⟨{
    toFun := fun d => ⟨split d.val, split_normalized d.val d.property⟩
    invFun := fun E => ⟨recombine E.val, recombine_normalized E.val E.property⟩
    left_inv := fun d => Subtype.ext (recombine_split d.val d.property)
    right_inv := fun E => Subtype.ext (split_recombine E.val E.property)
  }, (fun _ => rfl), (fun _ => rfl)⟩

end D07.Ch07.ClassificationDataConversion
