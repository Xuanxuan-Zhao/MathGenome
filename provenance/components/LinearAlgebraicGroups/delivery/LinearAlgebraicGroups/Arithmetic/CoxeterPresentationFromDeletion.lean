import Specs.LinearAlgebraicGroups.Arithmetic.CoxeterPresentationFromDeletion
import Mathlib.Tactic.Group

namespace LinearAlgebraicGroups

open Specs.CoxeterPresentationFromDeletion (wordValue DeletionCondition PresentationFromDeletion)
open CoxeterSystem (alternatingWord)

namespace CoxeterPresentationProof

variable {S W V : Type*} [Group W] [Group V] {s : S → W} {t : S → V}

@[simp] private theorem wordValue_nil : wordValue s [] = 1 := rfl

@[simp] private theorem wordValue_cons (i : S) (l : List S) :
    wordValue s (i :: l) = s i * wordValue s l := rfl

@[simp] private theorem wordValue_append (l k : List S) :
    wordValue s (l ++ k) = wordValue s l * wordValue s k := by
  simp [wordValue]

@[simp] private theorem wordValue_concat (l : List S) (i : S) :
    wordValue s (l.concat i) = wordValue s l * s i := by
  simp [List.concat_eq_append]

private theorem wordValue_append_concat (p q : List S) (i : S) :
    wordValue s (p ++ q.concat i) = wordValue s (p ++ q) * s i := by
  simp only [wordValue_append, wordValue_concat, mul_assoc]

private theorem generator_inv (hs : ∀ i, s i * s i = 1) (i : S) :
    (s i)⁻¹ = s i :=
  (eq_inv_of_mul_eq_one_right (hs i)).symm

private theorem wordValue_reverse (hs : ∀ i, s i * s i = 1) (l : List S) :
    wordValue s l.reverse = (wordValue s l)⁻¹ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp [List.reverse_cons, ih, mul_inv_rev, generator_inv hs]

/-- Words in the given subalphabet, evaluated as a subgroup. -/
private def wordSubgroup (hs : ∀ i, s i * s i = 1) (A : Set S) : Subgroup W where
  carrier := {w | ∃ l : List S, (∀ i ∈ l, i ∈ A) ∧ wordValue s l = w}
  one_mem' := ⟨[], by simp, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨l, hl, rfl⟩ ⟨k, hk, rfl⟩
    exact ⟨l ++ k, fun i hi => (List.mem_append.mp hi).elim (hl i) (hk i), by simp⟩
  inv_mem' := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨l.reverse, fun i hi => hl i (List.mem_reverse.mp hi), wordValue_reverse hs l⟩

private theorem generator_mem_wordSubgroup (hs : ∀ i, s i * s i = 1) {A : Set S}
    {i : S} (hi : i ∈ A) : s i ∈ wordSubgroup hs A :=
  ⟨[i], by simpa, by simp⟩

private theorem wordValue_surjective (hs : ∀ i, s i * s i = 1)
    (hgen : Subgroup.closure (Set.range s) = ⊤) : Function.Surjective (wordValue s) := by
  intro w
  have h : Subgroup.closure (Set.range s) ≤ wordSubgroup hs Set.univ :=
    (Subgroup.closure_le _).mpr (by
      rintro _ ⟨i, rfl⟩
      exact generator_mem_wordSubgroup hs (Set.mem_univ i))
  rw [hgen] at h
  obtain ⟨l, _, hl⟩ := h (Subgroup.mem_top w)
  exact ⟨l, hl⟩

private def Shortest (s : S → W) (l : List S) : Prop :=
  ∀ k : List S, wordValue s k = wordValue s l → l.length ≤ k.length

private theorem Shortest.transfer {l k : List S} (hl : Shortest s l)
    (he : wordValue s k = wordValue s l) (hn : k.length = l.length) : Shortest s k :=
  fun x hx => hn.symm ▸ hl x (hx.trans he)

private theorem Shortest.append_left {l k : List S} (h : Shortest s (l ++ k)) :
    Shortest s l := by
  intro x hx
  have hle := h (x ++ k) (by simp [hx])
  simpa using hle

private theorem Shortest.append_right {l k : List S} (h : Shortest s (l ++ k)) :
    Shortest s k := by
  intro x hx
  have hle := h (l ++ x) (by simp [hx])
  simpa using hle

private theorem minWord {P : List S → Prop} (h : ∃ l, P l) :
    ∃ l, P l ∧ ∀ k, P k → l.length ≤ k.length := by
  classical
  have hex : ∃ n : ℕ, ∃ l, l.length = n ∧ P l := by
    obtain ⟨l, hl⟩ := h
    exact ⟨l.length, l, rfl, hl⟩
  obtain ⟨l, hl, hp⟩ := Nat.find_spec hex
  exact ⟨l, hp, fun k hk => hl.trans_le (Nat.find_min' hex ⟨k, rfl, hk⟩)⟩

private theorem deletion_sublist (hd : DeletionCondition s) {l : List S}
    (h : ¬Shortest s l) :
    ∃ k : List S, List.Sublist k l ∧ wordValue s k = wordValue s l ∧ k.length + 2 = l.length := by
  classical
  have hshort : ∃ k : List S, wordValue s k = wordValue s l ∧ k.length < l.length := by
    obtain ⟨k, hk⟩ := not_forall.mp h
    exact ⟨k, (not_imp.mp hk).1, Nat.lt_of_not_ge (not_imp.mp hk).2⟩
  obtain ⟨p, m, q, i, j, rfl, he⟩ := hd l hshort
  refine ⟨p ++ m ++ q, ?_, he, by simp; omega⟩
  rw [List.append_assoc]
  exact (List.Sublist.refl p).append
    (((List.Sublist.refl m).append ((List.Sublist.refl q).cons j)).cons i)

/-- The product of a shortest coset representative and a shortest word in
a subalphabet is shortest. Deleting from the prefix would shorten the
coset representative. Deleting only from the suffix would shorten that word. -/
private theorem shortest_coset_append (hs : ∀ i, s i * s i = 1)
    (hd : DeletionCondition s) {A : Set S} {p l : List S} {w : W}
    (hp : (wordValue s p)⁻¹ * w ∈ wordSubgroup hs A)
    (hmin : ∀ q : List S, (wordValue s q)⁻¹ * w ∈ wordSubgroup hs A → p.length ≤ q.length)
    (hl : ∀ i ∈ l, i ∈ A)
    (hlmin : ∀ k : List S, (∀ i ∈ k, i ∈ A) →
      wordValue s k = wordValue s l → l.length ≤ k.length) :
    Shortest s (p ++ l) := by
  classical
  by_contra h
  obtain ⟨k, hk, he, hlen⟩ := deletion_sublist hd h
  obtain ⟨q, m, rfl, hq, hm⟩ := List.sublist_append_iff.mp hk
  have hma : ∀ i ∈ m, i ∈ A := fun i hi => hl i (hm.mem hi)
  have hlmem : wordValue s l ∈ wordSubgroup hs A := ⟨l, hl, rfl⟩
  have hmmem : wordValue s m ∈ wordSubgroup hs A := ⟨m, hma, rfl⟩
  have hqp : (wordValue s q)⁻¹ * w ∈ wordSubgroup hs A := by
    simp only [wordValue_append] at he
    have he' : (wordValue s q)⁻¹ * w =
        wordValue s m * (wordValue s l)⁻¹ * ((wordValue s p)⁻¹ * w) := by
      calc
        _ = (wordValue s q)⁻¹ * (wordValue s p * wordValue s l) *
            (wordValue s l)⁻¹ * ((wordValue s p)⁻¹ * w) := by group
        _ = _ := by rw [← he]; group
    rw [he']
    exact (wordSubgroup hs A).mul_mem
      ((wordSubgroup hs A).mul_mem hmmem ((wordSubgroup hs A).inv_mem hlmem)) hp
  have hqe : q = p := hq.eq_of_length_le (hmin q hqp)
  subst q
  have hml := hlmin m hma (mul_left_cancel (by simpa only [wordValue_append] using he))
  simp only [List.length_append] at hlen
  omega

private theorem cancel_repeat (hs : ∀ i, s i * s i = 1) (l : List S) (i : S) :
    wordValue s ((l.concat i).concat i) = wordValue s l := by
  simp [hs]

private theorem alternating_concat (hs : ∀ i, s i * s i = 1) (i j : S)
    {l : List S} (hl : Shortest s (l.concat j))
    (ha : l = alternatingWord i j l.length ∨ l = alternatingWord j i l.length) :
    l.concat j = alternatingWord i j (l.concat j).length := by
  rw [List.length_concat, CoxeterSystem.alternatingWord_succ]
  rcases ha with he | he
  · cases hn : l.length with
    | zero =>
      have hnil := List.length_eq_zero_iff.mp hn
      subst l
      rfl
    | succ n =>
      rw [hn, CoxeterSystem.alternatingWord_succ] at he
      have hc : wordValue s (l.concat j) = wordValue s (alternatingWord j i n) := by
        rw [he, cancel_repeat hs]
      have hab := hl (alternatingWord j i n) hc.symm
      simp only [List.length_concat, CoxeterSystem.length_alternatingWord, hn] at hab
      omega
  · rw [← he]

private theorem alternating_of_shortest {i j : S} {l : List S}
    (hs : ∀ i, s i * s i = 1) (hl : Shortest s l)
    (ha : ∀ a ∈ l, a = i ∨ a = j) :
    l = alternatingWord i j l.length ∨ l = alternatingWord j i l.length := by
  induction l using List.reverseRecOn with
  | nil => exact Or.inl rfl
  | append_singleton l a ih =>
    have hl' : Shortest s l := hl.append_left
    have ha' : ∀ b ∈ l, b = i ∨ b = j := fun b hb => ha b (List.mem_append_left _ hb)
    have hlast : a = i ∨ a = j := ha a (List.mem_append_right _ (by simp))
    have hl'' : Shortest s (l.concat a) := by simpa [List.concat_eq_append] using hl
    rcases hlast with he | he
    · subst a
      exact Or.inr (by simpa [List.concat_eq_append] using
        alternating_concat hs j i hl'' (ih hl' ha').symm)
    · subst a
      exact Or.inl (by simpa [List.concat_eq_append] using
        alternating_concat hs i j hl'' (ih hl' ha'))

private theorem alternating_difference (hs : ∀ i, s i * s i = 1) (i j : S) (n : ℕ) :
    (wordValue s (alternatingWord i j n))⁻¹ * wordValue s (alternatingWord j i n) =
      (s j * s i) ^ n := by
  induction n generalizing i j with
  | zero => simp [alternatingWord]
  | succ n ih =>
    simp only [CoxeterSystem.alternatingWord_succ, wordValue_concat, mul_inv_rev,
      generator_inv hs, mul_assoc]
    rw [← mul_assoc ((wordValue s (alternatingWord j i n))⁻¹), ih j i]
    rw [← mul_assoc, ← mul_pow_mul (s j) (s i), mul_assoc, ← pow_succ]

/-- At a chosen shortest coset representative, a reduced expression ending
in a letter of the pair can be written with an alternating suffix ending
in that letter. -/
private theorem shortest_coset_ending (hs : ∀ i, s i * s i = 1)
    (hd : DeletionCondition s) {A : Set S} {w : W} {p l : List S} {i j : S}
    (hp : (wordValue s p)⁻¹ * w ∈ wordSubgroup hs A)
    (hmin : ∀ q : List S, (wordValue s q)⁻¹ * w ∈ wordSubgroup hs A → p.length ≤ q.length)
    (hj : j ∈ A) (hA : ∀ a ∈ A, a = i ∨ a = j)
    (hl : Shortest s (l.concat j)) (he : wordValue s (l.concat j) = w) :
    ∃ q, Shortest s (p ++ q) ∧ wordValue s (p ++ q) = wordValue s l ∧
      q.concat j = alternatingWord i j (q.length + 1) := by
  have hex : ∃ q : List S, (∀ a ∈ q, a ∈ A) ∧
      wordValue s q = (wordValue s p)⁻¹ * w * s j :=
    (wordSubgroup hs A).mul_mem hp (generator_mem_wordSubgroup hs hj)
  obtain ⟨q, ⟨hq, hqv⟩, hqm⟩ := minWord hex
  have hshort : Shortest s (p ++ q) :=
    shortest_coset_append hs hd hp hmin hq (fun k hk hkv => hqm k ⟨hk, hkv.trans hqv⟩)
  have hval : wordValue s (p ++ q) = wordValue s l := by
    rw [wordValue_append, hqv]
    calc
      _ = w * s j := by group
      _ = wordValue s l := by rw [← he, wordValue_concat, mul_assoc, hs, mul_one]
  have hls : Shortest s l :=
    Shortest.append_left (k := [j]) (by simpa [List.concat_eq_append] using hl)
  have hlen : (p ++ q).length = l.length :=
    le_antisymm (hshort l hval.symm) (hls _ hval)
  have hfull : Shortest s (p ++ q.concat j) := hl.transfer
    (by rw [wordValue_append_concat, hval, wordValue_concat])
    (by simpa only [List.length_append, List.length_concat, ← Nat.add_assoc] using
      (congrArg (· + 1) hlen))
  have hsuffix : Shortest s (q.concat j) := hfull.append_right
  have hqshort : Shortest s q := hshort.append_right
  refine ⟨q, hshort, hval, ?_⟩
  simpa only [List.length_concat] using
    alternating_concat hs i j hsuffix (alternating_of_shortest hs hqshort (fun a ha => hA a (hq a ha)))

/-- Reduced words with the same value lift to the same value in any group
satisfying the involution and rank-two relations. -/
private theorem shortest_word_property (hs : ∀ i, s i * s i = 1)
    (hgen : Function.Surjective (wordValue s)) (hd : DeletionCondition s)
    (ht : ∀ i, t i * t i = 1)
    (htpow : ∀ i j, (t i * t j) ^ orderOf (s i * s j) = 1)
    {l k : List S} (hl : Shortest s l) (hk : Shortest s k)
    (he : wordValue s l = wordValue s k) : wordValue t l = wordValue t k := by
  induction hlen : l.length using Nat.strong_induction_on generalizing l k with
  | h n ih =>
    have hlen' : k.length = n :=
      (le_antisymm (hk l he) (hl k he.symm)).trans hlen
    cases l using List.reverseRecOn with
    | nil =>
      have : k = [] := List.length_eq_zero_iff.mp (hlen'.trans hlen.symm)
      subst k
      rfl
    | append_singleton l i =>
      cases k using List.reverseRecOn with
      | nil => simp at hlen hlen'; omega
      | append_singleton k j =>
        have hls : Shortest s l := hl.append_left
        have hks : Shortest s k := hk.append_left
        have hli : l.length < n := by simp at hlen; omega
        have hki : k.length < n := by simp at hlen'; omega
        by_cases hij : i = j
        · subst j
          simp only [wordValue_append, wordValue_cons, wordValue_nil, mul_one] at he ⊢
          rw [ih l.length hli hls hks (mul_right_cancel he) rfl]
        · let w := wordValue s (l ++ [i])
          have hlw : wordValue s (l.concat i) = w := by simp [w, List.concat_eq_append]
          have hkw : wordValue s (k.concat j) = w := by
            simpa only [List.concat_eq_append] using he.symm
          let A : Set S := {i, j}
          have hex : ∃ p : List S, (wordValue s p)⁻¹ * w ∈ wordSubgroup hs A := by
            obtain ⟨p, hp⟩ := hgen w
            exact ⟨p, by simp [hp]⟩
          obtain ⟨p, hp, hmin⟩ := minWord hex
          obtain ⟨q, hqs, hqv, hqa⟩ := shortest_coset_ending hs hd hp hmin
            (show i ∈ A by simp [A])
            (show ∀ a ∈ A, a = j ∨ a = i by simp [A, or_comm])
            (show Shortest s (l.concat i) by simpa [List.concat_eq_append] using hl) hlw
          obtain ⟨r, hrs, hrv, hra⟩ := shortest_coset_ending hs hd hp hmin
            (show j ∈ A by simp [A])
            (show ∀ a ∈ A, a = i ∨ a = j by simp [A])
            (show Shortest s (k.concat j) by simpa [List.concat_eq_append] using hk) hkw
          have hqval : wordValue s (p ++ q.concat i) = w := by
            rwa [wordValue_append_concat, hqv, ← wordValue_concat]
          have hrval : wordValue s (p ++ r.concat j) = w := by
            rwa [wordValue_append_concat, hrv, ← wordValue_concat]
          have hql : (p ++ q).length = l.length :=
            le_antisymm (hqs l hqv.symm) (hls _ hqv)
          have hrl : (p ++ r).length = k.length :=
            le_antisymm (hrs k hrv.symm) (hks _ hrv)
          have hqr : q.length = r.length := by
            simp only [List.length_append, List.length_singleton] at hql hrl hlen hlen'
            omega
          rw [hqr] at hqa
          have hsame : wordValue s (alternatingWord j i (r.length + 1)) =
              wordValue s (alternatingWord i j (r.length + 1)) := by
            rw [← hqa, ← hra]
            exact mul_left_cancel (by simpa only [wordValue_append] using hqval.trans hrval.symm)
          -- Their common length is a multiple of the rank-two relation exponent.
          have hdvd : orderOf (s i * s j) ∣ r.length + 1 := by
            rw [orderOf_dvd_iff_pow_eq_one, ← alternating_difference hs j i, hsame, inv_mul_cancel]
          have hbraid : wordValue t (alternatingWord j i (r.length + 1)) =
              wordValue t (alternatingWord i j (r.length + 1)) := by
            apply inv_mul_eq_one.mp
            rw [alternating_difference ht j i]
            obtain ⟨m, hm⟩ := hdvd
            rw [hm, pow_mul, htpow, one_pow]
          calc
            wordValue t (l ++ [i]) = wordValue t (p ++ q.concat i) := by
              rw [wordValue_append_concat, ← ih l.length hli hls hqs hqv.symm rfl]
              simp
            _ = wordValue t (p ++ r.concat j) := by
              rw [wordValue_append, wordValue_append, hqa, hra, hbraid]
            _ = wordValue t (k ++ [j]) := by
              rw [wordValue_append_concat, ← ih k.length hki hks hrs hrv.symm rfl]
              simp

/-- Deletion and the reduced-word comparison give a shortest word with the
same value both in the original group and in the group of the relations. -/
private theorem shortest_representative (hs : ∀ i, s i * s i = 1)
    (hgen : Function.Surjective (wordValue s)) (hd : DeletionCondition s)
    (ht : ∀ i, t i * t i = 1)
    (htpow : ∀ i j, (t i * t j) ^ orderOf (s i * s j) = 1) (l : List S) :
    ∃ k, Shortest s k ∧ wordValue s k = wordValue s l ∧ wordValue t k = wordValue t l := by
  classical
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], fun k _ => Nat.zero_le k.length, rfl, rfl⟩
  | append_singleton l i ih =>
    obtain ⟨r, hr, hrv, hrt⟩ := ih
    have hsval : wordValue s (r.concat i) = wordValue s (l ++ [i]) := by simp [hrv]
    have htval : wordValue t (r.concat i) = wordValue t (l ++ [i]) := by simp [hrt]
    by_cases ha : Shortest s (r.concat i)
    · exact ⟨r.concat i, ha, hsval, htval⟩
    · obtain ⟨k, _, he, hlen⟩ := deletion_sublist hd ha
      have hcancel : wordValue s (k.concat i) = wordValue s r := by
        simp [he, mul_assoc, hs]
      have hk : Shortest s (k.concat i) :=
        hr.transfer hcancel (by simp only [List.length_concat] at hlen ⊢; omega)
      have hkt := shortest_word_property hs hgen hd ht htpow hk hr hcancel
      have hre : wordValue t k = wordValue t (r.concat i) := by
        rw [wordValue_concat] at hkt ⊢
        rw [← hkt, mul_assoc, ht, mul_one]
      refine ⟨k, Shortest.append_left (k := [i]) ?_, he.trans hsval, hre.trans htval⟩
      simpa only [List.concat_eq_append] using hk

private noncomputable def orderMatrix (hinj : Function.Injective s)
    (hs : ∀ i, s i * s i = 1) : CoxeterMatrix S where
  M := Matrix.of fun i j => orderOf (s i * s j)
  isSymm := Matrix.IsSymm.ext (fun i j => by
    change orderOf (s j * s i) = orderOf (s i * s j)
    rw [← orderOf_inv (s i * s j), mul_inv_rev, generator_inv hs, generator_inv hs])
  diagonal i := by change orderOf (s i * s i) = 1; rw [hs, orderOf_one]
  off_diagonal i j hij h := by
    have hmul : s i * s j = 1 := orderOf_eq_one_iff.mp h
    exact hij (hinj ((eq_inv_of_mul_eq_one_right hmul).trans (generator_inv hs i)).symm)

private theorem hom_wordValue {G H : Type*} [Group G] [Group H]
    (f : G →* H) (g : S → G) (l : List S) :
    f (wordValue g l) = wordValue (f ∘ g) l := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- The Coxeter presentation of a group generated by distinct nonidentity
involutions and satisfying word deletion. -/
theorem _root_.LinearAlgebraicGroups.coxeterPresentationFromDeletion :
    PresentationFromDeletion.{u,v} := by
  intro S W _ s hinj _hne hs hgen hd
  let M := orderMatrix hinj hs
  have hM (i j : S) : M i j = orderOf (s i * s j) := rfl
  have hrel : M.IsLiftable s := fun i j => by rw [hM, pow_orderOf_eq_one]
  let cs₀ := M.toCoxeterSystem
  let f : M.Group →* W := cs₀.lift ⟨s, hrel⟩
  have hf (i : S) : f (cs₀.simple i) = s i := cs₀.lift_apply_simple hrel i
  have hmap (l : List S) : f (wordValue cs₀.simple l) = wordValue s l :=
    (hom_wordValue f cs₀.simple l).trans (congrArg (wordValue · l) (funext hf))
  have hwords := wordValue_surjective hs hgen
  have hsurj : Function.Surjective f := by
    intro w
    obtain ⟨l, hl⟩ := hwords w
    exact ⟨wordValue cs₀.simple l, (hmap l).trans hl⟩
  have hinjf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro x hx
    obtain ⟨l, rfl⟩ := cs₀.wordProd_surjective x
    change f (wordValue cs₀.simple l) = 1 at hx
    rw [hmap] at hx
    have hpow (i j : S) : (cs₀.simple i * cs₀.simple j) ^ orderOf (s i * s j) = 1 := by
      rw [← hM, cs₀.simple_mul_simple_pow]
    obtain ⟨k, hk, hkv, hkt⟩ :=
      shortest_representative hs hwords hd cs₀.simple_mul_simple_self hpow l
    have hnil : k = [] :=
      List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hk [] (hkv.trans hx).symm))
    change wordValue cs₀.simple l = 1
    rw [← hkt, hnil, wordValue_nil]
  let e := MulEquiv.ofBijective f ⟨hinjf, hsurj⟩
  refine ⟨M, hM, cs₀.map e, funext fun i => ?_⟩
  rw [CoxeterSystem.map_simple]
  exact hf i

end CoxeterPresentationProof

end LinearAlgebraicGroups
