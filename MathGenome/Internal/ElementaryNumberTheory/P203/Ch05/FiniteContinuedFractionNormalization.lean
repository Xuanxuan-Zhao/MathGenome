import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ContinuedFractionAlgorithm
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.FiniteContinuedFractionNormalization
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

namespace P203
open P203Specs

private theorem terminates_iff_absent (x : ℝ) :
    AlgorithmTerminates x ↔ ∃ n, P203Specs.completeQuotient x (n + 1) = none := by
  constructor
  · rintro ⟨n, α, hα, _, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    have hex : ∃ k, P203Specs.completeQuotient x (k + 1) = none := ⟨n, hn⟩
    let k := Nat.find hex
    have hk : P203Specs.completeQuotient x (k + 1) = none := Nat.find_spec hex
    have hdef : P203Specs.completeQuotient x k ≠ none := by
      intro h
      change P203Specs.completeQuotient x (Nat.find hex) = none at h
      by_cases hz : Nat.find hex = 0
      · rw [hz, (algorithm_initial x).1] at h
        contradiction
      · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hz
        apply Nat.find_min hex (show j < Nat.find hex by omega)
        simpa only [hj] using h
    obtain ⟨α, hα⟩ := Option.ne_none_iff_exists'.mp hdef
    exact ⟨k, α, hα, (algorithm_stopping x α k hα).mp hk, hk⟩

theorem termination_iff_rational : TerminationIffRational := by
  intro x
  rw [terminates_iff_absent]
  have hb : (∃ n, P203Specs.completeQuotient x (n + 1) = none) ↔
      (GenContFract.of x).Terminates := by
    exact exists_congr (fun n => (standard_termination_bridge x n).symm)
  rw [hb, GenContFract.terminates_iff_rat]
  exact exists_congr (fun q => eq_comm)

theorem irrational_nontermination : IrrationalNontermination := by
  intro x hx ht
  obtain ⟨q, hq⟩ := (termination_iff_rational x).mp ht
  exact hx ⟨q, hq⟩

private theorem tail_gt_one {a : ℤ} {t : List ℤ} (h : CanonicalTail a t) :
    1 < P203Specs.finiteContinuedFraction a t := by
  induction t generalizing a with
  | nil =>
    simp only [CanonicalTail] at h
    change 1 < (a : ℝ)
    exact_mod_cast (show (1 : ℤ) < a by omega)
  | cons b t ih =>
    obtain ⟨ha, ht⟩ := h
    have hb := ih ht
    have hi : 0 < 1 / P203Specs.finiteContinuedFraction b t := one_div_pos.mpr (by linarith)
    change 1 < (a : ℝ) + 1 / P203Specs.finiteContinuedFraction b t
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith

private theorem canonical_floor {a : ℤ} {t : List ℤ} (h : Canonical a t) :
    ⌊P203Specs.finiteContinuedFraction a t⌋ = a := by
  cases t with
  | nil => exact Int.floor_intCast a
  | cons b t =>
    have hb := tail_gt_one h
    apply Int.floor_eq_iff.mpr
    change (a : ℝ) ≤ (a : ℝ) + 1 / P203Specs.finiteContinuedFraction b t ∧
      (a : ℝ) + 1 / P203Specs.finiteContinuedFraction b t < (a : ℝ) + 1
    have hi : 0 < 1 / P203Specs.finiteContinuedFraction b t := one_div_pos.mpr (by linarith)
    have hi' : 1 / P203Specs.finiteContinuedFraction b t < 1 :=
      (div_lt_one (by linarith)).mpr hb
    constructor <;> linarith

private theorem canonicalTail_canonical {a : ℤ} {t : List ℤ}
    (h : CanonicalTail a t) : Canonical a t := by
  cases t with
  | nil => trivial
  | cons b t => exact h.2

private theorem canonical_next {a b : ℤ} {t : List ℤ}
    (h : Canonical a (b :: t)) :
    P203Specs.finiteContinuedFraction a (b :: t) ≠ (a : ℝ) ∧
      1 / (P203Specs.finiteContinuedFraction a (b :: t) - (a : ℝ)) =
        P203Specs.finiteContinuedFraction b t := by
  have hb := tail_gt_one h
  have hz : P203Specs.finiteContinuedFraction b t ≠ 0 := by linarith
  change (a : ℝ) + 1 / P203Specs.finiteContinuedFraction b t ≠ (a : ℝ) ∧
    1 / ((a : ℝ) + 1 / P203Specs.finiteContinuedFraction b t - (a : ℝ)) = _
  constructor
  · have hi := one_div_pos.mpr (show 0 < P203Specs.finiteContinuedFraction b t by linarith)
    linarith
  · field_simp
    ring

theorem canonical_uniqueness : CanonicalUniqueness := by
  intro a b s
  induction s generalizing a b with
  | nil =>
    intro t ha hb he
    have hab : a = b := by simpa only [canonical_floor ha, canonical_floor hb] using congrArg Int.floor he
    subst b
    cases t with
    | nil => exact ⟨rfl, rfl⟩
    | cons c t => exact False.elim ((canonical_next hb).1 he.symm)
  | cons c s ih =>
    intro t ha hb he
    have hab : a = b := by simpa only [canonical_floor ha, canonical_floor hb] using congrArg Int.floor he
    subst b
    cases t with
    | nil => exact False.elim ((canonical_next ha).1 he)
    | cons d t =>
      have hv : P203Specs.finiteContinuedFraction c s = P203Specs.finiteContinuedFraction d t := by
        exact (canonical_next ha).2.symm.trans
          ((congrArg (fun z : ℝ => 1 / (z - (a : ℝ))) he).trans (canonical_next hb).2)
      obtain ⟨hcd, hst⟩ := ih c d t (canonicalTail_canonical ha)
        (canonicalTail_canonical hb) hv
      exact ⟨rfl, by simp [hcd, hst]⟩

private theorem canonical_run {x : ℝ} {a : ℤ} {t : List ℤ}
    (hc : Canonical a t) {j : ℕ}
    (hq : P203Specs.completeQuotient x j = some (P203Specs.finiteContinuedFraction a t)) :
    (∀ k : ℕ, P203Specs.partialQuotient x (j + k) = (a :: t)[k]?) ∧
      P203Specs.completeQuotient x (j + t.length + 1) = none := by
  induction t generalizing a j with
  | nil =>
    have hs : P203Specs.completeQuotient x (j + 1) = none := by
      rw [algorithm_step, hq, Option.bind_some, canonical_floor hc]
      simp [P203Specs.finiteContinuedFraction]
    refine ⟨?_, by simpa using hs⟩
    intro k
    cases k with
    | zero =>
        change P203Specs.partialQuotient x j = some a
        rw [algorithm_digits, hq, Option.map_some, canonical_floor hc]
    | succ k =>
      have hn := algorithm_no_restart x (j + 1) k hs
      rw [show j + (k + 1) = j + 1 + k by omega, algorithm_digits, hn]
      simp
  | cons b t ih =>
    have hs : P203Specs.completeQuotient x (j + 1) = some (P203Specs.finiteContinuedFraction b t) := by
      rw [algorithm_step, hq, Option.bind_some, canonical_floor hc,
        ite_eq_right (canonical_next hc).1, (canonical_next hc).2]
    obtain ⟨hd, hn⟩ := ih (canonicalTail_canonical hc) hs
    refine ⟨?_, ?_⟩
    · intro k
      cases k with
      | zero =>
          change P203Specs.partialQuotient x j = some a
          rw [algorithm_digits, hq, Option.map_some, canonical_floor hc]
      | succ k => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hd k
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn

theorem canonical_algorithm_identification : CanonicalAlgorithmIdentification := by
  intro a t hc
  have h := canonical_run hc ((algorithm_initial (P203Specs.finiteContinuedFraction a t)).1)
  simpa [AlgorithmExpansion] using h

private theorem canonicalTail_of_gt_one {a : ℤ} {t : List ℤ}
    (hc : Canonical a t) (hv : 1 < P203Specs.finiteContinuedFraction a t) : CanonicalTail a t := by
  cases t with
  | nil =>
    change 2 ≤ a
    have ha : (1 : ℝ) < a := hv
    have : (1 : ℤ) < a := by exact_mod_cast ha
    omega
  | cons b t =>
    refine ⟨?_, hc⟩
    have : (1 : ℤ) ≤ ⌊P203Specs.finiteContinuedFraction a (b :: t)⌋ := Int.le_floor.mpr (by simpa only [Int.cast_one] using hv.le)
    rwa [canonical_floor hc] at this

private theorem canonical_of_absent (x : ℝ) (n : ℕ) :
    ∀ (j : ℕ) (α : ℝ), P203Specs.completeQuotient x j = some α →
      P203Specs.completeQuotient x (j + n + 1) = none →
      ∃ (a : ℤ) (t : List ℤ), Canonical a t ∧ P203Specs.finiteContinuedFraction a t = α := by
  induction n with
  | zero =>
    intro j α hq hn
    have hi := (algorithm_stopping x α j hq).mp (by simpa using hn)
    exact ⟨⌊α⌋, [], trivial, hi.symm⟩
  | succ n ih =>
    intro j α hq hn
    cases hs : P203Specs.completeQuotient x (j + 1) with
    | none =>
      have hi := (algorithm_stopping x α j hq).mp hs
      exact ⟨⌊α⌋, [], trivial, hi.symm⟩
    | some β =>
      have hβ : 1 < β := later_completeQuotients x β (j + 1) (by omega) hs
      obtain ⟨b, t, hc, hv⟩ := ih (j + 1) β hs (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn)
      have hne : α ≠ (⌊α⌋ : ℝ) := by
        intro he
        have ha := (algorithm_stopping x α j hq).mpr he
        rw [ha] at hs
        contradiction
      have hrec : 1 / (α - (⌊α⌋ : ℝ)) = β := by
        rw [algorithm_step, hq, Option.bind_some, ite_eq_right hne] at hs
        exact Option.some.inj hs
      refine ⟨⌊α⌋, b :: t, canonicalTail_of_gt_one hc (hv.symm ▸ hβ), ?_⟩
      change (⌊α⌋ : ℝ) + 1 / P203Specs.finiteContinuedFraction b t = α
      rw [hv, ← hrec]
      simp

theorem rational_canonical_existence : RationalCanonicalExistence := by
  intro q
  have ht := (termination_iff_rational (q : ℝ)).mpr ⟨q, rfl⟩
  obtain ⟨n, hn⟩ := (terminates_iff_absent (q : ℝ)).mp ht
  obtain ⟨a, t, hc, hv⟩ := canonical_of_absent (q : ℝ) n 0 (q : ℝ)
    (algorithm_initial (q : ℝ)).1 (by simpa using hn)
  refine ⟨a, t, hc, hv, ?_⟩
  rw [← hv]
  exact canonical_algorithm_identification a t hc

private theorem terminal_merge (a b : ℤ) (t : List ℤ) :
    P203Specs.finiteContinuedFraction a (t ++ [b, 1]) =
      P203Specs.finiteContinuedFraction a (t ++ [b + 1]) := by
  induction t generalizing a with
  | nil => simp [P203Specs.finiteContinuedFraction, Int.cast_add]
  | cons c t ih =>
    simp only [List.cons_append, P203Specs.finiteContinuedFraction]
    rw [ih]

private theorem integer_merge (a : ℤ) :
    P203Specs.finiteContinuedFraction a [1] =
      P203Specs.finiteContinuedFraction (a + 1) [] := by
  simp [P203Specs.finiteContinuedFraction, Int.cast_add]

theorem final_digit_splitting : FinalDigitSplitting := by
  constructor
  · intro a b t _
    simpa using (terminal_merge a (b - 1) t).symm
  · intro a
    simpa using (integer_merge (a - 1)).symm

private theorem tail_append_last (a b : ℤ) (t : List ℤ) :
    CanonicalTail a (t ++ [b]) ↔
      1 ≤ a ∧ (∀ c ∈ t, 1 ≤ c) ∧ 2 ≤ b := by
  induction t generalizing a with
  | nil => simp [CanonicalTail]
  | cons c t ih =>
    simp only [List.cons_append, CanonicalTail, ih, List.forall_mem_cons]
    tauto

private theorem canonical_append_last (a b : ℤ) (t : List ℤ) :
    Canonical a (t ++ [b]) ↔ (∀ c ∈ t, 1 ≤ c) ∧ 2 ≤ b := by
  cases t with
  | nil => simp [Canonical, CanonicalTail]
  | cons c t =>
    simp only [List.cons_append, Canonical, tail_append_last, List.forall_mem_cons]
    tauto

theorem noncanonical_merging : NoncanonicalMerging := by
  intro a t ha hn
  cases t using List.reverseRecOn with
  | nil => exact False.elim (hn trivial)
  | append_singleton u z =>
    have hz : 1 ≤ z := ha z (by simp)
    have hu : ∀ c ∈ u, 1 ≤ c := fun c hc => ha c (by simp [hc])
    have hz1 : z = 1 := by
      have : ¬ 2 ≤ z := fun h => hn ((canonical_append_last a z u).mpr ⟨hu, h⟩)
      omega
    subst z
    cases u using List.reverseRecOn with
    | nil =>
      left
      exact ⟨rfl, trivial, integer_merge a⟩
    | append_singleton s b =>
      right
      have hb : 1 ≤ b := hu b (by simp)
      have hs : ∀ c ∈ s, 1 ≤ c := fun c hc => hu c (by simp [hc])
      refine ⟨s, b, by simp, (canonical_append_last a (b + 1) s).mpr ⟨hs, by omega⟩, ?_⟩
      simpa [List.append_assoc] using terminal_merge a b s

private theorem alternative_append_last (a b : ℤ) (t : List ℤ) :
    alternativeExpansion a (t ++ [b]) = a :: (t ++ [b - 1, 1]) := by
  induction t generalizing a with
  | nil => rfl
  | cons c t ih => simpa [alternativeExpansion] using congrArg (List.cons a) (ih c)

private theorem canonical_admissible {a : ℤ} {t : List ℤ}
    (h : Canonical a t) : Admissible a t := by
  intro b hb
  induction t generalizing a with
  | nil => simp at hb
  | cons c t ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · cases t with
      | nil => change 2 ≤ b at h; omega
      | cons d t => exact h.1
    · exact ih (canonicalTail_canonical h) hb

theorem all_finite_expansions : AllFiniteExpansions := by
  intro a t ha
  by_cases hc : Canonical a t
  · exact ⟨a, t, hc, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rcases noncanonical_merging a t ha hc with hi | ⟨s, b, ht, hn, hv⟩
    · obtain ⟨rfl, hn, hv⟩ := hi
      refine ⟨a + 1, [], hn, hv, Or.inr ?_⟩
      simp [alternativeExpansion]
    · refine ⟨a, s ++ [b + 1], hn, hv, Or.inr ?_⟩
      rw [alternative_append_last]
      simp [ht]

theorem alternative_expansion_properties : AlternativeExpansionProperties := by
  intro a t hc
  cases t using List.reverseRecOn with
  | nil =>
    refine ⟨a - 1, [1], rfl, ?_, ?_, ?_⟩
    · simp [Admissible]
    · simpa [alternativeExpansion, expansionValue] using (integer_merge (a - 1))
    · simp [alternativeExpansion]
  | append_singleton s b =>
    obtain ⟨hs, hb⟩ := (canonical_append_last a b s).mp hc
    refine ⟨a, s ++ [b - 1, 1], alternative_append_last a b s, ?_, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | rfl | rfl
      · exact hs c hc
      · omega
      · omega
    · rw [alternative_append_last]
      change P203Specs.finiteContinuedFraction a (s ++ [b - 1, 1]) = _
      simpa using terminal_merge a (b - 1) s
    · intro he
      have hl := congrArg List.length he
      rw [alternative_append_last] at hl
      simp at hl

theorem finite_normalization : FiniteNormalization := by
  intro q
  obtain ⟨a, t, ha, hq, halg⟩ := rational_canonical_existence q
  obtain ⟨_, _, _, _, halt, _⟩ := alternative_expansion_properties a t ha
  refine ⟨a, t, ha, canonical_admissible ha, hq, halg, ?_, ?_⟩
  · intro b s hb he
    exact canonical_uniqueness b a s t hb ha (he.trans hq.symm)
  · intro b s hb
    constructor
    · intro he
      obtain ⟨c, u, hc, hv, hcases⟩ := all_finite_expansions b s hb
      obtain ⟨rfl, rfl⟩ := canonical_uniqueness c a u t hc ha
        (hv.symm.trans (he.trans hq.symm))
      rcases hcases with ⟨rfl, rfl⟩ | hcases
      · exact Or.inl rfl
      · exact Or.inr hcases
    · rintro (he | he)
      · obtain ⟨rfl, rfl⟩ := List.cons.inj he
        exact hq
      · have hv := congrArg expansionValue he
        exact hv.trans (halt.trans hq)

end P203
