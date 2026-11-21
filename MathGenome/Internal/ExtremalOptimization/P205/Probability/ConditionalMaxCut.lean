import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.ConditionalMaxCut
import MathGenome.Internal.ExtremalOptimization.P205.Probability.ConditionalSelection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators Classical

namespace P205.Probability.ConditionalMaxCut
open ConditionalSelection
variable {V : Type*} [Fintype V]

lemma fair_weight (c : V → Bool) :
    (fairModel V).weight c = (1 / 2 : ℝ) ^ Fintype.card V := by
  simp [fairModel, FiniteModel.pi, fairBit]

lemma fair_weight_pos (c : V → Bool) : 0 < (fairModel V).weight c := by
  rw [fair_weight]
  positivity

@[simp] lemma mem_partialCell (S : Finset V) (c d : V → Bool) :
    d ∈ partialCell S c ↔ ∀ v ∈ S, d v = c v := by
  simp [partialCell]

lemma self_mem_partialCell (S : Finset V) (c : V → Bool) : c ∈ partialCell S c := by simp

theorem partial_positive (S : Finset V) (c : V → Bool) :
    0 < cellMass (fairModel V) (partialCell S c) := by
  rw [cellMass_sum]
  exact Finset.sum_pos' (fun d _ => le_of_lt (fair_weight_pos d))
    ⟨c, self_mem_partialCell S c, fair_weight_pos c⟩

theorem cut_count (G : SimpleGraph V) (c : V → Bool) :
    cutObjective G c = ((cutEdges G c).card : ℝ) := by
  classical
  rw [cutObjective, cutEdges, Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ a b => by_cases h : c a = c b <;> simp [edgeIndicator, h]

noncomputable def flip (d : V → Bool) (v : V) : V → Bool :=
  Function.update d v (! d v)

omit [Fintype V] in
@[simp] lemma flip_flip (d : V → Bool) (v : V) : flip (flip d v) v = d := by
  classical
  funext w
  by_cases h : w = v <;> simp [flip, h]

lemma flip_mem (S : Finset V) (c d : V → Bool) (v : V) (hv : v ∉ S)
    (hd : d ∈ partialCell S c) : flip d v ∈ partialCell S c := by
  classical
  simp only [mem_partialCell] at hd ⊢
  intro w hw
  have h : w ≠ v := by rintro rfl; exact hv hw
  simpa [flip, h] using hd w hw

/-- Flipping an unrevealed bit permutes the compatible complete colorings. -/
lemma sum_flip (S : Finset V) (c : V → Bool) (v : V) (hv : v ∉ S)
    (f : (V → Bool) → ℝ) :
    (∑ d ∈ partialCell S c, f d) = ∑ d ∈ partialCell S c, f (flip d v) := by
  classical
  apply Finset.sum_bij (fun d _ => flip d v)
  · intro d hd
    exact flip_mem S c d v hv hd
  · intro a _ b _ hab
    have := congrArg (fun d => flip d v) hab
    simpa using this
  · intro b hb
    exact ⟨flip b v, flip_mem S c b v hv hb, flip_flip b v⟩
  · intro d _
    simp

omit [Fintype V] in
lemma flip_indicator (d : V → Bool) (a b : V) (hab : a ≠ b) :
    edgeIndicator (flip d a) s(a, b) = 1 - edgeIndicator d s(a, b) := by
  classical
  simp only [edgeIndicator, Sym2.lift_mk, flip,
    Function.update_self, Function.update_of_ne hab.symm]
  cases d a <;> cases d b <;> norm_num

/-- Pairing each coloring with its flip makes an unrevealed edge contribute one half. -/
lemma unrevealed_moment (S : Finset V) (c : V → Bool) (a b : V)
    (hab : a ≠ b) (ha : a ∉ S) :
    cellMoment (fairModel V) (fun d => edgeIndicator d s(a, b)) (partialCell S c) /
      cellMass (fairModel V) (partialCell S c) = 1 / 2 := by
  classical
  have hsum := sum_flip S c a ha (fun d =>
    (fairModel V).weight d * edgeIndicator d s(a, b))
  have hrel : cellMoment (fairModel V) (fun d => edgeIndicator d s(a,b))
        (partialCell S c) = cellMass (fairModel V) (partialCell S c) -
      cellMoment (fairModel V) (fun d => edgeIndicator d s(a,b)) (partialCell S c) := by
    change (∑ d ∈ partialCell S c, _) = _ at hsum
    change (∑ d ∈ partialCell S c, (fairModel V).weight d * edgeIndicator d s(a,b)) = _
    rw [hsum]
    simp_rw [flip_indicator _ a b hab, fair_weight, mul_sub, mul_one]
    rw [Finset.sum_sub_distrib]
    simp only [cellMass_sum, cellMoment, fair_weight]
  apply (div_eq_iff (ne_of_gt (partial_positive S c))).mpr
  linarith

theorem conditional_edge (G : SimpleGraph V) (S : Finset V) (c : V → Bool)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    cellMoment (fairModel V) (fun d => edgeIndicator d e) (partialCell S c) /
      cellMass (fairModel V) (partialCell S c) = edgeMean S c e := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · have hconst : ∀ d ∈ partialCell S c, edgeIndicator d s(a,b) = edgeIndicator c s(a,b) := by
          intro d hd
          have hd' := mem_partialCell S c d |>.mp hd
          simp [edgeIndicator, hd' a ha, hd' b hb]
        have hm : cellMoment (fairModel V) (fun d => edgeIndicator d s(a,b)) (partialCell S c) =
            cellMass (fairModel V) (partialCell S c) * edgeIndicator c s(a,b) := by
          rw [cellMoment, cellMass_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun d hd => by rw [hconst d hd])
        rw [hm, mul_div_cancel_left₀ _ (ne_of_gt (partial_positive S c))]
        simp [edgeMean, edgeIndicator, ha, hb]
      · rw [Sym2.eq_swap]
        simpa [edgeMean, hb] using unrevealed_moment S c b a hab.symm hb
    · simpa [edgeMean, ha] using unrevealed_moment S c a b hab ha

theorem conditional_formula (G : SimpleGraph V) (S : Finset V) (c : V → Bool) :
    conditionalCut G S c = potential G S c := by
  classical
  have hm : cellMoment (fairModel V) (cutObjective G) (partialCell S c) =
      ∑ e ∈ G.edgeFinset, cellMoment (fairModel V) (fun d => edgeIndicator d e) (partialCell S c) := by
    simp only [cellMoment, cutObjective, Finset.mul_sum]
    exact Finset.sum_comm
  unfold conditionalCut potential
  rw [hm, Finset.sum_div]
  exact Finset.sum_congr rfl (fun e he => conditional_edge G S c e he)

lemma potential_empty (G : SimpleGraph V) (c : V → Bool) :
    potential G ∅ c = (G.edgeFinset.card : ℝ) / 2 := by
  classical
  unfold potential
  have h : ∀ e : Sym2 V, edgeMean ∅ c e = 1 / 2 := by
    intro e
    induction e using Sym2.inductionOn with
    | _ a b => simp [edgeMean]
  simp only [h, Finset.sum_const, nsmul_eq_mul]
  ring

lemma potential_univ (G : SimpleGraph V) (c : V → Bool) :
    potential G Finset.univ c = cutObjective G c := by
  classical
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ a b => simp [edgeMean, edgeIndicator]

lemma partialCell_empty (c : V → Bool) : partialCell ∅ c = Finset.univ := by
  classical
  ext d
  simp

lemma partialCell_univ (c : V → Bool) : partialCell Finset.univ c = {c} := by
  classical
  ext d
  simp only [mem_partialCell, Finset.mem_univ, forall_const, Finset.mem_singleton]
  exact funext_iff.symm

theorem initial_expectation (G : SimpleGraph V) :
    (fairModel V).expectation (cutObjective G) = (G.edgeFinset.card : ℝ) / 2 := by
  have h := conditional_formula G ∅ (fun _ => false)
  simpa only [conditionalCut, partialCell_empty, cellMass_univ, div_one,
    cellMoment, FiniteModel.expectation, potential_empty] using h

omit [Fintype V] in
lemma edgeMean_average (S : Finset V) (c : V → Bool) (v : V) (hv : v ∉ S)
    (a b : V) (hab : a ≠ b) :
    edgeMean S c s(a,b) =
      (edgeMean (insert v S) (Function.update c v false) s(a,b) +
       edgeMean (insert v S) (Function.update c v true) s(a,b)) / 2 := by
  classical
  by_cases hav : a = v
  · subst a
    have hb : b ≠ v := hab.symm
    by_cases hbS : b ∈ S
    · cases hcb : c b <;> norm_num [edgeMean, hv, hb, hbS, hcb]
    · norm_num [edgeMean, hv, hb, hbS]
  · by_cases hbv : b = v
    · subst b
      by_cases haS : a ∈ S
      · cases hca : c a <;> norm_num [edgeMean, hv, hav, haS, hca]
      · norm_num [edgeMean, hv, hav, haS]
    · simp only [edgeMean, Sym2.lift_mk, Finset.mem_insert, hav, hbv,
        false_or, Function.update_of_ne hav, Function.update_of_ne hbv]
      ring

lemma potential_average (G : SimpleGraph V) (S : Finset V) (c : V → Bool)
    (v : V) (hv : v ∉ S) :
    potential G S c =
      (potential G (insert v S) (Function.update c v false) +
       potential G (insert v S) (Function.update c v true)) / 2 := by
  classical
  unfold potential
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.inductionOn with
  | _ a b =>
    exact edgeMean_average S c v hv a b
      (G.mem_edgeSet.mp (G.mem_edgeFinset.mp he)).ne

theorem choose_bit (G : SimpleGraph V) (S : Finset V) (c : V → Bool)
    (v : V) (hv : v ∉ S) :
    ∃ b : Bool, potential G S c ≤ potential G (insert v S) (Function.update c v b) := by
  have h := potential_average G S c v hv
  by_cases hle : potential G S c ≤ potential G (insert v S) (Function.update c v false)
  · exact ⟨false, hle⟩
  · exact ⟨true, by linarith⟩

lemma revealed_zero {n : ℕ} (e : Fin n ≃ V) : revealed e 0 = ∅ := by
  classical
  ext v
  simp [revealed]

lemma revealed_last {n : ℕ} (e : Fin n ≃ V) : revealed e n = Finset.univ := by
  classical
  ext v
  simp [revealed]

lemma not_mem_revealed {n : ℕ} (e : Fin n ≃ V) (i : ℕ) (hi : i < n) :
    e ⟨i, hi⟩ ∉ revealed e i := by
  simp [revealed]

lemma revealed_next {n : ℕ} (e : Fin n ≃ V) (i : ℕ) (hi : i < n) :
    revealed e (i + 1) = insert (e ⟨i, hi⟩) (revealed e i) := by
  classical
  ext v
  have heq : v = e ⟨i, hi⟩ ↔ (e.symm v).val = i := by
    constructor
    · rintro rfl
      simp
    · intro hv
      apply e.symm.injective
      apply Fin.ext
      simpa using hv
  simp only [revealed, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, heq]
  omega

lemma partialCell_update_subset (S : Finset V) (c : V → Bool) (v : V)
    (b : Bool) (hv : v ∉ S) :
    partialCell (insert v S) (Function.update c v b) ⊆ partialCell S c := by
  classical
  intro d hd
  simp only [mem_partialCell] at hd ⊢
  intro w hw
  have hwv : w ≠ v := by rintro rfl; exact hv hw
  simpa [hwv] using hd w (Finset.mem_insert_of_mem hw)

/-- Iterate the two-child averaging rule in the supplied vertex order. -/
theorem successive_choices (G : SimpleGraph V) (n : ℕ) (e : Fin n ≃ V) :
    ∃ c : ℕ → (V → Bool), c 0 = (fun _ => false) ∧
      (∀ i (hi : i < n), ∃ b : Bool, c (i + 1) = Function.update (c i) (e ⟨i, hi⟩) b) ∧
      (∀ i, i < n → partialCell (revealed e (i + 1)) (c (i + 1)) ⊆
          partialCell (revealed e i) (c i) ∧
        0 < cellMass (fairModel V) (partialCell (revealed e i) (c i)) ∧
        conditionalCut G (revealed e i) (c i) ≤
          conditionalCut G (revealed e (i + 1)) (c (i + 1))) ∧
      partialCell (revealed e n) (c n) = {c n} ∧
      0 < (fairModel V).weight (c n) ∧
      conditionalCut G (revealed e n) (c n) = ((cutEdges G (c n)).card : ℝ) ∧
      (G.edgeFinset.card : ℝ) / 2 ≤ ((cutEdges G (c n)).card : ℝ) := by
  classical
  let bit (i : ℕ) (hi : i < n) (d : V → Bool) : Bool :=
    (choose_bit G (revealed e i) d (e ⟨i,hi⟩) (not_mem_revealed e i hi)).choose
  have hbit (i : ℕ) (hi : i < n) (d : V → Bool) :
      potential G (revealed e i) d ≤
        potential G (insert (e ⟨i,hi⟩) (revealed e i))
          (Function.update d (e ⟨i,hi⟩) (bit i hi d)) :=
    (choose_bit G (revealed e i) d (e ⟨i,hi⟩) (not_mem_revealed e i hi)).choose_spec
  let step (i : ℕ) (d : V → Bool) : V → Bool :=
    if hi : i < n then Function.update d (e ⟨i,hi⟩) (bit i hi d) else d
  let c : ℕ → (V → Bool) := fun i => Nat.rec (fun _ => false) step i
  have hsucc (i : ℕ) (hi : i < n) :
      c (i + 1) = Function.update (c i) (e ⟨i,hi⟩) (bit i hi (c i)) := by
    change step i (c i) = _
    simp only [step, dite_eq_left hi]
  have hmono (i : ℕ) (hi : i < n) :
      potential G (revealed e i) (c i) ≤ potential G (revealed e (i + 1)) (c (i + 1)) := by
    rw [hsucc i hi, revealed_next e i hi]
    exact hbit i hi (c i)
  have hbound (i : ℕ) (hi : i ≤ n) :
      (G.edgeFinset.card : ℝ) / 2 ≤ potential G (revealed e i) (c i) := by
    induction i with
    | zero => simp only [revealed_zero, potential_empty]; exact le_refl _
    | succ i ih =>
      have hin : i < n := Nat.lt_of_succ_le hi
      exact (ih (Nat.le_of_lt hin)).trans (hmono i hin)
  refine ⟨c, rfl, ?_, ?_, ?_, fair_weight_pos _, ?_, ?_⟩
  · intro i hi
    exact ⟨bit i hi (c i), hsucc i hi⟩
  · intro i hi
    refine ⟨?_, partial_positive _ _, ?_⟩
    · rw [hsucc i hi, revealed_next e i hi]
      exact partialCell_update_subset _ _ _ _ (not_mem_revealed e i hi)
    · simpa only [conditional_formula] using hmono i hi
  · rw [revealed_last, partialCell_univ]
  · rw [conditional_formula, revealed_last, potential_univ, cut_count]
  · simpa only [revealed_last, potential_univ, cut_count] using hbound n (le_refl n)

theorem exists_cut (G : SimpleGraph V) :
    ∃ c : V → Bool, (G.edgeFinset.card : ℝ) / 2 ≤ ((cutEdges G c).card : ℝ) := by
  obtain ⟨c, _, _, _, _, _, _, h⟩ :=
    successive_choices G (Fintype.card V) (Fintype.equivFin V).symm
  exact ⟨c (Fintype.card V), h⟩

end P205.Probability.ConditionalMaxCut
