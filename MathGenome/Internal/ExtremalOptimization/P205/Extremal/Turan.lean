import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.Turan
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace P205.Extremal

open SimpleGraph

theorem turan_extremal : TuranSpecs.extremalStatement := by
  intro V _ G _ r hr hG
  refine ⟨hG.card_edgeFinset_le, ?_⟩
  constructor
  · intro he
    apply (isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp
    refine ⟨hG, ?_⟩
    intro H _ hH
    exact he ▸ hH.card_edgeFinset_le
  · rintro ⟨f⟩
    exact f.card_edgeFinset_eq

theorem mantel_bound : TuranSpecs.mantelStatement := by
  intro V _ G _ hG
  exact hG.card_edgeFinset_le.trans_eq turanNumber_two

/-- The residue classes include every one of the `r` possible parts. -/
theorem turan_balanced_parts : TuranSpecs.balancedStatement := by
  intro n r hr
  let P : Fin r → Finset (Fin n) := fun i => Finset.univ.filter (fun v => v.val % r = i.val)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro v
    refine ⟨⟨v.val % r, Nat.mod_lt _ hr⟩, ?_, ?_⟩
    · simp [P]
    · intro i hi
      apply Fin.ext
      exact (by simpa [P] using hi : v.val % r = i.val).symm
  · intro v w
    simp only [turanGraph_adj, P, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h ⟨i, hv, hw⟩
      exact h (hv.trans hw.symm)
    · intro h hvw
      exact h ⟨⟨v.val % r, Nat.mod_lt _ hr⟩, rfl, hvw.symm⟩
  · intro i
    have hcount := Nat.count_modEq_card (b := n) hr i.val
    rw [Nat.mod_eq_of_lt i.isLt, Nat.count_eq_card_filter_range] at hcount
    have hcard : (P i).card = (Finset.range n |>.filter (fun v => v ≡ i.val [MOD r])).card := by
      apply Finset.card_bij (fun v _ => v.val)
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P] at hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr v.isLt,
          by simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt] using hv⟩
      · intro v hv w hw he
        exact Fin.ext he
      · intro v hv
        have hvn := (Finset.mem_range.mp (Finset.mem_filter.mp hv).1)
        refine ⟨⟨v, hvn⟩, ?_, rfl⟩
        simpa only [P, Finset.mem_filter, Finset.mem_univ, true_and, Nat.ModEq,
          Nat.mod_eq_of_lt i.isLt] using (Finset.mem_filter.mp hv).2
    exact hcard.trans hcount

private lemma twice_choose_two_add (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

private lemma choose_two_add (n r : ℕ) :
    (n + r).choose 2 = n.choose 2 + r.choose 2 + n * r := by
  have hn := twice_choose_two_add n
  have hr := twice_choose_two_add r
  have hnr := twice_choose_two_add (n + r)
  nlinarith only [hn, hr, hnr]

private lemma turan_number_add_missing_pairs (q b r : ℕ) (hr : 0 < r) (hb : b < r) :
    turanNumber (q * r + b) r + (r - b) * q.choose 2 + b * (q + 1).choose 2 =
      (q * r + b).choose 2 := by
  induction q with
  | zero =>
    norm_num only [Nat.zero_mul, Nat.zero_add, Nat.choose, Nat.mul_zero, Nat.add_zero]
    have ht : turanGraph b r = ⊤ := turanGraph_eq_top.mpr (Or.inr hb.le)
    have he := card_edgeFinset_top_eq_card_choose_two (V := Fin b)
    rw [Fintype.card_fin] at he
    convert he
  | succ q ih =>
    have hcoef : (r - b) * q + b * (q + 1) = q * r + b := by
      calc
        _ = (r - b + b) * q + b := by ring
        _ = _ := by rw [Nat.sub_add_cancel hb.le]; ring
    have hc1 : (q + 1).choose 2 = q.choose 2 + q := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.add_comm _ _
    have hc2 : (q + 1 + 1).choose 2 = (q + 1).choose 2 + (q + 1) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.add_comm _ _
    have hm : (r - b) * (q + 1).choose 2 + b * (q + 1 + 1).choose 2 =
        (r - b) * q.choose 2 + b * (q + 1).choose 2 + (q * r + b) := by
      rw [hc2]
      nth_rw 1 [hc1]
      nlinarith only [hcoef]
    rw [show (q + 1) * r + b = (q * r + b) + r by ring, turanNumber_add,
      choose_two_add (q * r + b) r]
    have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
    have he : (q * r + b) * (r - 1) + (q * r + b) = (q * r + b) * r := by
      nlinarith only [congrArg (fun x => (q * r + b) * x) hpred]
    omega

theorem turan_edge_formula : TuranSpecs.edgeFormulaStatement := by
  intro n r q b hr hb hn
  subst n
  have h := turan_number_add_missing_pairs q b r hr hb
  change turanNumber (q * r + b) r = _
  omega

end P205.Extremal
