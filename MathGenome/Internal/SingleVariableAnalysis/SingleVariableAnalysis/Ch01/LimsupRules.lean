import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Limsup
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.LimitAlgebra
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.LimsupRules
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Limsup rules and convergence

K03.01.limsup_rules, paper.tex:301–313. The upstream tail definitions are
identified with filter liminf and limsup. Mathlib's order-topological limit
criterion and extended-real sum lemmas then apply. Boundedness certifies the
finite endpoints needed by the upper sum inequality. The example computes
both tail suprema by exhibiting a term equal to one in every tail.
-/

noncomputable section
namespace SingleVariableAnalysis

open Filter
open scoped Topology

open private sequenceLimsup_eq_filter sequenceLiminf_eq_filter finite_ne
  from MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Limsup

theorem bounded_convergence_iff_liminf_limsup (a : ℕ → ℝ)
    (_ha : BddAbove (Set.range a)) (_hb : BddBelow (Set.range a)) (L : ℝ) :
    RealSequenceConverges a L ↔
      sequenceLiminf a = (L : EReal) ∧ sequenceLimsup a = (L : EReal) := by
  rw [realSequenceConverges_iff, sequenceLiminf_eq_filter, sequenceLimsup_eq_filter]
  constructor
  · intro h
    have h' := EReal.tendsto_coe.mpr h
    exact ⟨h'.liminf_eq, h'.limsup_eq⟩
  · rintro ⟨hinf, hsup⟩
    exact EReal.tendsto_coe.mp (tendsto_of_liminf_eq_limsup hinf hsup)

theorem bounded_liminf_limsup_sum (a b : ℕ → ℝ)
    (ha : BddAbove (Set.range a)) (ha' : BddBelow (Set.range a))
    (_hb : BddAbove (Set.range b)) (_hb' : BddBelow (Set.range b)) :
    sequenceLiminf a + sequenceLiminf b ≤ sequenceLiminf (fun n => a n + b n) ∧
    sequenceLiminf (fun n => a n + b n) ≤ sequenceLimsup (fun n => a n + b n) ∧
    sequenceLimsup (fun n => a n + b n) ≤ sequenceLimsup a + sequenceLimsup b := by
  have hfinite := finite_ne (bounded_bounds_finite a ha ha').2.1
  rw [sequenceLimsup_eq_filter] at hfinite
  simp only [sequenceLiminf_eq_filter, sequenceLimsup_eq_filter]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [EReal.coe_add, Pi.add_def] using
      (EReal.le_liminf_add (u := fun n => (a n : EReal))
        (v := fun n => (b n : EReal)) (f := atTop))
  · exact liminf_le_limsup
  · simpa only [EReal.coe_add, Pi.add_def] using
      (EReal.limsup_add_le (u := fun n => (a n : EReal))
        (v := fun n => (b n : EReal)) (f := atTop)
        (Or.inl hfinite.2) (Or.inl hfinite.1))

theorem bounded_limsup_neg (a : ℕ → ℝ)
    (_ha : BddAbove (Set.range a)) (_hb : BddBelow (Set.range a)) :
    sequenceLimsup (fun n => -a n) = -sequenceLiminf a := by
  simp only [sequenceLimsup_eq_filter, sequenceLiminf_eq_filter]
  simpa only [EReal.coe_neg, Pi.neg_def] using
    (EReal.limsup_neg (v := fun n => (a n : EReal)) (f := atTop))

theorem limsup_sum_strict_example :
    let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 1)
    let b : ℕ → ℝ := fun n => -a n
    BddAbove (Set.range a) ∧ BddBelow (Set.range a) ∧
    BddAbove (Set.range b) ∧ BddBelow (Set.range b) ∧
    sequenceLimsup a = 1 ∧ sequenceLimsup b = 1 ∧
    sequenceLimsup (fun n => a n + b n) = 0 ∧
    sequenceLimsup (fun n => a n + b n) <
      sequenceLimsup a + sequenceLimsup b ∧ (0 : ℝ) < 2 := by
  let a : ℕ → ℝ := fun n => (-1 : ℝ) ^ (n + 1)
  let b : ℕ → ℝ := fun n => -a n
  have habs (n : ℕ) : |a n| = 1 := by simp [a]
  have ha (n : ℕ) : -1 ≤ a n ∧ a n ≤ 1 :=
    abs_le.mp (habs n).le
  have hb (n : ℕ) : -1 ≤ b n ∧ b n ≤ 1 := by
    have h := ha n
    dsimp [b]
    constructor <;> linarith
  have hTa (N : ℕ) : tailSupremum a N = 1 := by
    apply le_antisymm
    · exact iSup_le fun n => iSup_le fun _ => by exact_mod_cast (ha n).2
    · have hterm : a (2 * N + 1) = 1 := by
        dsimp [a]
        rw [show 2 * N + 1 + 1 = 2 * (N + 1) by omega, pow_mul]
        norm_num
      have hle : (a (2 * N + 1) : EReal) ≤ tailSupremum a N :=
        le_iSup_of_le (2 * N + 1) (le_iSup_of_le (by omega : N ≤ 2 * N + 1) le_rfl)
      simpa [hterm] using hle
  have hTb (N : ℕ) : tailSupremum b N = 1 := by
    apply le_antisymm
    · exact iSup_le fun n => iSup_le fun _ => by exact_mod_cast (hb n).2
    · have hterm : b (2 * N) = 1 := by
        simp [b, a, pow_add, pow_mul]
      have hle : (b (2 * N) : EReal) ≤ tailSupremum b N :=
        le_iSup_of_le (2 * N) (le_iSup_of_le (by omega : N ≤ 2 * N) le_rfl)
      simpa [hterm] using hle
  have hUa : sequenceLimsup a = 1 := by simp [sequenceLimsup, hTa]
  have hUb : sequenceLimsup b = 1 := by simp [sequenceLimsup, hTb]
  have hsum : sequenceLimsup (fun n => a n + b n) = 0 := by
    rw [sequenceLimsup_eq_filter]
    simp only [b, add_neg_cancel, EReal.coe_zero]
    exact tendsto_const_nhds.limsup_eq
  refine ⟨⟨1, ?_⟩, ⟨-1, ?_⟩, ⟨1, ?_⟩, ⟨-1, ?_⟩, hUa, hUb, hsum, ?_, by norm_num⟩
  · rintro _ ⟨n, rfl⟩; exact (ha n).2
  · rintro _ ⟨n, rfl⟩; exact (ha n).1
  · rintro _ ⟨n, rfl⟩; exact (hb n).2
  · rintro _ ⟨n, rfl⟩; exact (hb n).1
  · rw [hsum, hUa, hUb]
    norm_num

end SingleVariableAnalysis
