import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SimpleRootLifting
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse

namespace GaloisFormalization.IG

open Polynomial
open scoped PowerSeries

private theorem liftOverField {L : Type*} [Field L] (g : (PowerSeries L)[X]) (r : L)
    (hr : (g.map PowerSeries.constantCoeff).eval r = 0)
    (hd : (g.map PowerSeries.constantCoeff).derivative.eval r ≠ 0) :
    ∃! a : PowerSeries L, PowerSeries.constantCoeff a = r ∧ g.eval a = 0 := by
  classical
  let I : Ideal (PowerSeries L) := Ideal.span {PowerSeries.X}
  have hmem {x : PowerSeries L} : x ∈ I ↔ PowerSeries.constantCoeff x = 0 :=
    Ideal.mem_span_singleton.trans PowerSeries.X_dvd_iff
  have hunit (x : PowerSeries L) (hx : PowerSeries.constantCoeff x = r) :
      IsUnit (g.derivative.eval x) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, ← eval_map_apply,
      ← derivative_map, hx]
    exact hd
  let correction (x : PowerSeries L) :=
    -(g.eval x * Ring.inverse (g.derivative.eval x))
  let a : ℕ → PowerSeries L :=
    Nat.rec (PowerSeries.C r) fun _ x => x + correction x
  have hstep (n : ℕ) : a (n + 1) = a n + correction (a n) := rfl
  -- The Newton correction preserves the residue and gains at least one power of X.
  have ha (n : ℕ) : PowerSeries.constantCoeff (a n) = r ∧ g.eval (a n) ∈ I ^ (n + 1) := by
    induction n with
    | zero =>
      refine ⟨PowerSeries.constantCoeff_C r, ?_⟩
      rw [zero_add, pow_one, hmem, ← eval_map_apply]
      change (g.map PowerSeries.constantCoeff).eval
        (PowerSeries.constantCoeff (PowerSeries.C r)) = 0
      rw [PowerSeries.constantCoeff_C]
      exact hr
    | succ n ih =>
      have hc : correction (a n) ∈ I ^ (n + 1) :=
        (I ^ (n + 1)).neg_mem ((I ^ (n + 1)).mul_mem_right _ ih.2)
      have hc₀ : PowerSeries.constantCoeff (correction (a n)) = 0 := by
        apply hmem.mp
        simpa only [pow_one] using Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) hc
      refine ⟨by rw [hstep, map_add, ih.1, hc₀, add_zero], ?_⟩
      have hcancel : g.derivative.eval (a n) * correction (a n) + g.eval (a n) = 0 := by
        dsimp only [correction]
        rw [mul_neg, mul_left_comm, Ring.mul_inverse_cancel _ (hunit _ ih.1), mul_one,
          neg_add_cancel]
      obtain ⟨q, hq⟩ := exists_mul_sq_add_linear_part_eq_eval_add g (a n) (correction (a n))
      rw [hstep, ← hq, add_assoc (q * correction (a n) ^ 2), hcancel, add_zero]
      have hsq : correction (a n) ^ 2 ∈ I ^ ((n + 1) + (n + 1)) := by
        rw [pow_two, pow_add]
        exact Ideal.mul_mem_mul hc hc
      exact (I ^ (n + 1 + 1)).mul_mem_left q (Ideal.pow_le_pow_right (by omega) hsq)
  have hdiff (n : ℕ) : a n - a (n + 1) ∈ I ^ (n + 1) := by
    rw [hstep, sub_add_cancel_left]
    dsimp only [correction]
    rw [neg_neg]
    exact (I ^ (n + 1)).mul_mem_right _ (ha n).2
  have hsmul (n : ℕ) :
      (I ^ n • (⊤ : Submodule (PowerSeries L) (PowerSeries L))) =
        (I ^ n : Ideal (PowerSeries L)) := by
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → a m ≡ a n [SMOD (I ^ m : Ideal (PowerSeries L))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction j with
    | zero => simp
    | succ j ih =>
      have hj := Ideal.pow_le_pow_right (by omega : m ≤ (m + j) + 1) (hdiff (m + j))
      simpa only [sub_add_sub_cancel, Nat.add_assoc] using (I ^ m).add_mem ih hj
  obtain ⟨b, hb⟩ := IsPrecomplete.prec' (I := I) a (by
    intro m n hmn
    rw [hsmul]
    exact hcauchy hmn)
  have hb₀ : PowerSeries.constantCoeff b = r := by
    have hb₁ := hb 1
    rw [hsmul, pow_one, SModEq.sub_mem] at hb₁
    have h := hmem.mp hb₁
    rw [map_sub, sub_eq_zero, (ha 1).1] at h
    exact h.symm
  have hbroot : g.eval b = 0 := by
    apply (IsHausdorff.eq_iff_smodEq (I := I)).2
    intro n
    have hn : a n ≡ b [SMOD (I ^ n : Ideal (PowerSeries L))] := by
      simpa only [hsmul] using hb n
    rw [hsmul]
    refine (hn.symm.eval g).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) (ha n).2
  refine ⟨b, ⟨hb₀, hbroot⟩, ?_⟩
  rintro x ⟨hx, hxroot⟩
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hxroot hbroot _ (hunit x hx)
  rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, hx, hb₀, sub_self]
  exact not_isUnit_zero

/-- A simple root of the reduction lifts uniquely after extending coefficients. -/
theorem simpleRootLifting : Specs.GaloisFormalization.IG.simpleRootLiftingType := by
  intro k L _ _ _ f r
  dsimp only
  intro hr hd
  let g := f.map (PowerSeries.map (algebraMap k L))
  have hreduce : g.map PowerSeries.constantCoeff =
      (f.map PowerSeries.constantCoeff).map (algebraMap k L) := by
    dsimp only [g]
    rw [Polynomial.map_map, Polynomial.map_map]
    rfl
  exact liftOverField g r (by rwa [hreduce]) (by rwa [hreduce])

end GaloisFormalization.IG
