import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertPolynomialGrowth
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.Linarith

namespace P103.HilbertPolynomialGrowth
open Polynomial Filter
open P103.HilbertSerreLength

/-- A positive leading coefficient gives positivity on the integer tail,
including for a nonzero constant polynomial. -/
theorem eventually_pos_eval (P : Polynomial ℚ) (hp : 0 < P.leadingCoeff) :
    ∀ᶠ j : ℤ in atTop, 0 < P.eval (j : ℚ) := by
  by_cases hd : P.natDegree = 0
  · have he : P = C P.leadingCoeff := by
      rw [leadingCoeff, hd]; exact eq_C_of_natDegree_eq_zero hd
    exact Eventually.of_forall fun j => by rw [he, eval_C]; exact hp
  · exact ((P.tendsto_atTop_of_leadingCoeff_nonneg
      (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) hp.le
      ).eventually_gt_atTop 0).intCast_atTop

/-- Eventual nonnegative values force a nonnegative leading coefficient. -/
theorem leadingCoeff_nonneg_of_eventually_nonneg (P : Polynomial ℚ)
    (hP : ∀ᶠ j : ℤ in atTop, 0 ≤ P.eval (j : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_contra hn
  have hp : 0 < (-P).leadingCoeff := by
    rw [leadingCoeff_neg]; exact neg_pos.mpr (lt_of_not_ge hn)
  obtain ⟨j, hj, hj'⟩ := (hP.and (eventually_pos_eval (-P) hp)).exists
  simp only [eval_neg] at hj'
  linarith

/-- A polynomial with positive leading coefficient cannot be bounded above
on the integer tail by a polynomial of smaller degree. -/
theorem natDegree_le_of_eventually_le (P Q : Polynomial ℚ)
    (hp : 0 < P.leadingCoeff)
    (hPQ : ∀ᶠ j : ℤ in atTop, P.eval (j : ℚ) ≤ Q.eval (j : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hn
  have hd : Q.degree < P.degree := degree_lt_degree (lt_of_not_ge hn)
  have hc : 0 < (P - Q).leadingCoeff := by
    rwa [leadingCoeff_sub_of_degree_lt hd]
  obtain ⟨j, hj, hj'⟩ := (hPQ.and (eventually_pos_eval (P - Q) hc)).exists
  simp only [eval_sub] at hj'
  linarith

/-- Stars and bars as an actual rational polynomial, valid at every
nonnegative integer degree, including degree zero. -/
theorem preHilbertPoly_eval_int (n : ℕ) (j : ℤ) (hj : 0 ≤ j) :
    (preHilbertPoly ℚ n 0).eval (j : ℚ) = ((j.toNat + n).choose n : ℚ) := by
  have hc : (j : ℚ) = (j.toNat : ℚ) := by
    exact_mod_cast (Int.toNat_of_nonneg hj).symm
  rw [hc]
  simpa using preHilbertPoly_eq_choose_add_sub ℚ n (k := 0) (n := j.toNat)
    (Nat.zero_le _)

/-- An eventual polynomial identity may be translated by any integer. -/
theorem eventuallyPolynomial_shift {h : ℤ → ℤ} {q : Polynomial ℚ}
    (hq : EventuallyPolynomial h q) (a : ℤ) :
    ∀ᶠ j : ℤ in atTop, (h (j + a) : ℚ) = q.eval ((j : ℚ) + (a : ℚ)) := by
  obtain ⟨J, hJ⟩ := hq
  apply eventually_atTop.mpr
  refine ⟨J - a, fun j hj => ?_⟩
  simpa only [Int.cast_add] using hJ (j + a) (by omega)

/-- Finite translations cannot increase the degree of their sum. -/
theorem natDegree_sum_comp_add_le {r : ℕ} (q : Polynomial ℚ) (a : Fin r → ℤ) :
    (∑ i, q.comp (X + C (a i : ℚ))).natDegree ≤ q.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  simp only [natDegree_comp, natDegree_X_add_C, mul_one, le_refl]

theorem comparison : Specs.P103.HilbertPolynomialGrowth.comparisonType := by
  classical
  intro h b p e hnonneg hp hred d r hd hr a J hJ hJa hupper hlower
  obtain ⟨q, hq, hzero, hdegree⟩ := P103.HilbertSerreLength.coefficients h b p e hp
  let B : Polynomial ℚ := preHilbertPoly ℚ (d - 1) 0
  have hBdeg : B.natDegree = d - 1 := natDegree_preHilbertPoly ℚ (d - 1) 0
  have hBpos : 0 < B.leadingCoeff := by
    rw [show B.leadingCoeff = _ from leadingCoeff_preHilbertPoly ℚ (d - 1) 0]
    positivity
  have hB (j : ℤ) (hj : 0 ≤ j) :
      B.eval (j : ℚ) = ((j.toNat + d - 1).choose (d - 1) : ℚ) := by
    simpa only [Nat.add_sub_assoc hd] using preHilbertPoly_eval_int (d - 1) j hj
  have hqtail : ∀ᶠ j : ℤ in atTop, (h j : ℚ) = q.eval (j : ℚ) := by
    obtain ⟨K, hK⟩ := hq
    exact eventually_atTop.mpr ⟨K, hK⟩
  have hqnonneg : ∀ᶠ j : ℤ in atTop, 0 ≤ q.eval (j : ℚ) := by
    filter_upwards [hqtail] with j hj
    rw [← hj]
    exact_mod_cast hnonneg j
  let L : Polynomial ℚ := ∑ i, q.comp (X + C (a i : ℚ))
  have hLdeg : L.natDegree ≤ q.natDegree := natDegree_sum_comp_add_le q a
  have hBL : ∀ᶠ j : ℤ in atTop, B.eval (j : ℚ) ≤ L.eval (j : ℚ) := by
    have hs : ∀ᶠ j : ℤ in atTop,
        ∀ i, (h (j + a i) : ℚ) = q.eval ((j : ℚ) + (a i : ℚ)) :=
      eventually_all.mpr fun i => eventuallyPolynomial_shift hq (a i)
    filter_upwards [eventually_ge_atTop J, hs] with j hj hs
    rw [hB j (hJ.trans hj)]
    simpa only [L, eval_finsetSum, eval_comp, eval_add, eval_X, eval_C, ← hs] using
      hlower j hj
  have hqne : q ≠ 0 := by
    intro hz
    obtain ⟨j, hj, hj'⟩ := (hBL.and (eventually_pos_eval B hBpos)).exists
    have hLzero : L = 0 := by simp [L, hz]
    rw [hLzero, eval_zero] at hj
    linarith
  have he : 0 < e := by
    by_contra hn
    have hz : e = 0 := by omega
    exact hqne (hzero hz).1
  have hpne : p.eval 1 ≠ 0 := hred.resolve_left (by omega)
  have hqdeg : q.natDegree = e - 1 := (hdegree he hpne).2.1
  have hqpos : 0 < q.leadingCoeff :=
    lt_of_le_of_ne (leadingCoeff_nonneg_of_eventually_nonneg q hqnonneg)
      (Ne.symm (leadingCoeff_ne_zero.mpr hqne))
  let R : Polynomial ℚ := ∑ i, B.comp (X - C (a i : ℚ))
  have hRdeg : R.natDegree ≤ B.natDegree := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    simp only [natDegree_comp, natDegree_X_sub_C, mul_one, le_refl]
  have hqR : ∀ᶠ j : ℤ in atTop, q.eval (j : ℚ) ≤ R.eval (j : ℚ) := by
    filter_upwards [eventually_ge_atTop J, hqtail] with j hj hqj
    rw [← hqj]
    have hterm (i : Fin r) :
        (B.comp (X - C (a i : ℚ))).eval (j : ℚ) =
          (((j - a i).toNat + d - 1).choose (d - 1) : ℚ) := by
      simp only [eval_comp, eval_sub, eval_X, eval_C]
      rw [← Int.cast_sub]
      exact hB (j - a i) (by have := hJa i; omega)
    simpa only [R, eval_finsetSum, hterm] using hupper j hj
  have hle : e - 1 ≤ d - 1 := by
    rw [← hqdeg, ← hBdeg]
    exact (natDegree_le_of_eventually_le q R hqpos hqR).trans hRdeg
  have hge : d - 1 ≤ e - 1 := by
    rw [← hqdeg, ← hBdeg]
    exact (natDegree_le_of_eventually_le B L hBpos hBL).trans hLdeg
  omega

end P103.HilbertPolynomialGrowth
