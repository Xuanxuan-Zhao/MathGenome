import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.PeriodicQuadraticAlgebra
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticContinuedFractions
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ContinuedFractionErrors
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Batteries.Tactic.OpenPrivate

namespace P203
open P203Specs Polynomial
open private numerator_nat denominator_nat numerator_prev denominator_prev from MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.Convergents

/-- Shifting the canonical algorithm shifts its digits, with existence supplied
by irrationality. -/
theorem partialQuotient_iterate (x : ℝ) (hx : Irrational x) (m n : ℕ) :
    P203Specs.partialQuotient (continuedFractionStep^[m] x) n =
      P203Specs.partialQuotient x (m + n) := by
  rw [(quotient_iterates _ (quotient_iterates x hx m).1 n).2.2,
    (quotient_iterates x hx (m + n)).2.2]
  rw [Nat.add_comm m n, Function.iterate_add_apply]

/-- A nonzero rational quadratic annihilating an irrational real is its
minimal polynomial up to its leading scalar. -/
theorem quadratic_of_equation (x : ℝ) (hx : Irrational x) (A B C : ℚ)
    (hA : A ≠ 0) (he : (A : ℝ) * x ^ 2 + (B : ℝ) * x + (C : ℝ) = 0) :
    P203Specs.QuadraticIrrational x ∧
      P203Specs.quadraticConjugate x = -(B : ℝ) / (A : ℝ) - x := by
  let p : Polynomial ℚ := Polynomial.C A * X ^ 2 + Polynomial.C B * X + Polynomial.C C
  have hpdeg : p.natDegree = 2 := natDegree_quadratic hA
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hpdeg
    norm_num at hpdeg
  have hroot : aeval x p = 0 := by simpa [p] using he
  have ha : IsAlgebraic ℚ x := ⟨p, hp0, hroot⟩
  have hlow : 2 ≤ (minpoly ℚ x).natDegree :=
    (minpoly.two_le_natDegree_iff ha.isIntegral).mpr hx
  have hdeg : (minpoly ℚ x).natDegree = 2 := by
    have := natDegree_le_of_dvd (minpoly.dvd ℚ x hroot) hp0
    omega
  have hpoly : p = minpoly ℚ x * Polynomial.C A := by
    simpa only [p, leadingCoeff_quadratic hA] using
      eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic ha.isIntegral) (minpoly.dvd ℚ x hroot) (by omega)
  have hc : B = (minpoly ℚ x).coeff 1 * A := by
    have := congrArg (fun q : Polynomial ℚ => q.coeff 1) hpoly
    simpa [p, coeff_mul_C] using this
  refine ⟨⟨ha, hdeg⟩, ?_⟩
  dsimp [P203Specs.quadraticConjugate]
  rw [hc, Rat.cast_mul]
  field_simp

/-- Quadraticity propagates backwards through a single canonical step.
This uses an explicit quadratic substitution and retains degree exactly two. -/
theorem quadratic_of_step (x : ℝ) (hx : Irrational x)
    (hz : P203Specs.QuadraticIrrational (continuedFractionStep x)) :
    P203Specs.QuadraticIrrational x := by
  let z := continuedFractionStep x
  let a : ℚ := (⌊x⌋ : ℤ)
  let B : ℚ := (minpoly ℚ z).coeff 1
  let C : ℚ := (minpoly ℚ z).coeff 0
  have hc : C ≠ 0 := minpoly.coeff_zero_ne_zero hz.1.isIntegral (step_irrational x hx).ne_zero
  have hcoeff : (minpoly ℚ z).coeff 2 = 1 := by
    rw [← hz.2]
    exact (minpoly.monic hz.1.isIntegral).coeff_natDegree
  have hpoly : minpoly ℚ z = Polynomial.C 1 * X ^ 2 + Polynomial.C B * X + Polynomial.C C := by
    have h := (minpoly ℚ z).as_sum_range_C_mul_X_pow
    rw [hz.2] at h
    simpa [Finset.sum_range_succ, B, C, hcoeff, add_comm, add_left_comm, add_assoc] using h
  have he : z ^ 2 + (B : ℝ) * z + (C : ℝ) = 0 := by
    have h := minpoly.aeval ℚ z
    rw [hpoly] at h
    simpa using h
  have hne : x - (a : ℝ) ≠ 0 := by
    simpa [a] using sub_ne_zero.mpr (hx.ne_int ⌊x⌋)
  have he' : (C : ℝ) * x ^ 2 + ((B - 2 * C * a : ℚ) : ℝ) * x +
      ((1 - B * a + C * a ^ 2 : ℚ) : ℝ) = 0 := by
    have hm := congrArg (fun t : ℝ => t * (x - (a : ℝ)) ^ 2) he
    change ((1 / (x - (⌊x⌋ : ℝ))) ^ 2 + (B : ℝ) * (1 / (x - (⌊x⌋ : ℝ))) +
      (C : ℝ)) * (x - (a : ℝ)) ^ 2 = 0 * (x - (a : ℝ)) ^ 2 at hm
    have ha : (a : ℝ) = (⌊x⌋ : ℝ) := by simp [a]
    rw [← ha] at hm
    field_simp [hne] at hm
    push_cast
    nlinarith [hm]
  exact (quadratic_of_equation x hx C (B - 2 * C * a)
    (1 - B * a + C * a ^ 2) hc he').1

/-- Positive digits make both continuant coordinates nondecreasing, and their
sum strictly increasing. This includes the exceptional first denominator pair. -/
private theorem positive_continuants (x : ℝ) (hx : Irrational x) (hf : 1 ≤ ⌊x⌋) (n : ℕ) :
    0 < (P203Specs.integerContinuants x n).a ∧
    0 ≤ (P203Specs.integerContinuants x n).b ∧
    (P203Specs.integerContinuants x n).a ≤ (P203Specs.integerContinuants x (n + 1)).a ∧
    (P203Specs.integerContinuants x n).b ≤ (P203Specs.integerContinuants x (n + 1)).b ∧
    (P203Specs.integerContinuants x n).a + (P203Specs.integerContinuants x n).b <
      (P203Specs.integerContinuants x (n + 1)).a + (P203Specs.integerContinuants x (n + 1)).b := by
  induction n with
  | zero =>
    simp only [P203Specs.integerContinuants]
    omega
  | succ n ih =>
    let a := ⌊continuedFractionStep^[n + 1] x⌋
    have ha : P203Specs.partialQuotient x (n + 1) = some a :=
      (quotient_iterates x hx (n + 1)).2.2
    have hapos := later_partialQuotients x a (n + 1) (by omega) ha
    rcases ih with ⟨hp, hq, hpm, hqm, hs⟩
    have hp' : 0 < (P203Specs.integerContinuants x (n + 1)).a := by omega
    have hq' : 0 ≤ (P203Specs.integerContinuants x (n + 1)).b := by omega
    have hpa := mul_le_mul_of_nonneg_right hapos hp'.le
    have hqa := mul_le_mul_of_nonneg_right hapos hq'
    change 0 < (P203Specs.integerContinuants x (n + 1)).a ∧
      0 ≤ (P203Specs.integerContinuants x (n + 1)).b ∧ _
    rw [show n + 1 + 1 = n + 2 by omega, P203Specs.integerContinuants, ha]
    refine ⟨hp', hq', ?_, ?_, ?_⟩ <;> nlinarith

/-- Equality of the repeated digit strings implies equality of real quotients,
using the convergence-based upstream uniqueness theorem. -/
theorem quotient_returns_of_period (x : ℝ) (hx : Irrational x) (r : ℕ)
    (hper : ∀ n, P203Specs.partialQuotient x (n + r) = P203Specs.partialQuotient x n) :
    continuedFractionStep^[r] x = x := by
  apply infinite_digit_uniqueness _ _ (quotient_iterates x hx r).1 hx
  intro n
  rw [partialQuotient_iterate x hx r n, Nat.add_comm r n, hper]

/-- The fixed point of a positive period has degree two and is reduced.
The proof also covers a period consisting of a single digit. -/
theorem purely_periodic_quadratic_reduced : PurelyPeriodicQuadraticReduced := by
  intro y hy hper
  obtain ⟨_, r, hr, hd⟩ := (pure_periodicity_bridge y).mp hper
  have hreturn := quotient_returns_of_period y hy r hd
  have hy1 : 1 < y := by
    have h := later_completeQuotients y (continuedFractionStep^[r] y) r (by omega)
      (quotient_iterates y hy r).2.1
    rwa [hreturn] at h
  have hf : 1 ≤ ⌊y⌋ := Int.le_floor.mpr (by simpa using hy1.le)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  obtain ⟨α, hα, hD, hDn, he, _⟩ := convergent_exact_tail y hy n
  have hαy : α = y := (Option.some.inj
    (hα.symm.trans (quotient_iterates y hy (n + 1)).2.1)).trans hreturn
  subst α
  simp only [numerator_nat, denominator_nat, numerator_prev, denominator_prev] at he hD hDn
  let p := (P203Specs.integerContinuants y (n + 1)).a
  let q := (P203Specs.integerContinuants y (n + 1)).b
  let pp := (P203Specs.integerContinuants y n).a
  let qp := (P203Specs.integerContinuants y n).b
  have hq : (0 : ℝ) < q := by
    exact_mod_cast (show 0 < q from by
      dsimp [q]
      rw [← denominator_nat]
      exact convergent_denominator_pos y n)
  have hpp : (0 : ℝ) < pp := by
    exact_mod_cast (positive_continuants y hy hf n).1
  have hsum : (0 : ℝ) < ((q : ℝ) - qp) + ((p : ℝ) - pp) := by
    have h := (positive_continuants y hy hf n).2.2.2.2
    have hi : (0 : ℤ) < (q - qp) + (p - pp) := by dsimp [q, qp, p, pp]; omega
    exact_mod_cast hi
  have heq : (q : ℝ) * y ^ 2 + ((qp : ℝ) - p) * y - pp = 0 := by
    have hm := (eq_div_iff hDn).mp he
    change y * ((q : ℝ) * y + qp) = (p : ℝ) * y + pp at hm
    nlinarith only [hm]
  have hqQ : (q : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hq)
  have hquad := quadratic_of_equation y hy (q : ℚ) ((qp : ℚ) - p) (-(pp : ℚ)) hqQ
    (by push_cast; exact heq)
  have hconj : P203Specs.quadraticConjugate y = -((qp : ℝ) - p) / q - y := by
    simpa only [Rat.cast_sub, Rat.cast_intCast] using hquad.2
  let c := P203Specs.quadraticConjugate y
  have hsumroots : (q : ℝ) * (y + c) = (p : ℝ) - qp := by
    dsimp [c]
    rw [hconj]
    field_simp [ne_of_gt hq]
    ring
  have hproduct : (q : ℝ) * y * c = -(pp : ℝ) := by
    have h := congrArg (fun t : ℝ => t * y) hsumroots
    nlinarith only [heq, h]
  have hqp : 0 < (q : ℝ) * y := mul_pos hq (by linarith)
  have hcneg : c < 0 := by
    by_contra hn
    have := mul_nonneg hqp.le (le_of_not_gt hn)
    linarith [hproduct]
  have hfactor : (q : ℝ) * (y + 1) * (c + 1) = ((q : ℝ) - qp) + ((p : ℝ) - pp) := by
    nlinarith only [hsumroots, hproduct]
  have hcgt : -1 < c := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_pos hq (show 0 < y + 1 by linarith)).le (show c + 1 ≤ 0 by linarith)
    linarith [hfactor]
  exact ⟨hquad.1, hquad.1, hy1, hcgt, hcneg⟩

/-- A finite number of inverse algorithm steps preserves quadratic degree. -/
theorem quadratic_of_iterate (x : ℝ) (hx : Irrational x) (m : ℕ)
    (hm : P203Specs.QuadraticIrrational (continuedFractionStep^[m] x)) :
    P203Specs.QuadraticIrrational x := by
  induction m generalizing x with
  | zero => exact hm
  | succ m ih =>
    apply quadratic_of_step x hx
    apply ih _ (step_irrational x hx)
    simpa only [Function.iterate_succ_apply] using hm

/-- An eventually periodic canonical expansion has a purely periodic complete
quotient. Backwards propagation covers every possible finite initial segment. -/
theorem eventually_periodic_quadratic : EventuallyPeriodicQuadratic := by
  intro x hx hp
  obtain ⟨_, m, r, hr, hd⟩ := (eventual_periodicity_bridge x).mp hp
  let y := continuedFractionStep^[m] x
  have hy : Irrational y := (quotient_iterates x hx m).1
  have hpy : P203Specs.PurelyPeriodicCF y := by
    apply (pure_periodicity_bridge y).mpr
    refine ⟨hy, r, hr, ?_⟩
    intro n
    change P203Specs.partialQuotient (continuedFractionStep^[m] x) (n + r) =
      P203Specs.partialQuotient (continuedFractionStep^[m] x) n
    rw [partialQuotient_iterate x hx m (n + r), partialQuotient_iterate x hx m n,
      ← Nat.add_assoc]
    exact hd (m + n) (by omega)
  exact quadratic_of_iterate x hx m (purely_periodic_quadratic_reduced y hy hpy).1

end P203
