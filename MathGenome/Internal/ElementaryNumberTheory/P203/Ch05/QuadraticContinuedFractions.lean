import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticContinuedFractions
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ContinuedFractionAlgorithm
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace P203

abbrev QuadraticIrrational : P203Specs.QuadraticIrrationalType := P203Specs.QuadraticIrrational
noncomputable abbrev quadraticConjugate : P203Specs.QuadraticConjugateType :=
  P203Specs.quadraticConjugate
abbrev ReducedQuadratic : P203Specs.ReducedQuadraticType := P203Specs.ReducedQuadratic
noncomputable abbrev continuedFractionStep : P203Specs.ContinuedFractionStepType :=
  P203Specs.continuedFractionStep
abbrev IsDigitSequence : P203Specs.IsDigitSequenceType := P203Specs.IsDigitSequence
abbrev EventuallyPeriodicDigits : P203Specs.PeriodicDigitsType := P203Specs.EventuallyPeriodicDigits
abbrev PurelyPeriodicDigits : P203Specs.PeriodicDigitsType := P203Specs.PurelyPeriodicDigits
abbrev EventuallyPeriodicCF : P203Specs.PeriodicCFType := P203Specs.EventuallyPeriodicCF
abbrev PurelyPeriodicCF : P203Specs.PeriodicCFType := P203Specs.PurelyPeriodicCF

open P203Specs Polynomial

theorem quadratic_is_irrational : QuadraticIsIrrational := by
  intro x hx
  exact (minpoly.two_le_natDegree_iff hx.1.isIntegral).mp (by rw [hx.2])

private theorem quadratic_expansion (p : Polynomial ℚ) (hp : p.natDegree = 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have h := p.as_sum_range_C_mul_X_pow
  rw [hp] at h
  simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using h

private theorem quadratic_aeval (p : Polynomial ℚ) (hp : p.natDegree = 2) (y : ℝ) :
    aeval y p = (p.coeff 2 : ℝ) * y ^ 2 + (p.coeff 1 : ℝ) * y + (p.coeff 0 : ℝ) := by
  conv_lhs => rw [quadratic_expansion p hp]
  simp

private theorem minpoly_coeff_two (x : ℝ) (hx : QuadraticIrrational x) :
    (minpoly ℚ x).coeff 2 = 1 := by
  rw [← hx.2]
  exact (minpoly.monic hx.1.isIntegral).coeff_natDegree

private theorem minpoly_quadratic_equation (x : ℝ) (hx : QuadraticIrrational x) :
    x ^ 2 + ((minpoly ℚ x).coeff 1 : ℝ) * x + ((minpoly ℚ x).coeff 0 : ℝ) = 0 := by
  have h := minpoly.aeval ℚ x
  rw [quadratic_aeval _ hx.2, minpoly_coeff_two x hx] at h
  simpa using h

theorem quadratic_other_root : QuadraticOtherRoot := by
  intro x hx
  have hi := quadratic_is_irrational x hx
  have hc : Irrational (quadraticConjugate x) := by
    simpa [P203Specs.quadraticConjugate] using
      hi.ratCast_sub (-((minpoly ℚ x).coeff 1))
  refine ⟨hc, ?_, ?_⟩
  · intro heq
    have hrat : x = ((-((minpoly ℚ x).coeff 1) / 2 : ℚ) : ℝ) := by
      dsimp [P203Specs.quadraticConjugate] at heq
      push_cast
      linarith
    exact hi.ne_rat _ hrat
  · intro y
    rw [quadratic_aeval _ hx.2, minpoly_coeff_two x hx]
    simp only [Rat.cast_one, one_mul]
    have he := minpoly_quadratic_equation x hx
    have hfactor : y ^ 2 + ((minpoly ℚ x).coeff 1 : ℝ) * y +
        ((minpoly ℚ x).coeff 0 : ℝ) = (y - x) * (y - quadraticConjugate x) := by
      change y ^ 2 + ((minpoly ℚ x).coeff 1 : ℝ) * y +
        ((minpoly ℚ x).coeff 0 : ℝ) =
        (y - x) * (y - (-((minpoly ℚ x).coeff 1 : ℝ) - x))
      nlinarith [he]
    rw [hfactor, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem conjugate_independent : ConjugateIndependent := by
  intro x hx p hp hpx
  have heq := minpoly.Irreducible.eq_minpoly hp hpx
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.ne_zero
  have hd : p.natDegree = 2 := by
    rw [heq, natDegree_C_mul hlc, hx.2]
  have hc1 : p.coeff 1 = p.leadingCoeff * (minpoly ℚ x).coeff 1 := by
    conv_lhs => rw [heq, coeff_C_mul]
  have hc2 : p.coeff 2 = p.leadingCoeff := by
    conv_lhs => rw [heq, coeff_C_mul, minpoly_coeff_two x hx, mul_one]
  refine ⟨hd, ?_, ?_⟩
  · dsimp [P203Specs.quadraticConjugate]
    rw [hc1, hc2, Rat.cast_mul, mul_div_cancel_left₀ _ (Rat.cast_ne_zero.mpr hlc)]
  · intro y
    rw [heq, aeval_mul, aeval_C]
    rw [mul_eq_zero]
    have hn : algebraMap ℚ ℝ p.leadingCoeff ≠ 0 :=
      by simpa only [map_zero] using (algebraMap ℚ ℝ).injective.ne hlc
    rw [or_iff_right hn]
    exact (quadratic_other_root x hx).2.2 y

theorem conjugate_quadratic : ConjugateQuadratic := by
  intro x hx
  have hr : aeval (quadraticConjugate x) (minpoly ℚ x) = 0 :=
    ((quadratic_other_root x hx).2.2 _).mpr (Or.inr rfl)
  have heq : minpoly ℚ (quadraticConjugate x) = minpoly ℚ x :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx.1.isIntegral) hr
      (minpoly.monic hx.1.isIntegral)).symm
  refine ⟨⟨?_, heq ▸ hx.2⟩, heq, ?_⟩
  · exact ⟨minpoly ℚ x, minpoly.ne_zero hx.1.isIntegral, hr⟩
  · change -((minpoly ℚ (quadraticConjugate x)).coeff 1 : ℝ) - quadraticConjugate x = x
    rw [heq]
    change -((minpoly ℚ x).coeff 1 : ℝ) - (-((minpoly ℚ x).coeff 1 : ℝ) - x) = x
    ring

theorem step_irrational : StepIrrational := by
  intro x hx
  simpa only [P203Specs.continuedFractionStep, one_div] using (hx.sub_intCast ⌊x⌋).inv

theorem quotient_iterates : QuotientIterates := by
  intro x hx n
  have h : ∀ n : ℕ, Irrational (continuedFractionStep^[n] x) ∧
      P203Specs.completeQuotient x n = some (continuedFractionStep^[n] x) := by
    intro n
    induction n with
    | zero => exact ⟨hx, (algorithm_initial x).1⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨step_irrational _ ih.1, ?_⟩
      rw [algorithm_step, ih.2, Option.bind_some, ite_eq_right (ih.1.ne_int _)]
      rfl
  refine ⟨(h n).1, (h n).2, ?_⟩
  rw [algorithm_digits, (h n).2]
  rfl

theorem infinite_digits_iff : InfiniteDigitsIff := by
  intro x
  constructor
  · rintro ⟨a, ha⟩ ⟨q, hq⟩
    have ht : (GenContFract.of x).Terminates :=
      (GenContFract.terminates_iff_rat x).mpr ⟨q, hq.symm⟩
    obtain ⟨j, hj⟩ := ht
    have hc : P203Specs.completeQuotient x (j + 1) = none :=
      (standard_termination_bridge x j).mp hj
    have hd := ha (j + 1)
    rw [algorithm_digits, hc] at hd
    cases hd
  · intro hx
    exact ⟨fun n => ⌊continuedFractionStep^[n] x⌋, fun n => (quotient_iterates x hx n).2.2⟩

theorem digit_sequence_unique : DigitSequenceUnique := by
  intro x a b ha hb
  funext n
  exact Option.some.inj ((ha n).symm.trans (hb n))

theorem eventual_periodicity_bridge : EventualPeriodicityBridge := by
  intro x
  constructor
  · rintro ⟨a, ha, m, r, hr, hper⟩
    refine ⟨(infinite_digits_iff x).mp ⟨a, ha⟩, m, r, hr, ?_⟩
    intro n hn
    rw [ha, ha, hper n hn]
  · rintro ⟨hx, m, r, hr, hper⟩
    obtain ⟨a, ha⟩ := (infinite_digits_iff x).mpr hx
    refine ⟨a, ha, m, r, hr, ?_⟩
    intro n hn
    apply Option.some.inj
    rw [← ha, ← ha]
    exact hper n hn

theorem pure_periodicity_bridge : PurePeriodicityBridge := by
  intro x
  constructor
  · rintro ⟨a, ha, r, hr, hper⟩
    refine ⟨(infinite_digits_iff x).mp ⟨a, ha⟩, r, hr, ?_⟩
    intro n
    rw [ha, ha, hper n]
  · rintro ⟨hx, r, hr, hper⟩
    obtain ⟨a, ha⟩ := (infinite_digits_iff x).mpr hx
    refine ⟨a, ha, r, hr, ?_⟩
    intro n
    apply Option.some.inj
    rw [← ha, ← ha]
    exact hper n

theorem pure_is_eventual : PureIsEventual := by
  rintro x ⟨a, ha, r, hr, hper⟩
  exact ⟨a, ha, 0, r, hr, fun n _ => hper n⟩

end P203
