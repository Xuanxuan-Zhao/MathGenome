import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.Convergents
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.ContinuedFractionAlgorithm
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace P203
open P203Specs GenContFract

noncomputable abbrev integerContinuants : IntegerContinuantsType := P203Specs.integerContinuants
noncomputable abbrev convergentNumerator : ConvergentNumeratorType := P203Specs.convergentNumerator
noncomputable abbrev convergentDenominator : ConvergentDenominatorType := P203Specs.convergentDenominator

private theorem numerator_nat (x : ℝ) (n : ℕ) :
    P203Specs.convergentNumerator x n = (P203Specs.integerContinuants x (n + 1)).a := by
  unfold P203Specs.convergentNumerator
  rw [ite_eq_right (show (n : ℤ) ≠ -2 by omega),
    show ((n : ℤ) + 1).toNat = n + 1 by omega]

private theorem denominator_nat (x : ℝ) (n : ℕ) :
    P203Specs.convergentDenominator x n = (P203Specs.integerContinuants x (n + 1)).b := by
  unfold P203Specs.convergentDenominator
  rw [ite_eq_right (show (n : ℤ) ≠ -2 by omega),
    show ((n : ℤ) + 1).toNat = n + 1 by omega]

private theorem numerator_prev (x : ℝ) (n : ℕ) :
    P203Specs.convergentNumerator x ((n : ℤ) - 1) = (P203Specs.integerContinuants x n).a := by
  simp [P203Specs.convergentNumerator, show (n : ℤ) - 1 ≠ -2 by omega]

private theorem denominator_prev (x : ℝ) (n : ℕ) :
    P203Specs.convergentDenominator x ((n : ℤ) - 1) = (P203Specs.integerContinuants x n).b := by
  simp [P203Specs.convergentDenominator, show (n : ℤ) - 1 ≠ -2 by omega]

theorem convergent_initial : ConvergentInitial := by
  intro x
  norm_num [P203Specs.convergentNumerator, P203Specs.convergentDenominator,
    P203Specs.integerContinuants]

/-- Exact identification of the integer auxiliary pairs, including Mathlib's
constant extension beyond termination. -/
theorem integerContinuants_cast (x : ℝ) (n : ℕ) :
    ((P203Specs.integerContinuants x n).a : ℝ) = ((GenContFract.of x).contsAux n).a ∧
    ((P203Specs.integerContinuants x n).b : ℝ) = ((GenContFract.of x).contsAux n).b := by
  induction n using Nat.twoStepInduction with
  | zero => simp [P203Specs.integerContinuants, GenContFract.contsAux]
  | one => simp [P203Specs.integerContinuants, GenContFract.contsAux, of_h_eq_floor]
  | more n ih ih' =>
    have hs := (standard_continuedFraction_bridge x).2 n
    change (GenContFract.of x).s.get? n = _ at hs
    cases hd : P203Specs.partialQuotient x (n + 1) with
    | none =>
      simp only [hd, Option.map_none] at hs
      simpa only [P203Specs.integerContinuants, hd, GenContFract.contsAux, hs] using ih'
    | some a =>
      simp only [hd, Option.map_some] at hs
      simp only [P203Specs.integerContinuants, hd, GenContFract.contsAux, hs,
        GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
        Int.cast_add, Int.cast_mul, one_mul, ih.1, ih.2, ih'.1, ih'.2, and_self]

theorem convergent_mathlib_bridge : ConvergentMathlibBridge := by
  intro x n
  have hp : (P203Specs.convergentNumerator x n : ℝ) = (GenContFract.of x).nums n := by
    rw [numerator_nat]
    exact (integerContinuants_cast x (n + 1)).1
  have hq : (P203Specs.convergentDenominator x n : ℝ) = (GenContFract.of x).dens n := by
    rw [denominator_nat]
    exact (integerContinuants_cast x (n + 1)).2
  refine ⟨hp, hq, ?_, ?_⟩
  · exact congrArg₂ (· / ·) hp hq
  · rw [hp, hq, ← GenContFract.conv_eq_num_div_den, Real.convs_eq_convergent]

/-- An earlier digit exists whenever a later digit does. -/
private theorem digit_defined_before {x : ℝ} {j n : ℕ} (hj : j ≤ n)
    (hn : P203Specs.partialQuotient x n ≠ none) : P203Specs.partialQuotient x j ≠ none := by
  intro h
  have hc : P203Specs.completeQuotient x j = none := by
    simpa only [P203Specs.completeQuotient, P203Specs.partialQuotient,
      Option.map_eq_none_iff] using h
  have hcn := algorithm_no_restart x j (n - j) hc
  rw [Nat.add_sub_of_le hj] at hcn
  apply hn
  simpa only [P203Specs.completeQuotient, P203Specs.partialQuotient,
    Option.map_eq_none_iff] using hcn

theorem convergent_recurrences : ConvergentRecurrences := by
  intro x n a ha
  rcases n with _ | _ | n
  · have h : ⌊x⌋ = a := Option.some.inj ((algorithm_initial x).2.symm.trans ha)
    simp [P203Specs.convergentNumerator, P203Specs.convergentDenominator,
      P203Specs.integerContinuants, ← h]
  · simp [P203Specs.convergentNumerator, P203Specs.convergentDenominator,
      P203Specs.integerContinuants, ha]
  · have h1 : (((n + 2 : ℕ) : ℤ) - 1) = ((n + 1 : ℕ) : ℤ) := by omega
    have h2 : (((n + 2 : ℕ) : ℤ) - 2) = (n : ℤ) := by omega
    simp only [h1, h2, numerator_nat, denominator_nat]
    simp only [P203Specs.integerContinuants, ha]
    trivial

private theorem integer_determinant (x : ℝ) (n : ℕ)
    (hn : P203Specs.partialQuotient x n ≠ none) :
    (P203Specs.integerContinuants x (n + 1)).a * (P203Specs.integerContinuants x n).b -
      (P203Specs.integerContinuants x n).a * (P203Specs.integerContinuants x (n + 1)).b =
        (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero => simp [P203Specs.integerContinuants]
  | succ n ih =>
    have hprev := digit_defined_before (Nat.le_succ n) hn
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hn
    have hi := ih hprev
    change (P203Specs.integerContinuants x (n + 2)).a * (P203Specs.integerContinuants x (n + 1)).b -
      (P203Specs.integerContinuants x (n + 1)).a * (P203Specs.integerContinuants x (n + 2)).b = _
    rw [P203Specs.integerContinuants, ha]
    rw [pow_succ, ← hi]
    ring

theorem convergent_determinant : ConvergentDeterminant := by
  intro x n hn
  simpa only [numerator_nat, denominator_nat, numerator_prev, denominator_prev] using
    integer_determinant x n hn

/-- Positivity also holds for the constant auxiliary extension after termination. -/
theorem convergent_denominator_pos (x : ℝ) (n : ℕ) :
    0 < P203Specs.convergentDenominator x n := by
  have hm : Monotone (GenContFract.of x).dens :=
    monotone_nat_of_le_succ (fun _ => GenContFract.of_den_mono)
  have h : (1 : ℝ) ≤ (GenContFract.of x).dens n := by
    simpa only [GenContFract.zeroth_den_eq_one] using hm (Nat.zero_le n)
  change (1 : ℝ) ≤ (P203Specs.simpleContinuedFraction x).dens n at h
  rw [← (convergent_mathlib_bridge x n).2.1] at h
  have : (1 : ℤ) ≤ P203Specs.convergentDenominator x n := by exact_mod_cast h
  omega

theorem convergent_reduced : ConvergentReduced := by
  intro x n hn
  refine ⟨convergent_denominator_pos x n, ?_⟩
  have hdet := convergent_determinant x n hn
  have hd : (Int.gcd (P203Specs.convergentNumerator x n)
      (P203Specs.convergentDenominator x n) : ℤ) ∣ (-1 : ℤ) ^ (n + 1) := by
    rw [← hdet]
    exact dvd_sub
      (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) _)
  have habs := Int.natAbs_dvd_natAbs.mpr hd
  simpa only [Int.natAbs_natCast, Int.natAbs_pow, Int.natAbs_neg,
    Int.natAbs_one, one_pow, Nat.dvd_one] using habs

theorem convergent_denominator_growth : ConvergentDenominatorGrowth := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    norm_num [P203Specs.convergentDenominator, P203Specs.integerContinuants]
  · intro x a ha
    norm_num [P203Specs.convergentDenominator, P203Specs.integerContinuants, ha]
  · intro x n hn hd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hd
    have hrec := (convergent_recurrences x (k + 1 + 1) a ha).2
    have hpos := convergent_denominator_pos x (k + 1)
    have hprev := convergent_denominator_pos x k
    have hapos := later_partialQuotients x a (k + 1 + 1) (by omega) ha
    rw [show ((k + 1 + 1 : ℕ) : ℤ) - 1 = ((k + 1 : ℕ) : ℤ) by omega,
      show ((k + 1 + 1 : ℕ) : ℤ) - 2 = (k : ℤ) by omega] at hrec
    norm_num only [Nat.cast_add, Nat.cast_succ, Nat.cast_one] at hrec hpos hprev ⊢
    nlinarith [mul_le_mul_of_nonneg_right hapos hpos.le]

/-- Nested finite evaluation of a specified sequence prefix. -/
private theorem finite_prefix_eval (s : Stream'.Seq (GenContFract.Pair ℝ))
    (a : ℤ) (t : List ℤ)
    (ht : ∀ (j : ℕ) (b : ℤ), t[j]? = some b → s.get? j = some ⟨1, (b : ℝ)⟩) :
    (a : ℝ) + GenContFract.convs'Aux s t.length = P203Specs.finiteContinuedFraction a t := by
  induction t generalizing s a with
  | nil => simp [P203Specs.finiteContinuedFraction]
  | cons b t ih =>
    have hh : s.head = some ⟨1, (b : ℝ)⟩ := ht 0 b rfl
    have htail : ∀ (j : ℕ) (c : ℤ), t[j]? = some c →
        s.tail.get? j = some ⟨1, (c : ℝ)⟩ := by
      intro j c hc
      rw [Stream'.Seq.get?_tail]
      exact ht (j + 1) c hc
    simp only [List.length_cons, GenContFract.convs'Aux, hh]
    rw [ih s.tail b htail]
    rfl

private theorem finite_eval_of_digits (x : ℝ) (a : ℤ) (t : List ℤ)
    (hd : ∀ j ≤ t.length, P203Specs.partialQuotient x j = (a :: t)[j]?) :
    (GenContFract.of x).convs t.length = P203Specs.finiteContinuedFraction a t := by
  rw [GenContFract.of_convs_eq_convs']
  change (GenContFract.of x).h + GenContFract.convs'Aux (GenContFract.of x).s t.length = _
  have ha : ⌊x⌋ = a := by
    have h := hd 0 (Nat.zero_le _)
    rw [(algorithm_initial x).2] at h
    exact Option.some.inj h
  rw [GenContFract.of_h_eq_floor, ha]
  apply finite_prefix_eval
  intro j b hb
  have hj : j < t.length := (List.getElem?_eq_some_iff.mp hb).1
  have hpart : P203Specs.partialQuotient x (j + 1) = some b := by
    simpa only [List.getElem?_cons_succ] using (hd (j + 1) (by omega)).trans hb
  have hs := (standard_continuedFraction_bridge x).2 j
  simpa only [P203Specs.simpleContinuedFraction, hpart, Option.map_some] using hs

theorem convergent_finite_evaluation : ConvergentFiniteEvaluation := by
  intro x n hn
  let t := List.ofFn (fun j : Fin n => (P203Specs.partialQuotient x (j.val + 1)).getD 0)
  have hl : t.length = n := List.length_ofFn
  have hd : ∀ j ≤ n, P203Specs.partialQuotient x j = (⌊x⌋ :: t)[j]? := by
    intro j hj
    cases j with
    | zero => exact (algorithm_initial x).2
    | succ j =>
      have hj' : j < n := by omega
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (digit_defined_before hj hn)
      simp only [List.getElem?_cons_succ, t, List.getElem?_ofFn, dite_eq_left hj', hb,
        Option.getD_some]
  refine ⟨⌊x⌋, t, hl, hd, ?_⟩
  have he := finite_eval_of_digits x ⌊x⌋ t (by simpa only [hl] using hd)
  rw [hl] at he
  exact (convergent_mathlib_bridge x n).2.2.1.trans he

/-- Irrationality guarantees that every complete quotient is present. -/
theorem irrational_completeQuotient_defined (x : ℝ) (hx : Irrational x) (n : ℕ) :
    ∃ α : ℝ, P203Specs.completeQuotient x n = some α := by
  cases n with
  | zero => exact ⟨x, (algorithm_initial x).1⟩
  | succ n =>
    apply Option.ne_none_iff_exists'.mp
    intro hn
    have ht : (GenContFract.of x).Terminates :=
      ⟨n, (standard_termination_bridge x n).mpr hn⟩
    obtain ⟨q, hq⟩ := (GenContFract.terminates_iff_rat x).mp ht
    exact hx ⟨q, hq.symm⟩

private theorem irrational_digit_defined (x : ℝ) (hx : Irrational x) (n : ℕ) :
    P203Specs.partialQuotient x n ≠ none := by
  obtain ⟨α, hα⟩ := irrational_completeQuotient_defined x hx n
  rw [algorithm_digits, hα]
  simp

private theorem fractional_error (p q pp qp α y : ℝ) (n : ℕ)
    (hd : q * α + qp ≠ 0) (hy : y = (p * α + pp) / (q * α + qp))
    (hdet : p * qp - pp * q = (-1 : ℝ) ^ (n + 1)) :
    q * y - p = (-1 : ℝ) ^ n / (q * α + qp) := by
  rw [hy]
  field_simp [hd]
  nlinarith [pow_succ (-1 : ℝ) n]

theorem convergent_exact_tail : ConvergentExactTail := by
  intro x hx n
  obtain ⟨β, hβ⟩ := irrational_completeQuotient_defined x hx n
  obtain ⟨α, hα⟩ := irrational_completeQuotient_defined x hx (n + 1)
  have hβne : β ≠ (⌊β⌋ : ℝ) := by
    intro h
    have hn := (algorithm_stopping x β n hβ).mpr h
    rw [hα] at hn
    contradiction
  have hfr : Int.fract β ≠ 0 := by
    simpa only [Int.fract, sub_ne_zero] using hβne
  have hαval : (Int.fract β)⁻¹ = α := by
    have hs := algorithm_step x n
    rw [hβ, Option.bind_some, ite_eq_right hβne, hα] at hs
    simpa only [Int.fract, one_div] using (Option.some.inj hs).symm
  have hp : (P203Specs.convergentNumerator x n : ℝ) =
      ((GenContFract.of x).contsAux (n + 1)).a := by
    rw [numerator_nat]
    exact (integerContinuants_cast x (n + 1)).1
  have hq : (P203Specs.convergentDenominator x n : ℝ) =
      ((GenContFract.of x).contsAux (n + 1)).b := by
    rw [denominator_nat]
    exact (integerContinuants_cast x (n + 1)).2
  have hpp : (P203Specs.convergentNumerator x ((n : ℤ) - 1) : ℝ) =
      ((GenContFract.of x).contsAux n).a := by
    rw [numerator_prev]
    exact (integerContinuants_cast x n).1
  have hqp : (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ) =
      ((GenContFract.of x).contsAux n).b := by
    rw [denominator_prev]
    exact (integerContinuants_cast x n).2
  have hpos : 0 < (P203Specs.convergentDenominator x n : ℝ) * α +
      (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ) := by
    have hqpos : (0 : ℝ) < P203Specs.convergentDenominator x n := by
      exact_mod_cast convergent_denominator_pos x n
    have hαpos : 0 < α := lt_trans zero_lt_one
      (later_completeQuotients x α (n + 1) (by omega) hα)
    have hqprev : (0 : ℝ) ≤ P203Specs.convergentDenominator x ((n : ℤ) - 1) := by
      rw [hqp]
      exact GenContFract.zero_le_of_contsAux_b
    exact add_pos_of_pos_of_nonneg (mul_pos hqpos hαpos) hqprev
  have hval : x = ((P203Specs.convergentNumerator x n : ℝ) * α +
      (P203Specs.convergentNumerator x ((n : ℤ) - 1) : ℝ)) /
      ((P203Specs.convergentDenominator x n : ℝ) * α +
      (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ)) := by
    have hs := (completeQuotient_stream_bridge x β n).mp hβ
    have hv := GenContFract.compExactValue_correctness_of_stream_eq_some hs
    change x = GenContFract.compExactValue _ _ (Int.fract β) at hv
    rw [GenContFract.compExactValue, ite_eq_right hfr] at hv
    simpa only [GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
      one_mul, hαval, ← hp, ← hq, ← hpp, ← hqp, mul_comm] using hv
  refine ⟨α, hα, hpos, ne_of_gt hpos, hval, ?_⟩
  have hdet : (P203Specs.convergentNumerator x n : ℝ) *
      (P203Specs.convergentDenominator x ((n : ℤ) - 1) : ℝ) -
      (P203Specs.convergentNumerator x ((n : ℤ) - 1) : ℝ) *
      (P203Specs.convergentDenominator x n : ℝ) = (-1 : ℝ) ^ (n + 1) := by
    exact_mod_cast convergent_determinant x n (irrational_digit_defined x hx n)
  exact fractional_error _ _ _ _ α x n (ne_of_gt hpos) hval hdet

end P203
