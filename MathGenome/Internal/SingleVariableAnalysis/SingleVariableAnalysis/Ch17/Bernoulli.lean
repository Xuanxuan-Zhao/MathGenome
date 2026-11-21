import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.Bernoulli
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond

/-!
K03.17.bernoulli: the real Bernoulli polynomials and their normalization.
The canonical rational polynomial formula is transported to ℝ. Its derivative
and endpoint formulas give zero proper Darboux average by Newton–Leibniz.
The difference of two solutions is constant; the zero average fixes that
constant. This proves stepwise and whole-sequence uniqueness.
-/
noncomputable section
namespace SingleVariableAnalysis
open Polynomial Set
open scoped BigOperators
namespace BernoulliSpec
export Specs.SingleVariableAnalysis.Ch17.Bernoulli
  (bernoulliPolynomialValue bernoulliNumberValue normalizedStep bernoulliRecursionValue)
end BernoulliSpec

/-- Real Bernoulli polynomials, with the negative first Bernoulli number. -/
abbrev bernoulliPolynomial := BernoulliSpec.bernoulliPolynomialValue
/-- Bernoulli numbers are the constant terms of these real polynomials. -/
abbrev bernoulliNumber := BernoulliSpec.bernoulliNumberValue
abbrev BernoulliRecursion := BernoulliSpec.bernoulliRecursionValue

namespace Bernoulli
open Riemann

/-- A continuous real function on the unit interval has a proper Darboux integral.
This local bridge proves integrability from the closed-cell oscillation criterion. -/
theorem continuous_unit_integrable {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 1)) :
    RealIntegrable f 0 1 := by
  have hb : BoundedOnInterval f 0 1 :=
    ⟨(isCompact_Icc.image_of_continuousOn hc).bddBelow,
      (isCompact_Icc.image_of_continuousOn hc).bddAbove⟩
  apply (darboux_criterion f zero_lt_one hb).mpr
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) (ε / 2) (half_pos hε)
  obtain ⟨P, _, hP⟩ := arbitrarily_fine zero_lt_one δ hδ
  have hosc (i : Fin P.n) : cellSupremum f P hb i - cellInfimum f P hb i ≤ ε / 2 := by
    have hci : ContinuousOn f (cell P i) := hc.mono (cell_subset_interval P i)
    obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (cell_nonempty P i) hci
    obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn (cell_nonempty P i) hci
    have hsup : cellSupremum f P hb i = f x := by
      apply le_antisymm
      · apply (cell_bounds f P hb i).2.2
        rintro _ ⟨z, hz, rfl⟩
        exact hmax hz
      · exact le_cellSupremum f P hb i hx
    have hinf : cellInfimum f P hb i = f y := by
      apply le_antisymm
      · exact cellInfimum_le f P hb i hy
      · apply (cell_bounds f P hb i).1.2
        rintro _ ⟨z, hz, rfl⟩
        exact hmin hz
    have hdist : dist x y < δ := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt _ ((cellLength_le_mesh P i).trans_lt hP)
      change |x - y| ≤ P.point i.succ - P.point i.castSucc
      exact abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
    have hlt := hclose x (cell_subset_interval P i hx) y (cell_subset_interval P i hy) hdist
    rw [Real.dist_eq] at hlt
    rw [hsup, hinf]
    exact (le_abs_self _).trans hlt.le
  refine ⟨P, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (hosc i) (cell_positive P i).le)
  simpa only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_cellLength,
    sub_zero, mul_one, upperSum, lowerSum, D.upperSumValue, D.lowerSumValue] using hs

theorem polynomial_unit_integrable (p : Polynomial ℝ) : RealIntegrable p.eval 0 1 :=
  continuous_unit_integrable p.differentiable.continuous.continuousOn

end Bernoulli

theorem bernoulli_step_iff_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.normalizedStepIffHasDerivAt := by
  intro p q n
  constructor
  · rintro ⟨hd, ha⟩
    refine ⟨fun x => ?_, ha⟩
    simpa only [hd, Polynomial.eval_mul, Polynomial.eval_C] using p.hasDerivAt x
  · rintro ⟨hd, ha⟩
    refine ⟨Polynomial.funext (fun x => ?_), ha⟩
    simpa only [Polynomial.eval_mul, Polynomial.eval_C] using
      (p.hasDerivAt x).unique (hd x)

theorem bernoulli_zero : bernoulliPolynomial 0 = 1 := by
  simp [bernoulliPolynomial, BernoulliSpec.bernoulliPolynomialValue]

theorem bernoulli_derivative :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliDerivative := by
  intro n
  change derivative ((Polynomial.bernoulli (n + 1)).map (algebraMap ℚ ℝ)) = _
  rw [Polynomial.derivative_map, Polynomial.derivative_bernoulli_add_one, Polynomial.map_mul]
  simp [BernoulliSpec.bernoulliPolynomialValue]

theorem bernoulli_hasDerivAt :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliHasDerivAt := by
  intro n x
  have h := (bernoulliPolynomial (n + 1)).hasDerivAt x
  rw [bernoulli_derivative] at h
  simpa using h

namespace Bernoulli
open Riemann

/-- For positive index, an antiderivative has equal values at 0 and 1.
This follows from the actual two Bernoulli-number conventions in Mathlib. -/
private theorem primitive_endpoints (n : ℕ) :
    (bernoulliPolynomial (n + 2)).eval 1 = (bernoulliPolynomial (n + 2)).eval 0 := by
  change ((Polynomial.bernoulli (n + 2)).map (algebraMap ℚ ℝ)).eval 1 =
    ((Polynomial.bernoulli (n + 2)).map (algebraMap ℚ ℝ)).eval 0
  have h := _root_.bernoulli_eq_bernoulli'_of_ne_one (show n + 2 ≠ 1 by omega)
  have he := congrArg (algebraMap ℚ ℝ) h
  have h1 := Polynomial.eval_map_apply (p := Polynomial.bernoulli (n + 2))
    (f := algebraMap ℚ ℝ) (1 : ℚ)
  have h0 := Polynomial.eval_map_apply (p := Polynomial.bernoulli (n + 2))
    (f := algebraMap ℚ ℝ) (0 : ℚ)
  simp only [map_one, Polynomial.bernoulli_eval_one] at h1
  simp only [map_zero, Polynomial.bernoulli_eval_zero] at h0
  exact h1.trans (he.symm.trans h0.symm)

end Bernoulli

theorem bernoulli_zero_average :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliZeroAverage := by
  intro n
  let h := Bernoulli.polynomial_unit_integrable (bernoulliPolynomial (n + 1))
  refine ⟨h, ?_⟩
  have hd (x : ℝ) : HasDerivAt
      (fun t => (bernoulliPolynomial (n + 2)).eval t / ((n : ℝ) + 2))
      ((bernoulliPolynomial (n + 1)).eval x) x := by
    have H := (bernoulli_hasDerivAt (n + 1) x).div_const ((n : ℝ) + 2)
    convert H using 1
    push_cast
    field_simp
    ring
  have H := Riemann.real_ftc_second
    (fun t => (bernoulliPolynomial (n + 2)).eval t / ((n : ℝ) + 2))
    (bernoulliPolynomial (n + 1)).eval 0 1 zero_le_one
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x) h
  rw [Bernoulli.primitive_endpoints n, sub_self] at H
  exact H

namespace Bernoulli
open Riemann

/-- Equal polynomial derivatives leave one constant, fixed by the unit average. -/
theorem polynomial_unique_of_derivative_average (p q : Polynomial ℝ)
    (hd : derivative p = derivative q)
    (hp : ∃ h : RealIntegrable p.eval 0 1, realIntegral p.eval h = 0)
    (hq : ∃ h : RealIntegrable q.eval 0 1, realIntegral q.eval h = 0) : p = q := by
  obtain ⟨hp, hpv⟩ := hp
  obtain ⟨hq, hqv⟩ := hq
  let c : ℝ := (p - q).coeff 0
  have he : p - q = C c := Polynomial.eq_C_of_derivative_eq_zero
    (by rw [Polynomial.derivative_sub, hd, sub_self])
  have hev : p.eval = fun x => q.eval x + c := by
    funext x
    have hh := congrArg (fun r : Polynomial ℝ => r.eval x) he
    simp only [Polynomial.eval_sub, Polynomial.eval_C] at hh
    linarith
  let hc := continuous_unit_integrable (f := fun _ => c) continuousOn_const
  have hcv : realIntegral (fun _ => c) hc = c := by
    have H := real_ftc_second (fun x => c * x) (fun _ => c) 0 1 zero_le_one
      (by fun_prop) (fun x _ => by simpa using (hasDerivAt_id x).const_mul c) hc
    simpa using H
  obtain ⟨hs, hvs⟩ := real_add_value hq hc
  have hv : realIntegral p.eval hp = realIntegral q.eval hq + c := by
    simpa only [← hev, hcv] using hvs
  have hc0 : c = 0 := by rw [hpv, hqv] at hv; linarith
  exact sub_eq_zero.mp (by simpa only [hc0, Polynomial.C_0] using he)

end Bernoulli

theorem bernoulli_step_unique :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliStepUnique := by
  intro n
  refine ⟨bernoulliPolynomial (n + 1), ⟨bernoulli_derivative n, bernoulli_zero_average n⟩, ?_⟩
  intro p hp
  exact Bernoulli.polynomial_unique_of_derivative_average p (bernoulliPolynomial (n + 1))
    (hp.1.trans (bernoulli_derivative n).symm) hp.2 (bernoulli_zero_average n)

theorem bernoulli_normalization :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliNormalization :=
  ⟨bernoulli_zero, fun n => ⟨bernoulli_derivative n, bernoulli_zero_average n⟩⟩

theorem bernoulli_unique_sequence :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliUniqueSequence := by
  refine ⟨bernoulliPolynomial, bernoulli_normalization, ?_⟩
  intro B hB
  funext n
  induction n with
  | zero => exact hB.1.trans bernoulli_zero.symm
  | succ n ih =>
    have hp := hB.2 n
    rw [ih] at hp
    exact (bernoulli_step_unique n).unique hp (bernoulli_normalization.2 n)

theorem bernoulli_number_canonical :
    Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliNumberCanonical := by
  intro n
  have H := Polynomial.eval_map_apply (p := Polynomial.bernoulli n)
    (f := algebraMap ℚ ℝ) (0 : ℚ)
  change ((Polynomial.bernoulli n).map (algebraMap ℚ ℝ)).eval 0 = _
  simpa only [map_zero, Polynomial.bernoulli_eval_zero] using H

theorem bernoulli_one : Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliOne := by
  change (Polynomial.bernoulli 1).map (algebraMap ℚ ℝ) = _
  simp [Polynomial.bernoulli_one]

theorem bernoulli_two : Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliTwo := by
  have h : Polynomial.bernoulli 2 = (X ^ 2 - X + C (1 / 6) : Polynomial ℚ) := by
    norm_num [Polynomial.bernoulli, Finset.sum_range_succ,
      ← Polynomial.C_mul_X_pow_eq_monomial]
    have hh : (C (1 / 2 : ℚ) : Polynomial ℚ) * 2 = 1 := by
      rw [← Polynomial.C_ofNat, ← Polynomial.C_mul]
      norm_num
    rw [hh, one_mul]
    ring
  change (Polynomial.bernoulli 2).map (algebraMap ℚ ℝ) = _
  rw [h]
  norm_num

theorem bernoulli_four : Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliFour := by
  have h : Polynomial.bernoulli 4 =
      (X ^ 4 - C 2 * X ^ 3 + X ^ 2 - C (1 / 30) : Polynomial ℚ) := by
    norm_num [Polynomial.bernoulli, Finset.sum_range_succ,
      ← Polynomial.C_mul_X_pow_eq_monomial, _root_.bernoulli, _root_.bernoulli'_four,
      show Nat.choose 4 2 = 6 from rfl]
    have hh : (C (1 / 2 : ℚ) : Polynomial ℚ) * 4 = C 2 := by
      rw [← Polynomial.C_ofNat, ← Polynomial.C_mul]
      norm_num
    have hs : (C (1 / 6 : ℚ) : Polynomial ℚ) * 6 = 1 := by
      rw [← Polynomial.C_ofNat, ← Polynomial.C_mul]
      norm_num
    calc
      _ = (X ^ 2 * (C (1 / 6) * 6) - X ^ 3 * (C (1 / 2) * 4) + X ^ 4 - C (1 / 30) : Polynomial ℚ) := by ring
      _ = _ := by rw [hh, hs, mul_one]; ring
  change (Polynomial.bernoulli 4).map (algebraMap ℚ ℝ) = _
  rw [h]
  norm_num

theorem bernoulli_numbers : Specs.SingleVariableAnalysis.Ch17.Bernoulli.bernoulliNumbers := by
  change bernoulliNumber 0 = 1 ∧ bernoulliNumber 1 = -1 / 2 ∧
    bernoulliNumber 2 = 1 / 6 ∧ bernoulliNumber 4 = -1 / 30
  simp only [bernoulliNumber, BernoulliSpec.bernoulliNumberValue]
  change (bernoulliPolynomial 0).eval 0 = 1 ∧ (bernoulliPolynomial 1).eval 0 = -1 / 2 ∧
    (bernoulliPolynomial 2).eval 0 = 1 / 6 ∧ (bernoulliPolynomial 4).eval 0 = -1 / 30
  have h1 : bernoulliPolynomial 1 = X - C (1 / 2) := bernoulli_one
  have h2 : bernoulliPolynomial 2 = X ^ 2 - X + C (1 / 6) := bernoulli_two
  have h4 : bernoulliPolynomial 4 = X ^ 4 - C 2 * X ^ 3 + X ^ 2 - C (1 / 30) :=
    bernoulli_four
  rw [bernoulli_zero, h1, h2, h4]
  norm_num

end SingleVariableAnalysis
