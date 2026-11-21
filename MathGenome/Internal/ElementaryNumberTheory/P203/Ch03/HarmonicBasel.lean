import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.HarmonicBasel
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Filter
open scoped Topology Asymptotics BigOperators
open P203Specs.Ch03

namespace P203.Ch03.HarmonicBasel

/-- Bridge the positive-index real sum to Mathlib's rational harmonic number. -/
theorem harmonic_eq_mathlib (m : ℕ) : harmonicNumber m = (harmonic m : ℝ) := by
  simp [harmonicNumber, harmonic_eq_sum_Icc, Rat.cast_sum, one_div]

theorem gamma_eq : P203Specs.Ch03.HarmonicBasel.GammaIdentification := rfl

theorem harmonic_limit : P203Specs.Ch03.HarmonicBasel.HarmonicLimit := by
  unfold P203Specs.Ch03.HarmonicBasel.HarmonicLimit
  simpa only [harmonic_eq_mathlib, gamma] using Real.tendsto_harmonic_sub_log

theorem harmonic_limit_exists : P203Specs.Ch03.HarmonicBasel.HarmonicLimitExists :=
  ⟨gamma, harmonic_limit⟩

/-- Sandwich gamma between the two harmonic-log sequences, then use log x ≤ x-1. -/
theorem harmonic_error_bound : P203Specs.Ch03.HarmonicBasel.HarmonicErrorBound := by
  intro m hm
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant m
  have hhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq',
    ite_eq_right (Nat.ne_of_gt hm)] at hlo hhi
  have hnonneg : 0 ≤ harmonicNumber m - Real.log (m : ℝ) - gamma := by
    rw [harmonic_eq_mathlib, gamma]
    linarith
  refine ⟨hnonneg, ?_⟩
  rw [abs_of_nonneg hnonneg, harmonic_eq_mathlib, gamma]
  have hlog : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
    rw [← Real.log_div (by positivity) (ne_of_gt hmR)]
    calc
      Real.log (((m : ℝ) + 1) / m) ≤ ((m : ℝ) + 1) / m - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (m : ℝ) := by field_simp; ring
  linarith

theorem harmonic_asymptotic : P203Specs.Ch03.HarmonicBasel.HarmonicAsymptotic := by
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with m hm
  have h := (harmonic_error_bound m hm).2
  simpa only [Real.norm_eq_abs, one_mul, sub_add_eq_sub_sub,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ))] using h

theorem basel_hasSum : P203Specs.Ch03.HarmonicBasel.BaselHasSum := by
  unfold P203Specs.Ch03.HarmonicBasel.BaselHasSum
  apply (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2
  simpa using hasSum_zeta_two

theorem basel_summable : P203Specs.Ch03.HarmonicBasel.BaselSummable :=
  basel_hasSum.summable

end P203.Ch03.HarmonicBasel
