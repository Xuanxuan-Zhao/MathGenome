import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
K03.04.noncontinuous_derivative. At zero the difference quotient is bounded
by |h|. Away from zero the ordinary product, reciprocal and sine chain rules
apply. Positive-index samples 1/(2πn) approach zero with derivative -1,
contradicting sequential continuity of the derivative, whose value at zero
is 0. We use the canonical Real.sin and Real.pi; the upstream SinCos and
PiPeriod goals identify the manuscript's series and analytic period with these.
-/
noncomputable section
namespace SingleVariableAnalysis.NoncontinuousDerivative

open scoped Topology
open Filter

def exampleFunction : ℝ → ℝ :=
  Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative.exampleFunctionValue

def samplePoint : ℕ → ℝ :=
  Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative.samplePointValue

theorem exampleFunction_eq (x : ℝ) : exampleFunction x = x ^ 2 * Real.sin (1 / x) := by
  by_cases hx : x = 0 <;>
    simp [exampleFunction,
      Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative.exampleFunctionValue, hx]

theorem hasDerivAt_zero : HasDerivAt exampleFunction 0 0 := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp
  apply (realDerivative_epsilon_iff _ _ _).mpr
  intro ε hε
  refine ⟨ε, hε, fun h hp hh => ?_⟩
  have hn : h ≠ 0 := abs_pos.mp hp
  have hq : (exampleFunction (0 + h) - exampleFunction 0) / h - 0 =
      h * Real.sin (1 / h) := by
    simp only [exampleFunction_eq, zero_add, zero_pow (by decide : 2 ≠ 0),
      zero_mul, sub_zero]
    field_simp
  rw [hq, abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg h) (Real.abs_sin_le_one _)).trans_lt hh

theorem hasDerivAt_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt exampleFunction
      (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
  have hi : HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa using (hasDerivAt_id x).fun_inv hx
  have hs := (Real.hasDerivAt_sin (1 / x)).comp x hi
  have hd := ((hasDerivAt_id x).pow 2).mul hs
  change HasDerivAt (fun y : ℝ => y ^ 2 * Real.sin (1 / y)) _ x at hd
  have he : (fun y : ℝ => y ^ 2 * Real.sin (1 / y)) = exampleFunction :=
    funext fun y => (exampleFunction_eq y).symm
  rw [he] at hd
  convert hd using 1
  dsimp
  field_simp
  ring

theorem differentiable : Differentiable ℝ exampleFunction := by
  intro x
  by_cases hx : x = 0
  · subst x; exact hasDerivAt_zero.differentiableAt
  · exact (hasDerivAt_of_ne_zero x hx).differentiableAt

theorem deriv_zero : deriv exampleFunction 0 = 0 := hasDerivAt_zero.deriv

theorem deriv_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    deriv exampleFunction x = 2 * x * Real.sin (1 / x) - Real.cos (1 / x) :=
  (hasDerivAt_of_ne_zero x hx).deriv

theorem samplePoint_pos (n : ℕ) (hn : 0 < n) : 0 < samplePoint n := by
  dsimp [samplePoint,
    Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative.samplePointValue]
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (Nat.cast_pos.mpr hn))

theorem samplePoint_tendsto : Tendsto samplePoint atTop (𝓝 (0 : ℝ)) := by
  have h := tendsto_const_div_atTop_nhds_zero_nat (1 / (2 * Real.pi))
  change Tendsto (fun n : ℕ => 1 / (2 * Real.pi * (n : ℝ))) atTop (𝓝 (0 : ℝ))
  simpa only [div_div] using h

theorem deriv_samplePoint (n : ℕ) (hn : 0 < n) :
    deriv exampleFunction (samplePoint n) = -1 := by
  rw [deriv_of_ne_zero _ (ne_of_gt (samplePoint_pos n hn))]
  have hi : 1 / samplePoint n = (n : ℝ) * (2 * Real.pi) := by
    simp [samplePoint,
      Specs.SingleVariableAnalysis.Ch04.NoncontinuousDerivative.samplePointValue, mul_comm]
  rw [hi, Real.cos_nat_mul_two_pi]
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_nat_mul_two_pi_sub 0 n
  rw [hs]
  ring

theorem not_continuousAt_deriv : ¬ ContinuousAt (deriv exampleFunction) 0 := by
  intro hc
  have hlim := hc.tendsto.comp samplePoint_tendsto
  rw [deriv_zero] at hlim
  have hm : Tendsto (fun n => deriv exampleFunction (samplePoint n)) atTop
      (𝓝 (-1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (deriv_samplePoint n hn).symm
  have he : (0 : ℝ) = -1 := tendsto_nhds_unique hlim hm
  norm_num at he

theorem not_contDiffAt_one : ¬ ContDiffAt ℝ 1 exampleFunction 0 := by
  intro hc
  exact not_continuousAt_deriv (hc.derivWithin (m := 0) (by norm_num)).continuousAt

end SingleVariableAnalysis.NoncontinuousDerivative
