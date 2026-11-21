import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.GammaRecurrence
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDefinition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Recurrence and factorial values of the source's improper Gamma integral.

The upstream `gamma_eq_realGamma` identifies the sum of the independent
Darboux limits with Mathlib's Gamma for positive parameters. We use
`Real.Gamma_add_one` and `Real.Gamma_one` only through this bridge.
Mathlib proves its recurrence by integration by parts for the truncated
Gamma integral and an exponential domination estimate (Gamma/Basic.lean,
`Complex.partialGamma_add_one`, `Complex.GammaIntegral_add_one`).
The source's two boundary limits are also established independently below;
at zero continuity applies since s > 0, and at infinity a fixed real
power times a decaying exponential tends to zero (Pow/Asymptotics.lean).
Factorial values then follow by natural-number induction.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology

namespace GRSpec
export Specs.SingleVariableAnalysis.Ch18.GammaRecurrence
  (boundaryAtZero boundaryAtInfinity recurrence atOne factorialValues)
end GRSpec

theorem gamma_boundary_at_zero : GRSpec.boundaryAtZero := by
  intro s hs
  have hp := Real.continuousAt_rpow_const (0 : ℝ) s (Or.inr hs.le)
  have he : ContinuousAt (fun t : ℝ => Real.exp (-t)) 0 :=
    Real.continuous_exp.continuousAt.comp continuousAt_id.neg
  have hc : ContinuousAt (fun t : ℝ => -(t ^ s * Real.exp (-t))) 0 := (hp.mul he).neg
  have h := hc.tendsto.mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa only [Pi.neg_apply, Pi.mul_apply, Real.zero_rpow hs.ne', zero_mul, neg_zero] using h

theorem gamma_boundary_at_infinity : GRSpec.boundaryAtInfinity := by
  intro s _hs
  simpa only [neg_mul, one_mul, neg_zero] using
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s 1 zero_lt_one).neg

theorem gamma_recurrence : GRSpec.recurrence := by
  intro s hs
  rw [gamma_eq_realGamma (s + 1) (add_pos hs zero_lt_one),
    gamma_eq_realGamma s hs]
  exact Real.Gamma_add_one hs.ne'

theorem gamma_at_one : GRSpec.atOne := by
  change GSpec.gammaIntegralValue 1 zero_lt_one = 1
  rw [gamma_eq_realGamma 1 zero_lt_one, Real.Gamma_one]

theorem gamma_factorial_values : GRSpec.factorialValues := by
  intro n
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one] using
      (show GSpec.gammaIntegralValue 1 zero_lt_one = 1 from gamma_at_one)
  | succ n ih =>
    have hn : 0 < (n : ℝ) + 1 :=
      lt_add_of_le_of_pos (Nat.cast_nonneg n) zero_lt_one
    have hrec := gamma_recurrence ((n : ℝ) + 1) hn
    simpa only [Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_succ] using hrec.trans (congrArg (fun x : ℝ => ((n : ℝ) + 1) * x) ih)

end SingleVariableAnalysis
