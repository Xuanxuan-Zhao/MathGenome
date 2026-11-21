import MathGenome.Internal.Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity
import Mathlib.Algebra.Polynomial.SumIteratedDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
Analytic identities for the special Lindemann relation. Polynomial
nilpotence of differentiation gives the telescoping identity. The real
FTC for ℂ-valued functions is the vector-valued form of applying real FTC
to both components; it introduces no complex contour integration.
-/

noncomputable section

namespace D07.Appendix.LindemannRelationExponentialIntegralIdentity

open Polynomial
open scoped BigOperators
open Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity

abbrev derivativeSum :=
  Specs.D07.Appendix.LindemannRelationExponentialIntegralIdentity.derivativeSum

/-- A degree bound permits padding the sum by zero higher derivatives. -/
theorem derivativeSum_eq_sumIDeriv (f : Polynomial ℂ) (N : ℕ)
    (h : f.natDegree ≤ N) : derivativeSum f N = Polynomial.sumIDeriv f := by
  exact (Polynomial.sumIDeriv_apply_of_le h).symm

theorem telescoping_identity : TelescopingIdentity := by
  intro f N h
  change (derivativeSum f N).derivative - derivativeSum f N = -f
  rw [derivativeSum_eq_sumIDeriv f N h]
  have hf := Polynomial.sumIDeriv_eq_self_add f
  linear_combination -hf

theorem segment_derivative : SegmentDerivative := by
  intro f N h β t
  change HasDerivAt
    (fun x : ℝ => Complex.exp (-((x : ℂ) * β)) *
      (derivativeSum f N).eval ((x : ℂ) * β)) _ t
  have h₀ := (hasDerivAt_id' t).smul_const β
  have h₁ := h₀.fun_neg.cexp
  have h₂ := ((derivativeSum f N).hasDerivAt (t • β)).comp t h₀
  have heval : (derivativeSum f N).derivative.eval (t • β) -
      (derivativeSum f N).eval (t • β) = -f.eval (t • β) := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_neg] using
      congrArg (Polynomial.eval (t • β)) (telescoping_identity f N h)
  simp only [Complex.real_smul] at heval
  convert! h₁.mul h₂ using 1;
    simp only [one_smul, Complex.real_smul, Function.comp_apply]
  linear_combination -(Complex.exp (-((t : ℂ) * β)) * β) * heval

/-- A shifted integrating factor puts the required integrand directly
under FTC, so there is no need to divide by β (which may be zero). -/
theorem shifted_segment_derivative (f : Polynomial ℂ) (N : ℕ)
    (h : f.natDegree ≤ N) (β : ℂ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => -(Complex.exp ((1 - (x : ℂ)) * β) *
        (derivativeSum f N).eval ((x : ℂ) * β)))
      (β * (Complex.exp ((1 - (t : ℂ)) * β) * f.eval ((t : ℂ) * β))) t := by
  have h₀ := (hasDerivAt_id' t).smul_const β
  have h₁ := (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id' t)).smul_const β).cexp
  have h₂ := ((derivativeSum f N).hasDerivAt (t • β)).comp t h₀
  have heval : (derivativeSum f N).derivative.eval (t • β) -
      (derivativeSum f N).eval (t • β) = -f.eval (t • β) := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_neg] using
      congrArg (Polynomial.eval (t • β)) (telescoping_identity f N h)
  simp only [Complex.real_smul] at heval
  convert! (h₁.mul h₂).fun_neg using 1 <;>
    simp only [zero_sub, one_smul, Complex.real_smul, Function.comp_apply,
      Pi.sub_apply, Pi.mul_apply, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_neg]
  linear_combination (Complex.exp ((1 - (t : ℂ)) * β) * β) * heval

theorem exponential_integral_identity : ExponentialIntegralIdentity := by
  intro f N h β
  change Complex.exp β * (derivativeSum f N).eval 0 - (derivativeSum f N).eval β = _
  rw [← intervalIntegral.integral_const_mul]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t _ => shifted_segment_derivative f N h β t)
    (ContinuousOn.intervalIntegrable (by fun_prop))
  simpa [sub_eq_add_neg, add_comm] using hFTC.symm

theorem summed_exponential_integral_identity : SummedExponentialIntegralIdentity := by
  intro f N h m β k hrel
  change -((k : ℂ) * (derivativeSum f N).eval 0 +
      ∑ j, (derivativeSum f N).eval (β j)) = _
  simp_rw [← exponential_integral_identity f N h]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsum : (∑ j, Complex.exp (β j)) = -(k : ℂ) := eq_neg_of_add_eq_zero_right hrel
  rw [hsum]
  ring

end D07.Appendix.LindemannRelationExponentialIntegralIdentity
