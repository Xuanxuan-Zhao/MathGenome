import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.RatioRadius
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.BinomialInterior
import Mathlib.Analysis.Analytic.Binomial

/-!
# Generalized binomial series: interior, termination and radius

K03.13.binomial, paper.tex:1452–1470 (the endpoint tests belong to Ch13.Binomial).
The falling product definition is identified with `Ring.choose` by induction
on the descending Pochhammer polynomial. Natural exponents then reduce to the
finite binomial theorem, with no restriction on the sign of 1+x.

For |x|<1, `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` supplies the
unconditional sum; the approved ordinary-series bridge shifts `range N` to
the source's inclusive `range (N+1)` sums. Positivity of 1+x allows the approved
real-power construction bridge. The library's interior theorem is proved
using analytic Taylor expansion of the complex power, restricted to real
arguments; it does not use the manuscript's zero-derivative proof route.

The radius proof follows the manuscript directly: for nonnatural α the
coefficients never vanish, their successive ratio is (α-n)/(n+1), and the
absolute ratios tend to 1. The approved ratio theorem identifies the source's
root-limsup radius with 1. No formal multilinear radius is substituted for it.

Library source and public documentation:
Mathlib/Analysis/Analytic/Binomial.lean (real interior theorem),
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Binomial.html
-/

noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped BigOperators Topology ENNReal

/-- The empty falling product gives c₀=1; every denominator is a nonzero factorial. -/
def binomialCoefficient (α : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (α - (j : ℝ))) / (n.factorial : ℝ)

theorem binomialCoefficient_zero (α : ℝ) : binomialCoefficient α 0 = 1 := by
  simp [binomialCoefficient]

theorem binomialCoefficient_recurrence (α : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * binomialCoefficient α (n + 1) =
      (α - n) * binomialCoefficient α n := by
  simp only [binomialCoefficient, Finset.prod_range_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem binomialCoefficient_eq_choose (α : ℝ) (n : ℕ) :
    binomialCoefficient α n = Ring.choose α n := by
  rw [Ring.choose_eq_smul]
  simp only [smul_eq_mul]
  have hp : (descPochhammer ℤ n).smeval α =
      ∏ j ∈ Finset.range n, (α - (j : ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp [descPochhammer_succ_right, Polynomial.smeval_mul,
        Polynomial.smeval_sub, Polynomial.smeval_natCast, ih, Finset.prod_range_succ]
  rw [hp]
  simp only [binomialCoefficient, div_eq_mul_inv, mul_comm]

theorem binomialCoefficient_nat (m n : ℕ) :
    binomialCoefficient (m : ℝ) n = (m.choose n : ℝ) := by
  rw [binomialCoefficient_eq_choose, Ring.choose_natCast]

theorem binomialCoefficient_termination (m n : ℕ) (h : m < n) :
    binomialCoefficient (m : ℝ) n = 0 := by
  rw [binomialCoefficient_nat, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

theorem binomial_natural_identity (m : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range (m + 1), binomialCoefficient (m : ℝ) n * x^n =
      (1 + x)^m := by
  simp only [binomialCoefficient_nat]
  simpa [mul_comm, add_comm] using (add_pow x (1 : ℝ) m).symm

theorem binomial_interior (α x : ℝ) (hx : |x| < 1) :
    RealPowerSeriesHasSum (binomialCoefficient α) 0 x (realPower (1 + x) α) := by
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := α)).hasSum
    (y := x) (by simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx)
  have hb : 0 < 1 + x := by have := (abs_lt.mp hx).1; linarith
  rw [realPower_eq_rpow _ hb]
  have hs' : HasSum (fun n => binomialCoefficient α n * x^n) ((1+x)^α) := by
    simpa [binomialSeries, binomialCoefficient_eq_choose, mul_comm] using hs
  change RealSeriesHasSum (fun n => binomialCoefficient α n * (x-0)^n) ((1+x)^α)
  simpa only [sub_zero] using PowerSeriesDifferentiation.real_hasSum_of_hasSum hs'

theorem binomialCoefficient_ne_zero (α : ℝ) (hα : ∀ m : ℕ, α ≠ (m : ℝ))
    (n : ℕ) : binomialCoefficient α n ≠ 0 := by
  apply div_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => sub_ne_zero.mpr (hα j))
  · exact_mod_cast n.factorial_ne_zero

theorem binomialCoefficient_ratio (α : ℝ) (hα : ∀ m : ℕ, α ≠ (m : ℝ))
    (n : ℕ) : binomialCoefficient α (n+1) / binomialCoefficient α n =
      (α - n) / (n + 1 : ℝ) := by
  apply (div_eq_div_iff (binomialCoefficient_ne_zero α hα n)
    (by positivity : (n + 1 : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using binomialCoefficient_recurrence α n

theorem binomial_nonnatural_radius (α : ℝ) (hα : ∀ m : ℕ, α ≠ (m : ℝ)) :
    realPowerSeriesRadius (binomialCoefficient α) = 1 := by
  have hlim : Tendsto (fun n : ℕ => (α - n) / (n + 1 : ℝ)) atTop (𝓝 (-1)) := by
    have h := ((tendsto_const_nhds (x := α + 1)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    convert h using 1
    · funext n
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · norm_num
  have hratio : Tendsto (fun n => ENNReal.ofReal
      |binomialCoefficient α (n+1) / binomialCoefficient α n|) atTop (𝓝 1) := by
    simp_rw [binomialCoefficient_ratio α hα]
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.abs
    change Tendsto (fun n : ℕ => ENNReal.ofReal |(α - n) / (n + 1 : ℝ)|)
      atTop (𝓝 (ENNReal.ofReal |(-1 : ℝ)|)) at hh
    simpa using hh
  simpa only [inv_one] using real_powerSeries_ratio_radius
    (binomialCoefficient α) 1 ⟨0, fun n _ => binomialCoefficient_ne_zero α hα n⟩ hratio

end SingleVariableAnalysis
