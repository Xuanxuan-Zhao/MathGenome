import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.MTest
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.CauSeqFilter
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The exponential constructed from its factorial series

K03.07.exp_construction, paper.tex:1542–1560. Absolute convergence follows
from the numerical factorial majorant; its library proof is the ratio test
(`Real.summable_pow_div_factorial`, Analysis/SpecificLimits/Normed.lean).
The upstream M-test gives uniform convergence on every closed bounded disk.
Sum uniqueness identifies that limit with the constructed series sum.

The canonical complex exponential is itself the Cauchy-sequence limit of
these same partial sums (Analysis/Complex/Exponential.lean, `exp'`, `exp`).
We identify it by uniqueness of limits, without Taylor's theorem, logarithms
or ODE uniqueness. The real derivative is obtained below by differentiating
the shifted series on a bounded real interval. All increments are real.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped BigOperators Topology

/-- The sum of the everywhere absolutely convergent factorial series. -/
def seriesExp (z : ℂ) : ℂ := ∑' n : ℕ, z^n / (n.factorial : ℂ)

/-- The real factorial series; the restriction bridge is proved below. -/
def realSeriesExp (x : ℝ) : ℝ := ∑' n : ℕ, x^n / (n.factorial : ℝ)

namespace ExpConstruction

theorem norm_term (z : ℂ) (n : ℕ) :
    ‖z^n / (n.factorial : ℂ)‖ = ‖z‖^n / (n.factorial : ℝ) := by
  simp only [norm_div, norm_pow, Complex.norm_natCast]

theorem norm_summable (z : ℂ) : Summable (fun n => ‖z^n / (n.factorial : ℂ)‖) := by
  simp only [norm_term]
  exact Real.summable_pow_div_factorial ‖z‖

theorem summable (z : ℂ) : Summable (fun n => z^n / (n.factorial : ℂ)) :=
  (norm_summable z).of_norm

theorem disk_bound (R : ℝ) (_hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖z^n / (n.factorial : ℂ)‖ ≤ R^n / (n.factorial : ℝ) := by
  rw [norm_term]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)

end ExpConstruction

/-- Absolute convergence is stated in the project's ordinary series interface. -/
theorem expSeries_absolute : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.absoluteConvergence := by
  intro z
  exact ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum (ExpConstruction.norm_summable z).hasSum⟩

/-- The defining sum is the limit of the inclusive partial sums. -/
theorem expSeries_hasSum : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.seriesValue := by
  intro z
  exact PowerSeriesDifferentiation.complex_hasSum_of_hasSum (ExpConstruction.summable z).hasSum

/-- One tail threshold controls every argument in the disk. -/
theorem expSeries_uniform_disk : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.uniformDisk := by
  intro R hR
  obtain ⟨⟨f, hf⟩, _⟩ := complex_m_test
    (fun n (z : {z : ℂ // ‖z‖ ≤ R}) => (z : ℂ)^n / (n.factorial : ℂ))
    (fun n => R^n / (n.factorial : ℝ))
    (fun n => by positivity)
    (fun n z => ExpConstruction.disk_bound R hR z z.property n)
    ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum (Real.summable_pow_div_factorial R).hasSum⟩
  have he : f = fun (z : {z : ℂ // ‖z‖ ≤ R}) => seriesExp (z : ℂ) := by
    funext z
    exact complex_series_sum_unique _ _ _ (complexUniformConverges_pointwise _ _ hf z)
      (expSeries_hasSum z)
  simpa only [he, ComplexUniformConverges, complexPartialSum, seriesExp,
    Specs.SingleVariableAnalysis.Ch12.Uniform.complexUniformConvergesValue,
    Specs.SingleVariableAnalysis.Ch11.PartialSums.complexPartialSumValue,
    Specs.SingleVariableAnalysis.Ch07.ExpConstruction.seriesExpValue] using hf

theorem real_expSeries_hasSum : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realSeriesValue := by
  intro x
  exact PowerSeriesDifferentiation.real_hasSum_of_hasSum (Real.summable_pow_div_factorial x).hasSum

/-- The defining Cauchy-sequence and the series have identical partial sums. -/
theorem expSeries_eq_complexExp : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.canonicalComplex := by
  intro z
  change seriesExp z = Complex.exp z
  rw [Complex.exp]
  exact tendsto_nhds_unique (ExpConstruction.summable z).hasSum.tendsto_sum_nat
    z.exp'.tendsto_limit

/-- Casting the real series commutes with its convergent sum. -/
theorem expSeries_real_restriction (x : ℝ) :
    seriesExp (x : ℂ) = (realSeriesExp x : ℂ) := by
  have h := Complex.ofRealCLM.hasSum (Real.summable_pow_div_factorial x).hasSum
  have h' : HasSum (fun n : ℕ => (x : ℂ)^n / (n.factorial : ℂ)) (realSeriesExp x : ℂ) := by
    simpa only [realSeriesExp, Complex.ofRealCLM_apply, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_natCast] using h
  exact h'.tsum_eq

theorem expSeries_eq_realExp : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.canonicalReal := by
  intro x
  apply Complex.ofReal_injective
  exact (expSeries_real_restriction x).symm.trans
    ((expSeries_eq_complexExp x).trans (Complex.ofReal_exp x).symm)

namespace ExpConstruction

/-- The derivative of the shifted nth term is the unshifted nth term. -/
theorem shifted_term_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y^(n+1) / ((n+1).factorial : ℝ))
      (x^n / (n.factorial : ℝ)) x := by
  have hd : HasDerivAt (fun y : ℝ => y^(n+1) / ((n+1).factorial : ℝ))
      (((n+1 : ℕ) : ℝ) * x^n / ((n+1).factorial : ℝ)) x := by
    simpa using ((hasDerivAt_id x).pow (n+1)).div_const ((n+1).factorial : ℝ)
  convert hd using 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Removing the constant term expresses E as 1 plus the shifted series. -/
theorem real_series_split (y : ℝ) :
    realSeriesExp y = 1 + ∑' n : ℕ, y^(n+1) / ((n+1).factorial : ℝ) := by
  simpa only [realSeriesExp, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] using
    ((Real.summable_pow_div_factorial y).sum_add_tsum_nat_add 1).symm

end ExpConstruction

/-- Termwise differentiation on a bounded real interval, with an independently
proved summable factorial majorant of the derivative series. -/
theorem real_expSeries_hasDerivAt : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.realDerivative := by
  intro x
  change HasDerivAt realSeriesExp (realSeriesExp x) x
  let A : ℝ := |x| + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hxA : x ∈ Ioo (-A) A := by
    have h := abs_le.mp (le_refl |x|)
    constructor <;> dsimp [A] <;> linarith [h.1, h.2]
  have hd : HasDerivAt (fun y : ℝ => ∑' n : ℕ, y^(n+1) / ((n+1).factorial : ℝ))
      (realSeriesExp x) x := by
    apply hasDerivAt_tsum_of_isPreconnected (Real.summable_pow_div_factorial A)
      isOpen_Ioo (convex_Ioo (-A) A).isPreconnected
      (fun n y _ => ExpConstruction.shifted_term_hasDerivAt n y)
      (fun n y hy => ?_)
      (show (0 : ℝ) ∈ Ioo (-A) A by constructor <;> linarith)
      ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial 0)) hxA
    simp only [Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩) _
  exact (hd.const_add 1).congr_of_eventuallyEq
    (Eventually.of_forall ExpConstruction.real_series_split)

/-- The complex-valued restriction has a derivative with real increments. -/
theorem expSeries_real_hasDerivAt : Specs.SingleVariableAnalysis.Ch07.ExpConstruction.complexRealDerivative := by
  intro x
  change HasDerivAt (fun t : ℝ => seriesExp (t : ℂ)) (seriesExp (x : ℂ)) x
  have he : (fun t : ℝ => seriesExp (t : ℂ)) = fun t => (realSeriesExp t : ℂ) :=
    funext expSeries_real_restriction
  rw [he, expSeries_real_restriction x]
  exact (real_expSeries_hasDerivAt x).ofReal_comp

end SingleVariableAnalysis
