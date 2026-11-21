import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.QuadraticFourier
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.C1Uniform
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Representation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Parts
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
namespace SingleVariableAnalysis
open Set Filter Riemann
open scoped BigOperators Topology
namespace QuadraticFourier
open Specs.SingleVariableAnalysis.Ch19.QuadraticFourier

abbrev quadratic := quadraticValue

lemma polynomial_continuous : Continuous (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_id.pow 2)

lemma polynomial_endpoints :
    (((-Real.pi) ^ 2 : ℝ) : ℂ) = ((Real.pi ^ 2 : ℝ) : ℂ) := by simp

lemma extension_complex :
    (fun x => (quadratic x : ℂ)) =
      fourierPeriodicExtension (fun t => ((t ^ 2 : ℝ) : ℂ)) := by
  rfl

end QuadraticFourier
open QuadraticFourier Specs.SingleVariableAnalysis.Ch19.QuadraticFourier

/-- The actual periodic extension agrees at both endpoints as well as inside. -/
theorem quadratic_fourier_extension : extensionProperties := by
  obtain ⟨hc, hp, he⟩ := fourier_periodic_extension _
    polynomial_continuous.continuousOn polynomial_endpoints
  refine ⟨Complex.continuous_re.comp hc, ?_, ?_⟩
  · intro x
    exact congrArg Complex.re (hp x)
  · intro x hx
    exact congrArg Complex.re (he hx)

theorem quadratic_fourier_integrability : integrability := by
  have hi := Fourier.realIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) quadratic_fourier_extension.1.continuousOn
  exact ⟨⟨quadratic_fourier_extension.2.1, hi⟩,
    fourierCosCoeff_integrable _ hi, fourierSinCoeff_integrable _ hi⟩

namespace QuadraticFourier
lemma primitive_cos_deriv (n : ℝ) (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t^2 * Real.sin (n*t) / n +
      2*t*Real.cos (n*t)/n^2 - 2*Real.sin (n*t)/n^3)
      (x^2 * Real.cos (n*x)) x := by
  have hs := (hasDerivAt_id x).const_mul n |>.sin
  have hc := (hasDerivAt_id x).const_mul n |>.cos
  convert (((((hasDerivAt_id x).pow 2).mul hs).div_const n).add
    ((((hasDerivAt_id x).const_mul 2).mul hc).div_const (n^2))).sub
    ((hs.const_mul 2).div_const (n^3)) using 1 <;> (try dsimp) <;> (try funext t) <;> (try dsimp) <;> field_simp [hn] <;> ring

lemma primitive_sin_deriv (n : ℝ) (hn : n ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -t^2 * Real.cos (n*t) / n +
      2*t*Real.sin (n*t)/n^2 + 2*Real.cos (n*t)/n^3)
      (x^2 * Real.sin (n*x)) x := by
  have hs := (hasDerivAt_id x).const_mul n |>.sin
  have hc := (hasDerivAt_id x).const_mul n |>.cos
  convert ((((((hasDerivAt_id x).pow 2).neg).mul hc).div_const n).add
    ((((hasDerivAt_id x).const_mul 2).mul hs).div_const (n^2))).add
    ((hc.const_mul 2).div_const (n^3)) using 1 <;> (try dsimp) <;> (try funext t) <;> (try dsimp) <;> field_simp [hn] <;> ring
end QuadraticFourier

/-- Fourier coefficients with the manuscript's proper Darboux normalization. -/
theorem quadratic_fourier_coefficients : coefficients := by
  intro h ha hb
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have heq := quadratic_fourier_extension.2.2
  have hzero := real_ftc_second (fun t : ℝ => t^3/3) quadraticValue
    (-Real.pi) Real.pi hab ((continuous_id.pow 3).div_const 3).continuousOn
    (fun x hx => by
      rw [heq (Ioo_subset_Icc_self hx)]
      convert ((hasDerivAt_id x).pow 3).div_const 3 using 1 <;> norm_num) h
  constructor
  · change (1 / Real.pi) * Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue _ h / 2 = _
    erw [hzero]
    field_simp
    ring
  · intro n
    have hn : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast n.pos)
    have hs : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_nat_mul_pi n
    have hc : Real.cos ((n : ℝ) * Real.pi) = (-1 : ℝ) ^ (n : ℕ) :=
      Real.cos_nat_mul_pi n
    constructor
    · have hv := real_ftc_second
        (fun t : ℝ => -t^2 * Real.cos ((n : ℝ)*t) / n +
          2*t*Real.sin ((n : ℝ)*t)/(n : ℝ)^2 + 2*Real.cos ((n : ℝ)*t)/(n : ℝ)^3)
        (fun t => quadraticValue t * Real.sin ((n : ℝ)*t))
        (-Real.pi) Real.pi hab (by fun_prop)
        (fun x hx => by
          rw [heq (Ioo_subset_Icc_self hx)]
          exact primitive_sin_deriv n hn x) (hb n)
      change (1 / Real.pi) * Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue _ (hb n) = 0
      erw [hv]
      simp only [mul_neg, Real.sin_neg, Real.cos_neg, hs, hc, neg_sq,
        neg_zero, mul_zero, zero_div, add_zero, sub_self]
    · have hv := real_ftc_second
        (fun t : ℝ => t^2 * Real.sin ((n : ℝ)*t) / n +
          2*t*Real.cos ((n : ℝ)*t)/(n : ℝ)^2 - 2*Real.sin ((n : ℝ)*t)/(n : ℝ)^3)
        (fun t => quadraticValue t * Real.cos ((n : ℝ)*t))
        (-Real.pi) Real.pi hab (by fun_prop)
        (fun x hx => by
          rw [heq (Ioo_subset_Icc_self hx)]
          exact primitive_cos_deriv n hn x) (ha n)
      change (1 / Real.pi) * Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue _ (ha n) = _
      erw [hv]
      simp only [mul_neg, Real.sin_neg, Real.cos_neg, hs, hc, neg_sq,
        neg_zero, mul_zero, zero_div, zero_add, sub_zero]
      field_simp
      ring

namespace QuadraticFourier

lemma majorant_summable : Summable (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ)^2)) :=
  (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))

lemma term_bound (k : ℕ) (x : ℝ) :
    |termValue k x| ≤ 1 / (((k+1 : ℕ) : ℝ)^2) := by
  unfold termValue
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show 0 ≤ (((k+1 : ℕ) : ℝ)^2) from sq_nonneg _)]
  exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (sq_nonneg _)

lemma term_summable (x : ℝ) : Summable (fun k => termValue k x) :=
  majorant_summable.of_norm_bounded (fun k => by simpa only [Real.norm_eq_abs] using term_bound k x)

end QuadraticFourier

theorem quadratic_fourier_absolute : absoluteConvergence := by
  constructor
  · intro x
    exact majorant_summable.of_norm_bounded (fun k => by
      simpa only [Real.norm_eq_abs, abs_abs] using term_bound k x)
  · exact tendstoUniformly_tsum_nat majorant_summable (fun k x => by
      simpa only [Real.norm_eq_abs, abs_abs] using term_bound k x)

/-- The explicit cosine partial sums converge uniformly to the periodic quadratic. -/
theorem quadratic_fourier_uniform : uniformExpansion := by
  let f : ℝ → ℂ := fun t => ((t ^ 2 : ℝ) : ℂ)
  have hci : ContDiffOn ℝ 1 f (Icc (-Real.pi) Real.pi) := by
    have h : ContDiff ℝ 1 f := Complex.ofRealCLM.contDiff.comp (contDiff_id.pow 2)
    exact h.contDiffOn
  obtain ⟨H, _hs, _hc, _hp, _he, hu, _ha, _hsum⟩ :=
    fourier_c1_uniform_to_extension f hci polynomial_endpoints
  obtain ⟨hq, Hcos, Hsin⟩ := quadratic_fourier_integrability
  let g : ℝ → ℂ := fun x => (quadraticValue x : ℂ)
  have hgi := fourierRealEmbedding_integrable _ hq.2
  let Hg := fourierCoeff_integrable g hgi
  have hfi := Fourier.complexIntegrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) polynomial_continuous.continuousOn
  have hcoeff (n : ℤ) : fourierCoeff f n (H n) = fourierCoeff g n (Hg n) :=
    Fourier.coefficient_eq_of_eqOn hfi hgi H Hg
      (fun x hx => by dsimp [f, g]; rw [quadratic_fourier_extension.2.2 hx]) n
  have he := quadratic_fourier_coefficients hq.2 Hcos Hsin
  have hpartial (N : ℕ) (x : ℝ) :
      Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue f H N x =
      (partialValue N x : ℂ) := by
    calc
      _ = Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue g Hg N x := by
        unfold Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue
        apply Finset.sum_congr rfl
        intro n _
        exact congrArg (fun z : ℂ => z * fourierMode n x) (hcoeff n)
      _ = _ := by
        rw [fourierPartialSum_real quadraticValue hq Hg Hcos Hsin N x]
        congr 1
        change _ = Real.pi^2/3 + 4 * ∑ k ∈ Finset.range N, termValue k x
        rw [he.1, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        rw [(he.2 ⟨k+1, Nat.succ_pos k⟩).1, (he.2 ⟨k+1, Nat.succ_pos k⟩).2]
        dsimp [termValue]
        ring
  intro ε hε
  obtain ⟨N, hN⟩ := hu ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have hh := hN n hn x
  rw [hpartial] at hh
  change ‖(partialValue n x : ℂ) - (quadraticValue x : ℂ)‖ < ε at hh
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh

theorem quadratic_fourier_series : seriesIdentity := by
  intro x hx
  have ht := (term_summable x).hasSum.tendsto_sum_nat
  have hp : Tendsto (fun N => partialValue N x) atTop
      (𝓝 (Real.pi^2/3 + 4 * ∑' k, termValue k x)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul ht)
  have hq : Tendsto (fun N => partialValue N x) atTop (𝓝 (quadraticValue x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := quadratic_fourier_uniform ε hε
    exact ⟨N, fun n hn => by simpa only [Real.dist_eq] using hN n hn x⟩
  have he := tendsto_nhds_unique hp hq
  rw [quadratic_fourier_extension.2.2 hx] at he
  convert (term_summable x).hasSum using 1
  linarith

/-- Evaluate the proved Fourier expansion at π to obtain the Basel sum. -/
theorem quadratic_fourier_basel : baselSum := by
  have h := quadratic_fourier_series Real.pi
    ⟨by linarith [Real.pi_pos], le_rfl⟩
  change HasSum (fun k : ℕ => 1 / (((k+1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 6)
  convert h using 1
  · funext k
    unfold termValue
    rw [Real.cos_nat_mul_pi, ← mul_pow]
    norm_num
  · ring

end SingleVariableAnalysis
