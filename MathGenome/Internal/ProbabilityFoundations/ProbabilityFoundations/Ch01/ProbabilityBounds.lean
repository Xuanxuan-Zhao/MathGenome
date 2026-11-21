import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.ProbabilityObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Markov, moment, Chebyshev and exponential bounds (paper.tex:304–325).
Extended integrals retain infinite nonnegative expectations. -/
open MeasureTheory
open scoped ENNReal

namespace ProbabilityFoundations.Ch01
universe u

/-- The centered second moment; on square integrable variables this is the variance. -/
noncomputable def realVariance {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  realExpectation P (fun ω => (X ω - realExpectation P X) ^ 2)

theorem markov_ge {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (a : ℝ) (ha : 0 < a) :
    P {ω | ENNReal.ofReal a ≤ Y ω} ≤ nonnegativeExpectation P Y / ENNReal.ofReal a := by
  exact meas_ge_le_lintegral_div hY.aemeasurable (by simpa using ha) ENNReal.ofReal_ne_top

theorem markov_gt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ≥0∞) (hY : Measurable Y)
    (a : ℝ) (ha : 0 < a) :
    P {ω | ENNReal.ofReal a < Y ω} ≤ nonnegativeExpectation P Y / ENNReal.ofReal a := by
  have hs : {ω | ENNReal.ofReal a < Y ω} ⊆ {ω | ENNReal.ofReal a ≤ Y ω} :=
    fun ω (h : ENNReal.ofReal a < Y ω) => le_of_lt h
  exact (measure_mono hs).trans (markov_ge P Y hY a ha)

/-- Applying Markov to a positive real threshold and any contained event.
No integrability or finiteness of the expectation is needed. -/
private theorem transformed_markov {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 < c)
    (s : Set Ω) (hs : ∀ ω ∈ s, c ≤ f ω) :
    P s ≤ (ENNReal.ofReal c)⁻¹ * (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) := by
  have h := meas_ge_le_lintegral_div hf.ennreal_ofReal.aemeasurable
    (by simpa using hc : ENNReal.ofReal c ≠ 0) ENNReal.ofReal_ne_top (μ := P)
  rw [div_eq_mul_inv, mul_comm] at h
  exact (measure_mono (fun ω hω => ENNReal.ofReal_le_ofReal (hs ω hω))).trans h

theorem moment_ge {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    P {ω | a ≤ |X ω|} ≤ ENNReal.ofReal (a ^ (-p)) *
      nonnegativeExpectation P (fun ω => ENNReal.ofReal (|X ω| ^ p)) := by
  have h := transformed_markov P (fun ω => |X ω| ^ p)
    (by simpa only [Real.norm_eq_abs] using hX.norm.pow_const p)
    (a ^ p) (Real.rpow_pos_of_pos ha p) {ω | a ≤ |X ω|}
    (fun ω hω => Real.rpow_le_rpow ha.le hω hp.le)
  simpa only [nonnegativeExpectation, Real.rpow_neg ha.le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos ha p)] using h

theorem moment_gt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (a p : ℝ) (ha : 0 < a) (hp : 0 < p) :
    P {ω | a < |X ω|} ≤ ENNReal.ofReal (a ^ (-p)) *
      nonnegativeExpectation P (fun ω => ENNReal.ofReal (|X ω| ^ p)) := by
  have hs : {ω | a < |X ω|} ⊆ {ω | a ≤ |X ω|} :=
    fun ω (h : a < |X ω|) => le_of_lt h
  exact (measure_mono hs).trans (moment_ge P X hX a p ha hp)

theorem chebyshev_ge {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (h2 : MemLp X 2 P)
    (a : ℝ) (ha : 0 < a) :
    P {ω | a ≤ |X ω - realExpectation P X|} ≤ ENNReal.ofReal (realVariance P X / a ^ 2) := by
  have h := ProbabilityTheory.meas_ge_le_variance_div_sq h2 ha
  rw [ProbabilityTheory.variance_eq_integral hX.aemeasurable] at h
  exact h

theorem chebyshev_gt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) (h2 : MemLp X 2 P)
    (a : ℝ) (ha : 0 < a) :
    P {ω | a < |X ω - realExpectation P X|} ≤ ENNReal.ofReal (realVariance P X / a ^ 2) := by
  have hs : {ω | a < |X ω - realExpectation P X|} ⊆ {ω | a ≤ |X ω - realExpectation P X|} :=
    fun ω (h : a < |X ω - realExpectation P X|) => le_of_lt h
  exact (measure_mono hs).trans (chebyshev_ge P X hX h2 a ha)

theorem exponential_markov_ge {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (x θ : ℝ) (hθ : 0 < θ) :
    P {ω | x ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-θ * x)) *
      nonnegativeExpectation P (fun ω => ENNReal.ofReal (Real.exp (θ * X ω))) := by
  have h := transformed_markov P (fun ω => Real.exp (θ * X ω))
    (hX.const_mul θ).exp (Real.exp (θ * x)) (Real.exp_pos _) {ω | x ≤ X ω}
    (fun ω hω => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hθ.le))
  simpa only [nonnegativeExpectation, neg_mul, Real.exp_neg,
    ENNReal.ofReal_inv_of_pos (Real.exp_pos _)] using h

theorem exponential_markov_gt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (x θ : ℝ) (hθ : 0 < θ) :
    P {ω | x < X ω} ≤ ENNReal.ofReal (Real.exp (-θ * x)) *
      nonnegativeExpectation P (fun ω => ENNReal.ofReal (Real.exp (θ * X ω))) := by
  have hs : {ω | x < X ω} ⊆ {ω | x ≤ X ω} :=
    fun ω (h : x < X ω) => le_of_lt h
  exact (measure_mono hs).trans (exponential_markov_ge P X hX x θ hθ)

end ProbabilityFoundations.Ch01
