import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinNonuniqueCoshSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Set

namespace ExpandedFA.PartIV.KreinNonuniqueCoshSeries

/-- The ungrouped absolute coefficient of the two exponential series. -/
def weight (k : ℕ × ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ k.1 / k.1.factorial) * ((1 / 2 : ℝ) ^ k.2 / k.2.factorial)

/-- Folding a pair of exponential frequencies onto the nonnegative axis. -/
def frequency (k : ℕ × ℕ) : ℝ := |(k.1 : ℝ) - k.2|

lemma weight_pos (k : ℕ × ℕ) : 0 < weight k := by
  unfold weight
  positivity

lemma frequency_nonneg (k : ℕ × ℕ) : 0 ≤ frequency k := abs_nonneg _

lemma frequency_eq_zero (k : ℕ × ℕ) : frequency k = 0 ↔ k.1 = k.2 := by
  simp [frequency, sub_eq_zero]

lemma cosh_frequency (k : ℕ × ℕ) (s : ℝ) :
    Real.cosh (frequency k * s) = Real.cosh (((k.1 : ℝ) - k.2) * s) := by
  unfold frequency
  rcases le_total 0 ((k.1 : ℝ) - k.2) with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, neg_mul, Real.cosh_neg]

lemma double_exp_hasSum (x y : ℝ) :
    HasSum (fun k : ℕ × ℕ => (x ^ k.1 / k.1.factorial) *
      (y ^ k.2 / k.2.factorial)) (Real.exp (x + y)) := by
  rw [Real.exp_add]
  simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp x).mul
    (NormedSpace.expSeries_div_hasSum_exp y)
    (summable_mul_of_summable_norm
      (NormedSpace.expSeries_div_hasSum_exp x).summable.norm
      (NormedSpace.expSeries_div_hasSum_exp y).summable.norm)

lemma exponential_term (t s : ℝ) (k : ℕ × ℕ) :
    ((t * Real.exp s / 2) ^ k.1 / k.1.factorial) *
        ((t * Real.exp (-s) / 2) ^ k.2 / k.2.factorial) =
      weight k * t ^ (k.1 + k.2) * Real.exp (((k.1 : ℝ) - k.2) * s) := by
  rw [weight, pow_add, sub_mul, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul]
  simp only [div_pow, mul_pow, Real.exp_neg]
  ring

lemma exponential_hasSum (t s : ℝ) :
    HasSum (fun k : ℕ × ℕ => weight k * t ^ (k.1 + k.2) *
      Real.exp (((k.1 : ℝ) - k.2) * s)) (Real.exp (t * Real.cosh s)) := by
  have h := double_exp_hasSum (t * Real.exp s / 2) (t * Real.exp (-s) / 2)
  convert h.congr_fun (fun k => (exponential_term t s k).symm) using 1
  rw [Real.cosh_eq]
  congr 1
  ring

lemma cosh_hasSum (t s : ℝ) :
    HasSum (fun k : ℕ × ℕ => weight k * t ^ (k.1 + k.2) *
      Real.cosh (frequency k * s)) (Real.exp (t * Real.cosh s)) := by
  have h := ((exponential_hasSum t s).add (exponential_hasSum t (-s))).div_const 2
  simp only [Real.cosh_neg, add_self_div_two] at h
  apply h.congr_fun
  intro k
  rw [cosh_frequency, Real.cosh_eq]
  simp only [mul_neg]
  ring

/-- Retain an arbitrary subfamily of the nonnegative double-series weights. -/
def selectedWeight (Q : ℕ × ℕ → Prop) (k : ℕ × ℕ) : ℝ :=
  @ite ℝ (Q k) (Classical.propDecidable _) (weight k) 0

lemma selectedWeight_nonneg (Q : ℕ × ℕ → Prop) (k : ℕ × ℕ) :
    0 ≤ selectedWeight Q k := by
  classical
  unfold selectedWeight
  split_ifs
  · exact (weight_pos k).le
  · exact le_rfl

/-- A countable sum of positive point masses at folded frequencies. -/
def discreteMeasure (Q : ℕ × ℕ → Prop) : Measure ℝ :=
  Measure.sum (fun k => ENNReal.ofReal (selectedWeight Q k) • Measure.dirac (frequency k))

lemma selected_cosh_summable (Q : ℕ × ℕ → Prop) (s : ℝ) :
    Summable (fun k => selectedWeight Q k * Real.cosh (frequency k * s)) := by
  classical
  have h : Summable (fun k => weight k * Real.cosh (frequency k * s)) := by
    simpa using (cosh_hasSum 1 s).summable
  apply h.of_nonneg_of_le
  · intro k
    exact mul_nonneg (selectedWeight_nonneg Q k) (Real.cosh_pos _).le
  · intro k
    unfold selectedWeight
    split_ifs <;> simp [mul_nonneg (weight_pos k).le (Real.cosh_pos _).le]

lemma discrete_integrable_cosh (Q : ℕ × ℕ → Prop) (s : ℝ) :
    Integrable (fun b => Real.cosh (b * s)) (discreteMeasure Q) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (selectedWeight_nonneg Q _),
    Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)] using selected_cosh_summable Q s

lemma discrete_finite (Q : ℕ × ℕ → Prop) : IsFiniteMeasure (discreteMeasure Q) := by
  apply (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
  simpa using discrete_integrable_cosh Q 0

lemma discrete_integral (Q : ℕ × ℕ → Prop) (f : ℝ → ℝ) :
    (∫ b, f b ∂discreteMeasure Q) = ∑' k, selectedWeight Q k * f (frequency k) := by
  simp only [discreteMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (selectedWeight_nonneg Q _), smul_eq_mul]

lemma discrete_null (Q : ℕ × ℕ → Prop) (S : Set ℝ)
    (h : ∀ k, Q k → frequency k ∉ S) : discreteMeasure Q S = 0 := by
  classical
  rw [discreteMeasure, Measure.sum_apply_eq_zero]
  intro k
  by_cases hk : Q k
  · simp [Measure.smul_apply, h k hk]
  · simp [selectedWeight, hk]

/-- The diagonal coefficients supply the unique constant-frequency part. -/
def gamma : Measure ℝ := discreteMeasure (fun k => k.1 = k.2)

/-- Strictly positive, even frequencies carry positive coefficients. -/
def betaPlus : Measure ℝ :=
  discreteMeasure (fun k => k.1 ≠ k.2 ∧ Even (k.1 + k.2))

/-- Odd frequencies carry negative coefficients. -/
def betaMinus : Measure ℝ := discreteMeasure (fun k => ¬ Even (k.1 + k.2))

lemma gamma_support : gamma (Iio 0) = 0 := by
  apply discrete_null
  intro k _
  exact not_lt_of_ge (frequency_nonneg k)

lemma betaPlus_support : betaPlus (Iic 0) = 0 := by
  apply discrete_null
  intro k hk
  exact not_le_of_gt (lt_of_le_of_ne (frequency_nonneg k) (Ne.symm
    (mt (frequency_eq_zero k).mp hk.1)))

lemma betaMinus_support : betaMinus (Iic 0) = 0 := by
  apply discrete_null
  intro k hk
  have hne : k.1 ≠ k.2 := by
    intro he
    apply hk
    rw [he]
    exact ⟨k.2, rfl⟩
  exact not_le_of_gt (lt_of_le_of_ne (frequency_nonneg k) (Ne.symm
    (mt (frequency_eq_zero k).mp hne)))

lemma gamma_cos_integrable (s : ℝ) :
    Integrable (fun a => Real.cos (a * s)) gamma := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  have h := selected_cosh_summable (fun k => k.1 = k.2) 0
  simp only [mul_zero, Real.cosh_zero, mul_one] at h
  convert h using 1
  funext k
  by_cases hk : k.1 = k.2
  · simp [ENNReal.toReal_ofReal (selectedWeight_nonneg _ _),
      (frequency_eq_zero k).mpr hk]
  · simp [selectedWeight, hk]

lemma gamma_cos_integral (s : ℝ) :
    (∫ a, Real.cos (a * s) ∂gamma) = ∑' k, selectedWeight (fun k => k.1 = k.2) k := by
  rw [gamma, discrete_integral]
  apply tsum_congr
  intro k
  by_cases hk : k.1 = k.2
  · simp [(frequency_eq_zero k).mpr hk]
  · simp [selectedWeight, hk]

lemma betaPlus_atom_one : betaPlus {1} = 0 := by
  apply discrete_null
  intro k hk hf
  have hf : |(k.1 : ℝ) - k.2| = 1 := hf
  rcases hk.2 with ⟨n, hn⟩
  rcases le_total 0 ((k.1 : ℝ) - k.2) with h | h
  · rw [abs_of_nonneg h] at hf
    have he : k.1 = k.2 + 1 := by exact_mod_cast (show (k.1 : ℝ) = k.2 + 1 by linarith)
    omega
  · rw [abs_of_nonpos h] at hf
    have he : k.2 = k.1 + 1 := by exact_mod_cast (show (k.2 : ℝ) = k.1 + 1 by linarith)
    omega

lemma betaMinus_atom_one : 0 < betaMinus {1} := by
  have h := (Measure.le_sum
    (fun k => ENNReal.ofReal (selectedWeight (fun k => ¬ Even (k.1 + k.2)) k) •
      Measure.dirac (frequency k)) (1, 0)) {1}
  change _ ≤ betaMinus {1} at h
  apply lt_of_lt_of_le _ h
  norm_num [selectedWeight, frequency, weight]

lemma signed_term (k : ℕ × ℕ) (s : ℝ) :
    selectedWeight (fun k => k.1 = k.2) k +
      selectedWeight (fun k => k.1 ≠ k.2 ∧ Even (k.1 + k.2)) k *
        Real.cosh (frequency k * s) -
      selectedWeight (fun k => ¬ Even (k.1 + k.2)) k *
        Real.cosh (frequency k * s) =
      weight k * (-1 : ℝ) ^ (k.1 + k.2) * Real.cosh (frequency k * s) := by
  classical
  by_cases hd : k.1 = k.2
  · simp [selectedWeight, hd, (frequency_eq_zero k).mpr hd]
  · by_cases he : Even (k.1 + k.2) <;>
      simp [selectedWeight, hd, he, neg_one_pow_eq_ite]

lemma signed_identity (s : ℝ) :
    Real.exp (-Real.cosh s) = (∫ a, Real.cos (a * s) ∂gamma) +
      (∫ b, Real.cosh (b * s) ∂betaPlus) - ∫ b, Real.cosh (b * s) ∂betaMinus := by
  have hg : Summable (fun k => selectedWeight (fun k => k.1 = k.2) k) := by
    simpa using selected_cosh_summable (fun k => k.1 = k.2) 0
  have hp := selected_cosh_summable (fun k => k.1 ≠ k.2 ∧ Even (k.1 + k.2)) s
  have hm := selected_cosh_summable (fun k => ¬ Even (k.1 + k.2)) s
  rw [gamma_cos_integral, betaPlus, betaMinus, discrete_integral, discrete_integral,
    ← hg.tsum_add hp, ← (hg.add hp).tsum_sub hm]
  symm
  calc
    _ = ∑' k, weight k * (-1 : ℝ) ^ (k.1 + k.2) * Real.cosh (frequency k * s) :=
      tsum_congr (fun k => signed_term k s)
    _ = Real.exp (-Real.cosh s) := by simpa using (cosh_hasSum (-1) s).tsum_eq

/-- The discrete half of the nonuniqueness construction. -/
theorem discrete_decomposition : Spec.DiscreteDecomposition := by
  refine ⟨gamma, betaPlus, betaMinus, discrete_finite _, discrete_finite _,
    discrete_finite _, gamma_support, betaPlus_support, betaMinus_support, ?_, ?_,
    betaMinus_atom_one, betaPlus_atom_one⟩
  · intro s
    exact ⟨gamma_cos_integrable s, discrete_integrable_cosh _ s,
      discrete_integrable_cosh _ s, signed_identity s⟩
  · intro R _
    constructor
    · simpa only [betaPlus, mul_comm R] using
        discrete_integrable_cosh (fun k => k.1 ≠ k.2 ∧ Even (k.1 + k.2)) R
    · simpa only [betaMinus, mul_comm R] using
        discrete_integrable_cosh (fun k => ¬ Even (k.1 + k.2)) R

end ExpandedFA.PartIV.KreinNonuniqueCoshSeries
