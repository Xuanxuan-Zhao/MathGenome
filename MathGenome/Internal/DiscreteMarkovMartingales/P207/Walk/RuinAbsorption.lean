import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.RuinAbsorption
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.HittingProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory Filter
open scoped ENNReal

namespace P207.Walk
noncomputable section

namespace RuinAbsorption
abbrev kernel : RuinAbsorptionSpec.kernelType := ruinKernel
abbrev time : RuinAbsorptionSpec.timeType := ruinTime
end RuinAbsorption

theorem ruinKernel_boundary : RuinAbsorptionSpec.kernel_boundary := by
  intro N p hp hp1 i hi
  exact ite_eq_left hi

theorem ruinKernel_interior : RuinAbsorptionSpec.kernel_interior := by
  intro N p hp hp1 i j hi
  change ¬ (i.val = 0 ∨ i.val = N) at hi
  unfold ruinKernel
  rw [ite_eq_right hi, PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, ruinCoin, PMF.ofFintype_apply]

/-- Integrating a row against a nonnegative function gives its two move terms. -/
theorem ruinKernel_action (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∉ ruinBoundary N) (f : RuinState N → ℝ≥0∞) :
    Markov.action (ruinKernel N p hp hp1) f i =
      ENNReal.ofReal p * f (ruinRight i) +
      ENNReal.ofReal (1 - p) * f (ruinLeft i) := by
  unfold Markov.action
  simp_rw [ruinKernel_interior N p hp hp1 i _ hi, add_mul, ite_mul, zero_mul]
  rw [ENNReal.tsum_add]
  simp

private theorem measurableSet_ruinTime_gt (N n : ℕ) :
    MeasurableSet {ω | (n : WithTop ℕ) < ruinTime N ω} := by
  simpa only [Set.compl_ofPred, not_le, ruinTime] using
    (Markov.measurableSet_hittingTime_le (ruinBoundary N) n).compl

local instance ruin_statePathLaw_probability (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) : IsProbabilityMeasure (Markov.statePathLaw (ruinKernel N p hp hp1) i) :=
  Markov.pathLaw_probability _ (PMF.pure i)

private def survival (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℕ) (i : RuinState N) : ℝ≥0∞ :=
  Markov.statePathLaw (ruinKernel N p hp hp1) i {ω | (n : WithTop ℕ) < ruinTime N ω}

private theorem survival_boundary (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∈ ruinBoundary N) (n : ℕ) :
    survival N p hp hp1 n i = 0 := by
  unfold survival
  rw [← measure_empty (μ := Markov.statePathLaw (ruinKernel N p hp hp1) i)]
  apply measure_congr
  filter_upwards [Markov.coordinate_zero_ae (ruinKernel N p hp hp1) i] with ω hω
  have ht : ruinTime N ω ≤ (0 : ℕ) :=
    (Markov.hittingTime_le_iff _ ω 0).mpr ⟨0, le_rfl, hω ▸ hi⟩
  have hn : (0 : WithTop ℕ) ≤ n := WithTop.coe_le_coe.mpr (Nat.zero_le n)
  apply propext
  exact iff_false_intro (not_lt.mpr (ht.trans hn))

private theorem survival_zero (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∉ ruinBoundary N) :
    survival N p hp hp1 0 i = 1 := by
  unfold survival
  apply (mem_ae_iff_prob_eq_one (measurableSet_ruinTime_gt N 0)).mp
  filter_upwards [Markov.coordinate_zero_ae (ruinKernel N p hp hp1) i] with ω hω
  change (0 : WithTop ℕ) < ruinTime N ω
  rw [← not_le]
  intro ht
  rcases (Markov.hittingTime_le_iff (ruinBoundary N) ω 0).mp ht with ⟨k, hk, hkA⟩
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  exact hi (hω ▸ hkA)

private theorem survival_step (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∉ ruinBoundary N) (n : ℕ) :
    survival N p hp hp1 (n + 1) i =
      ENNReal.ofReal p * survival N p hp hp1 n (ruinRight i) +
      ENNReal.ofReal (1 - p) * survival N p hp hp1 n (ruinLeft i) := by
  rw [← ruinKernel_action N p hp hp1 i hi]
  change Markov.statePathLaw _ i _ = ∑' j, _ * Markov.statePathLaw _ j _
  rw [← Markov.hitting_first_step _ i _
    (measurableSet_ruinTime_gt N n)]
  apply measure_congr
  filter_upwards [Markov.coordinate_zero_ae (ruinKernel N p hp hp1) i] with ω hω
  apply propext
  simp only [← not_le, ruinTime, Markov.hittingTime_le_iff]
  apply not_congr
  constructor
  · rintro ⟨k, hk, hkA⟩
    cases k with
    | zero => exact (hi (hω ▸ hkA)).elim
    | succ k => exact ⟨k, Nat.le_of_succ_le_succ hk, by simpa [Nat.add_comm] using hkA⟩
  · rintro ⟨k, hk, hkA⟩
    exact ⟨1 + k, by omega, hkA⟩

private def partialMean (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℕ) (i : RuinState N) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range n, survival N p hp hp1 k i

private theorem partialMean_boundary (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∈ ruinBoundary N) (n : ℕ) :
    partialMean N p hp hp1 n i = 0 := by
  simp [partialMean, survival_boundary N p hp hp1 i hi]

private theorem partialMean_step (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∉ ruinBoundary N) (n : ℕ) :
    partialMean N p hp hp1 (n + 1) i = 1 +
      ENNReal.ofReal p * partialMean N p hp hp1 n (ruinRight i) +
      ENNReal.ofReal (1 - p) * partialMean N p hp hp1 n (ruinLeft i) := by
  unfold partialMean
  rw [Finset.sum_range_succ']
  simp_rw [survival_step N p hp hp1 i hi]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    survival_zero N p hp hp1 i hi]
  ac_rfl

/-- A finite nonnegative potential dominating the expected remaining lifetime. -/
def ruinPotential (N : ℕ) (p : ℝ) (i : RuinState N) : ℝ :=
  (2 / p) ^ N - (2 / p) ^ i.val

private theorem potential_nonneg (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) : 0 ≤ ruinPotential N p i := by
  have ha : 1 ≤ 2 / p := (le_div_iff₀ hp).mpr (by linarith)
  exact sub_nonneg.mpr (pow_le_pow_right₀ ha (Nat.le_of_lt_succ i.isLt))

/-- The potential has a unit downward drift before hitting the boundary. -/
private theorem potential_drift (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∉ ruinBoundary N) :
    1 + p * ruinPotential N p (ruinRight i) +
      (1 - p) * ruinPotential N p (ruinLeft i) ≤ ruinPotential N p i := by
  have ha : 1 ≤ 2 / p := (le_div_iff₀ hp).mpr (by linarith)
  have hpow : 1 ≤ (2 / p) ^ i.val := one_le_pow₀ ha
  have hleft : 0 ≤ (1 - p) * (2 / p) ^ (i.val - 1) := by positivity
  have hright : p * (2 / p) ^ (i.val + 1) = 2 * (2 / p) ^ i.val := by
    rw [pow_succ]
    field_simp
  have hr : i.val + 1 ≤ N := by
    have his := i.isLt
    change ¬ (i.val = 0 ∨ i.val = N) at hi
    omega
  unfold ruinPotential ruinRight ruinLeft
  simp only [min_eq_left hr]
  nlinarith [hright]

private theorem partialMean_le_potential (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (n : ℕ) (i : RuinState N) :
    partialMean N p hp hp1 n i ≤ ENNReal.ofReal (ruinPotential N p i) := by
  induction n generalizing i with
  | zero => simp [partialMean]
  | succ n ih =>
    by_cases hi : i ∈ ruinBoundary N
    · rw [partialMean_boundary N p hp hp1 i hi]
      exact zero_le
    · rw [partialMean_step N p hp hp1 i hi]
      calc
        _ ≤ 1 + ENNReal.ofReal p * ENNReal.ofReal (ruinPotential N p (ruinRight i)) +
            ENNReal.ofReal (1 - p) * ENNReal.ofReal (ruinPotential N p (ruinLeft i)) := by
          gcongr <;> exact ih _
        _ = ENNReal.ofReal (1 + p * ruinPotential N p (ruinRight i) +
            (1 - p) * ruinPotential N p (ruinLeft i)) := by
          have hR := potential_nonneg N p hp hp1 (ruinRight i)
          have hL := potential_nonneg N p hp hp1 (ruinLeft i)
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one,
            ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul (sub_nonneg.mpr hp1.le)]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (potential_drift N p hp hp1 i hi)

/-- The identity is pointwise, even at infinite time. -/
private theorem extendedTime_eq_tsum (t : WithTop ℕ) :
    ENat.toENNReal t = ∑' n : ℕ, if (n : WithTop ℕ) < t then 1 else 0 := by
  induction t using WithTop.recTopCoe with
  | top =>
    change (∞ : ℝ≥0∞) = ∑' n : ℕ, if (n : WithTop ℕ) < ⊤ then 1 else 0
    calc
      (∞ : ℝ≥0∞) = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
        (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ = _ := tsum_congr fun n => (ite_eq_left (WithTop.coe_lt_top n)).symm
  | coe k =>
    change (k : ℝ≥0∞) = ∑' n : ℕ, if (n : WithTop ℕ) < (k : WithTop ℕ) then 1 else 0
    rw [tsum_eq_sum (s := Finset.range k)]
    · calc
        (k : ℝ≥0∞) = ∑ _n ∈ Finset.range k, (1 : ℝ≥0∞) := by simp
        _ = _ := Finset.sum_congr rfl (fun n hn => (ite_eq_left (WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hn))).symm)
    · intro n hn
      exact ite_eq_right (fun h => hn (Finset.mem_range.mpr (WithTop.coe_lt_coe.mp h)))

/-- The usual tail-sum identity for the actual shared hitting time. -/
theorem ruinTime_expectation_eq_tsum (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) :
    (∫⁻ ω, ENat.toENNReal (ruinTime N ω)
      ∂Markov.statePathLaw (ruinKernel N p hp hp1) i) =
    ∑' n : ℕ, Markov.statePathLaw (ruinKernel N p hp hp1) i
      {ω | (n : WithTop ℕ) < ruinTime N ω} := by
  simp_rw [extendedTime_eq_tsum]
  have hm (n : ℕ) : Measurable (fun ω : ℕ → RuinState N =>
      if (n : WithTop ℕ) < ruinTime N ω then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_ruinTime_gt N n) measurable_const measurable_const
  rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
  apply tsum_congr
  intro n
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
    (lintegral_indicator_one (μ := Markov.statePathLaw (ruinKernel N p hp hp1) i)
      (measurableSet_ruinTime_gt N n))

/-- A concrete finite upper bound on the extended expectation. -/
theorem ruinTime_expectation_le (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) :
    (∫⁻ ω, ENat.toENNReal (ruinTime N ω)
      ∂Markov.statePathLaw (ruinKernel N p hp hp1) i) ≤
    ENNReal.ofReal (ruinPotential N p i) := by
  rw [ruinTime_expectation_eq_tsum]
  exact ENNReal.tsum_le_of_sum_range_le (fun n => partialMean_le_potential N p hp hp1 n i)

theorem ruinTime_finite_mean : RuinAbsorptionSpec.absorption_finite_mean := by
  intro N _ p hp hp1 i
  exact (ruinTime_expectation_le N p hp hp1 i).trans_lt ENNReal.ofReal_lt_top

theorem ruinTime_ae_finite : RuinAbsorptionSpec.absorption_ae_finite := by
  intro N hN p hp hp1 i
  have hm : Measurable (fun ω : ℕ → RuinState N => ENat.toENNReal (ruinTime N ω)) := by
    simp_rw [extendedTime_eq_tsum]
    apply Measurable.tsum
    intro n
    exact Measurable.ite (measurableSet_ruinTime_gt N n) measurable_const measurable_const
  have ha := ae_lt_top hm (ruinTime_finite_mean N hN p hp hp1 i).ne
  filter_upwards [ha] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

end
end P207.Walk
