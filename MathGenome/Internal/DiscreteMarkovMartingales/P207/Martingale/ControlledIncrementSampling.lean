import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.ControlledIncrementSampling
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.BoundedMartingaleSampling
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal
universe u
namespace P207

/-- Tail-count representation, including an infinite stopping time. -/
theorem stopping_time_tail_count (t : WithTop ℕ) :
    (∑' k : ℕ, if (k : WithTop ℕ) < t then (1 : ℝ≥0∞) else 0) =
      ENat.toENNReal t := by
  classical
  cases t with
  | top =>
    change (∑' _ : ℕ, (1 : ℝ≥0∞)) = ⊤
    simp
  | coe n =>
    change (∑' k : ℕ, if (k : WithTop ℕ) < (n : WithTop ℕ) then (1 : ℝ≥0∞) else 0) = (n : ℝ≥0∞)
    rw [tsum_eq_sum (s := Finset.range n)]
    · calc
        _ = ∑ _k ∈ Finset.range n, (1 : ℝ≥0∞) :=
          Finset.sum_congr rfl (fun k hk => ite_eq_left (WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hk)))
        _ = _ := by simp
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp [hk]

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- The discrete tail formula for the extended expectation. -/
theorem stopping_time_tail_expectation (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ) :
    (∑' k : ℕ, μ {ω | (k : WithTop ℕ) < τ ω}) =
      ∫⁻ ω, ENat.toENNReal (τ ω) ∂μ := by
  classical
  have hm (k : ℕ) : MeasurableSet {ω | (k : WithTop ℕ) < τ ω} := by
    simpa only [← not_le, ← Set.compl_ofPred] using ℱ.le k _ (hτ k).compl
  calc
    _ = ∑' k : ℕ, ∫⁻ ω, {ω | (k : WithTop ℕ) < τ ω}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      congr 1
      ext k
      simp [lintegral_indicator, hm k]
    _ = ∫⁻ ω, ∑' k : ℕ, {ω | (k : WithTop ℕ) < τ ω}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω ∂μ :=
      (lintegral_tsum (fun k => (measurable_const.indicator (hm k)).aemeasurable)).symm
    _ = _ := by
      apply lintegral_congr
      intro ω
      simpa only [Set.indicator, Set.mem_ofPred_eq] using stopping_time_tail_count (τ ω)

/-- Finite extended mean forces the stopping time to be finite almost surely. -/
theorem stopping_time_ae_finite_of_mean (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hmean : (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) < ⊤) :
    ∀ᵐ ω ∂μ, τ ω < ⊤ := by
  have hm : Measurable (fun ω => ENat.toENNReal (τ ω)) := by
    have ht : Measurable τ := MeasureTheory.IsStoppingTime.measurable' hτ
    exact (measurable_of_countable _).comp ht
  filter_upwards [ae_lt_top hm hmean.ne] with ω hω
  exact ENat.toENNReal_lt_top.mp hω

namespace ControlledIncrement

/-- The predictable increment retained before the stopping time. -/
noncomputable def stoppedIncrement (M : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (k : ℕ) : Ω → ℝ :=
  {ω | (k : WithTop ℕ) < τ ω}.indicator (fun ω => M (k + 1) ω - M k ω)

theorem tail_measurable {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (k : ℕ) :
    MeasurableSet[ℱ k] {ω | (k : WithTop ℕ) < τ ω} := by
  simpa only [← not_le, ← Set.compl_ofPred] using (hτ k).compl

theorem integrable_stoppedIncrement (μ : Measure Ω) (ℱ : Filtration ℕ m)
    (M : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : IsDiscreteStoppingTime ℱ τ) (hi : ∀ k, Integrable (M k) μ) (k : ℕ) :
    Integrable (stoppedIncrement M τ k) μ :=
  ((hi (k + 1)).sub (hi k)).indicator (ℱ.le k _ (tail_measurable hτ k))

/-- The conditional bound controls each retained absolute increment. -/
theorem lintegral_stoppedIncrement_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (hτ : IsDiscreteStoppingTime ℱ τ) (hi : ∀ k, Integrable (M k) μ)
    (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    (hb : μ[(fun ω => |M (k + 1) ω - M k ω|) | ℱ k] ≤ᵐ[μ] fun _ => C) :
    (∫⁻ ω, ‖stoppedIncrement M τ k ω‖ₑ ∂μ) ≤
      ENNReal.ofReal C * μ {ω | (k : WithTop ℕ) < τ ω} := by
  have hs := tail_measurable hτ k
  have hs' := ℱ.le k _ hs
  have hi' := integrable_stoppedIncrement μ ℱ M τ hτ hi k
  have habs : Integrable (fun ω => |M (k + 1) ω - M k ω|) μ :=
    ((hi (k + 1)).sub (hi k)).abs
  have he : (∫ ω, ‖stoppedIncrement M τ k ω‖ ∂μ) ≤
      C * (μ {ω | (k : WithTop ℕ) < τ ω}).toReal := by
    calc
      _ = ∫ ω in {ω | (k : WithTop ℕ) < τ ω}, |M (k + 1) ω - M k ω| ∂μ := by
        simp only [stoppedIncrement, norm_indicator_eq_indicator_norm, Real.norm_eq_abs]
        exact integral_indicator hs'
      _ = ∫ ω in {ω | (k : WithTop ℕ) < τ ω},
          μ[(fun ω => |M (k + 1) ω - M k ω|) | ℱ k] ω ∂μ :=
        (setIntegral_condExp (ℱ.le k) habs hs).symm
      _ ≤ ∫ _ in {ω | (k : WithTop ℕ) < τ ω}, C ∂μ := by
        apply integral_mono_ae integrable_condExp.integrableOn (integrable_const C).integrableOn
        exact ae_restrict_of_ae hb
      _ = _ := by simp [measureReal_def, mul_comm]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi']
  calc
    _ ≤ ENNReal.ofReal (C * (μ {ω | (k : WithTop ℕ) < τ ω}).toReal) :=
      ENNReal.ofReal_le_ofReal he
    _ = _ := by rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Each retained signed increment still has mean zero. -/
theorem integral_stoppedIncrement_eq_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ) (k : ℕ) :
    (∫ ω, stoppedIncrement M τ k ω ∂μ) = 0 := by
  have hs := tail_measurable hτ k
  have he := ((martingale_iff_library μ ℱ M).mp hM).setIntegral_eq k.le_succ hs
  rw [stoppedIncrement, integral_indicator (ℱ.le k _ hs),
    integral_sub (hM.2.1 (k + 1)).integrableOn (hM.2.1 k).integrableOn]
  exact sub_eq_zero.mpr he.symm

/-- At a finite stop the retained increments form a finite telescoping sum. -/
theorem hasSum_stoppedIncrement_of_finite (M : ℕ → Ω → ℝ)
    (τ : Ω → WithTop ℕ) (ω : Ω) (n : ℕ) (ht : τ ω = n) :
    HasSum (fun k => stoppedIncrement M τ k ω)
      (fullStoppedValue M τ (fun _ => 0) ω - M 0 ω) := by
  classical
  have he : (∑ k ∈ Finset.range n, stoppedIncrement M τ k ω) = M n ω - M 0 ω := by
    calc
      _ = ∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Set.indicator_of_mem
        change (k : WithTop ℕ) < τ ω
        rw [ht]
        exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hk)
      _ = _ := Finset.sum_range_sub (fun k => M k ω) n
  rw [fullStoppedValue_at_finite M τ (fun _ => 0) n ω ht, ← he]
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  have hkn : ¬ k < n := by simpa using hk
  simp [stoppedIncrement, ht, Set.indicator, hkn]

/-- Absolute integrability of a series gives integrability of any measurable
almost-everywhere sum. This also records the required limit-interchange bound. -/
theorem integrable_of_hasSum (μ : Measure Ω) (Z : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hZ : ∀ k, AEStronglyMeasurable (Z k) μ) (hf : AEStronglyMeasurable f μ)
    (hs : ∀ᵐ ω ∂μ, HasSum (fun k => Z k ω) (f ω))
    (hb : (∑' k, ∫⁻ ω, ‖Z k ω‖ₑ ∂μ) < ⊤) : Integrable f μ := by
  refine ⟨hf, ?_⟩
  change (∫⁻ ω, ‖f ω‖ₑ ∂μ) < ⊤
  calc
    _ ≤ ∫⁻ ω, ∑' k, ‖Z k ω‖ₑ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hs] with ω hω
      exact hω.enorm_le_of_bounded ENNReal.summable.hasSum (fun _ => le_rfl)
    _ = ∑' k, ∫⁻ ω, ‖Z k ω‖ₑ ∂μ := lintegral_tsum (fun k => (hZ k).enorm)
    _ < ⊤ := hb

end ControlledIncrement
/-- Optional sampling at an integrable time under a uniform conditional
expected absolute-increment bound (paper.tex §7.4). -/
theorem controlled_increment_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hmean : (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, μ[(fun ω => |M (k + 1) ω - M k ω|) | ℱ k] ≤ᵐ[μ] fun _ => C) :
    (∀ᵐ ω ∂μ, τ ω < ⊤) ∧
    Integrable (fullStoppedValue M τ (fun _ => 0)) μ ∧
    (∫ ω, fullStoppedValue M τ (fun _ => 0) ω ∂μ) = ∫ ω, M 0 ω ∂μ := by
  have hfinite := stopping_time_ae_finite_of_mean μ ℱ τ hτ hmean
  let Z := ControlledIncrement.stoppedIncrement M τ
  have hZi (k : ℕ) : Integrable (Z k) μ :=
    ControlledIncrement.integrable_stoppedIncrement μ ℱ M τ hτ hM.2.1 k
  have hsum_norm : (∑' k, ∫⁻ ω, ‖Z k ω‖ₑ ∂μ) < ⊤ := by
    calc
      _ ≤ ∑' k : ℕ, ENNReal.ofReal C * μ {ω | (k : WithTop ℕ) < τ ω} := by
        apply ENNReal.tsum_le_tsum
        intro k
        exact ControlledIncrement.lintegral_stoppedIncrement_le μ ℱ M τ hτ hM.2.1 C hC k (hb k)
      _ = ENNReal.ofReal C * (∑' k : ℕ, μ {ω | (k : WithTop ℕ) < τ ω}) :=
        ENNReal.tsum_mul_left
      _ = ENNReal.ofReal C * (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) := by
        rw [stopping_time_tail_expectation μ ℱ τ hτ]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmean
  have hs : ∀ᵐ ω ∂μ, HasSum (fun k => Z k ω)
      (fullStoppedValue M τ (fun _ => 0) ω - M 0 ω) := by
    filter_upwards [hfinite] with ω hω
    cases ht : τ ω with
    | top => simp [ht] at hω
    | coe n => exact ControlledIncrement.hasSum_stoppedIncrement_of_finite M τ ω n ht
  have hm : Measurable (fullStoppedValue M τ (fun _ => 0)) :=
    (measurable_fullStoppedValue hτ M hM.1 (fun _ => 0) measurable_const).mono
      (MeasureTheory.IsStoppingTime.measurableSpace_le hτ) le_rfl
  have hdiff : Integrable (fun ω => fullStoppedValue M τ (fun _ => 0) ω - M 0 ω) μ :=
    ControlledIncrement.integrable_of_hasSum μ Z _ (fun k => (hZi k).1)
      (hm.aestronglyMeasurable.sub (hM.2.1 0).1) hs hsum_norm
  have hstop : Integrable (fullStoppedValue M τ (fun _ => 0)) μ := by
    have hi := hdiff.add (hM.2.1 0)
    convert hi using 1
    ext ω
    simp
  refine ⟨hfinite, hstop, ?_⟩
  have heq : (fun ω => ∑' k, Z k ω) =ᵐ[μ]
      (fun ω => fullStoppedValue M τ (fun _ => 0) ω - M 0 ω) := hs.mono (fun _ h => h.tsum_eq)
  have hint : (∫ ω, fullStoppedValue M τ (fun _ => 0) ω - M 0 ω ∂μ) = 0 := by
    rw [← integral_congr_ae heq, integral_tsum (fun k => (hZi k).1) hsum_norm.ne]
    have hz (k : ℕ) : (∫ ω, Z k ω ∂μ) = 0 :=
      ControlledIncrement.integral_stoppedIncrement_eq_zero μ ℱ M hM τ hτ k
    simp only [hz, tsum_zero]
  rw [integral_sub hstop (hM.2.1 0)] at hint
  exact sub_eq_zero.mp hint

/-- The bounded-increment sufficient condition follows by conditional monotonicity. -/
theorem bounded_increment_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hmean : (∫⁻ ω, ENat.toENNReal (τ ω) ∂μ) < ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k, ∀ᵐ ω ∂μ, |M (k + 1) ω - M k ω| ≤ C) :
    (∀ᵐ ω ∂μ, τ ω < ⊤) ∧
    Integrable (fullStoppedValue M τ (fun _ => 0)) μ ∧
    (∫ ω, fullStoppedValue M τ (fun _ => 0) ω ∂μ) = ∫ ω, M 0 ω ∂μ := by
  apply controlled_increment_sampling μ ℱ M hM τ hτ hmean C hC
  intro k
  have hi : Integrable (fun ω => |M (k + 1) ω - M k ω|) μ :=
    ((hM.2.1 (k + 1)).sub (hM.2.1 k)).abs
  have hc := condExp_mono (m := ℱ k) hi (integrable_const C) (hb k)
  simpa only [condExp_const (ℱ.le k) C] using hc

end P207
