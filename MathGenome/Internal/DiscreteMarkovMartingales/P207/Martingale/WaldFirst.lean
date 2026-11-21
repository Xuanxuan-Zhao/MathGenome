import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.WaldFirst
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.ControlledIncrementSampling
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped MeasureTheory ENNReal
universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Algebraic identification with the sum of the centered increments. -/
theorem waldCenteredSum_eq_sum (P : Measure Ω) (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    waldCenteredSum P Y n ω = ∑ k ∈ Finset.range n, (Y (k + 1) ω - waldMean P Y) := by
  simp [waldCenteredSum, waldSum, Finset.sum_sub_distrib, mul_comm]

/-- The increment of the centered sum is the centered next observation. -/
theorem waldCenteredSum_increment (P : Measure Ω) (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    waldCenteredSum P Y (k + 1) ω - waldCenteredSum P Y k ω =
      Y (k + 1) ω - waldMean P Y := by
  simp only [waldCenteredSum, waldSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  ring

theorem wald_centered_sum_martingale
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ)
    (hi : ∀ k, 1 ≤ k → Integrable (Y k) P)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (Y k))
    (hd : ∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P)
    (hind : ∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) :
    IsMartingale (waldCenteredSum P Y) ℱ P := by
  have hc := centered_independent_sum P ℱ (fun k ω => Y k ω - waldMean P Y)
    (fun k hk => (hi k hk).sub (integrable_const _))
    (fun k hk => (ha k hk).sub measurable_const)
    (fun k hk => by
      rw [integral_sub (hi k hk) (integrable_const _), (hd k hk).integral_eq]
      simp [waldMean])
    (fun k hk => ProbabilityTheory.indep_of_indep_of_le_left (hind k hk)
      (MeasurableSpace.comap_le_comap_of_eq_comp
        (fun x : ℝ => x - waldMean P Y) (measurable_id.sub measurable_const) rfl))
  have heq : waldCenteredSum P Y =
      (fun n ω => ∑ k ∈ Finset.range n, (Y (k + 1) ω - waldMean P Y)) := by
    funext n ω
    exact waldCenteredSum_eq_sum P Y n ω
  rw [heq]
  exact hc

theorem wald_centered_increment_condExp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ)
    (_hi : ∀ k, 1 ≤ k → Integrable (Y k) P)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (Y k))
    (hd : ∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P)
    (hind : ∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) (k : ℕ) :
    P[(fun ω => |waldCenteredSum P Y (k + 1) ω -
      waldCenteredSum P Y k ω|) | ℱ k] =ᵐ[P]
      fun _ => ∫ ω, |Y 1 ω - waldMean P Y| ∂P := by
  have hm : Measurable (Y (k + 1)) :=
    (ha (k + 1) (by omega)).mono (ℱ.le _) le_rfl
  have hbase : Measurable[MeasurableSpace.comap (Y (k + 1)) inferInstance]
      (Y (k + 1)) := measurable_iff_comap_le.mpr le_rfl
  have habs : Measurable[MeasurableSpace.comap (Y (k + 1)) inferInstance]
      (fun ω => |Y (k + 1) ω - waldMean P Y|) :=
    measurable_abs.comp (hbase.sub measurable_const)
  have hce := condExp_indep_eq hm.comap_le (ℱ.le k) habs.stronglyMeasurable
    (by simpa using hind (k + 1) (by omega))
  have he : (∫ ω, |Y (k + 1) ω - waldMean P Y| ∂P) =
      ∫ ω, |Y 1 ω - waldMean P Y| ∂P :=
    ((hd (k + 1) (by omega)).comp
    ((measurable_id.sub measurable_const).abs :
      Measurable (fun x : ℝ => |x - waldMean P Y|))).integral_eq
  simpa only [waldCenteredSum_increment, he] using hce

/-- Decomposition of the stopped sum, including the explicit zero convention at infinity. -/
theorem wald_stopped_decomposition (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (τ : Ω → WithTop ℕ) :
    fullStoppedValue (waldSum Y) τ (fun _ => 0) =
      fun ω => fullStoppedValue (waldCenteredSum P Y) τ (fun _ => 0) ω +
        waldMean P Y * waldTimeReal τ ω := by
  funext ω
  cases ht : τ ω with
  | top =>
    rw [fullStoppedValue_at_top _ _ _ _ ht, fullStoppedValue_at_top _ _ _ _ ht]
    have htime : waldTimeReal τ ω = 0 := by
      unfold waldTimeReal
      rw [ht]
      change (⊤ : ℝ≥0∞).toReal = 0
      exact ENNReal.toReal_top
    rw [htime, mul_zero, add_zero]
  | coe n =>
    rw [fullStoppedValue_at_finite _ _ _ _ _ ht, fullStoppedValue_at_finite _ _ _ _ _ ht]
    have htime : waldTimeReal τ ω = n := by
      unfold waldTimeReal
      rw [ht]
      change (n : ℝ≥0∞).toReal = n
      exact ENNReal.toReal_natCast n
    rw [htime]
    simp [waldCenteredSum]

theorem wald_first
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ)
    (hi : ∀ k, 1 ≤ k → Integrable (Y k) P)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (Y k))
    (hd : ∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P)
    (hind : ∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hmean : (∫⁻ ω, ENat.toENNReal (τ ω) ∂P) < ⊤) :
    (∀ᵐ ω ∂P, τ ω < ⊤) ∧
    Integrable (waldTimeReal τ) P ∧
    (∫ ω, waldTimeReal τ ω ∂P) = (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal ∧
    Integrable (fullStoppedValue (waldSum Y) τ (fun _ => 0)) P ∧
    (∫ ω, fullStoppedValue (waldSum Y) τ (fun _ => 0) ω ∂P) =
      waldMean P Y * (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal := by
  have hM := wald_centered_sum_martingale P ℱ Y hi ha hd hind
  have hC : 0 ≤ ∫ ω, |Y 1 ω - waldMean P Y| ∂P :=
    integral_nonneg (fun _ => abs_nonneg _)
  obtain ⟨hfinite, hstopM, hEM⟩ := controlled_increment_sampling P ℱ
    (waldCenteredSum P Y) hM τ hτ hmean
    (∫ ω, |Y 1 ω - waldMean P Y| ∂P) hC
    (fun k => (wald_centered_increment_condExp P ℱ Y hi ha hd hind k).le)
  have hm : Measurable (fun ω => ENat.toENNReal (τ ω)) :=
    (measurable_of_countable _).comp (MeasureTheory.IsStoppingTime.measurable' hτ)
  have ht : Integrable (waldTimeReal τ) P :=
    integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmean.ne
  have het : (∫ ω, waldTimeReal τ ω ∂P) =
      (∫⁻ ω, ENat.toENNReal (τ ω) ∂P).toReal :=
    integral_toReal hm.aemeasurable (ae_lt_top hm hmean.ne)
  have hEM0 : (∫ ω, fullStoppedValue (waldCenteredSum P Y) τ (fun _ => 0) ω ∂P) = 0 := by
    simpa [waldCenteredSum, waldSum] using hEM
  have hscaled := ht.const_mul (waldMean P Y)
  refine ⟨hfinite, ht, het, ?_, ?_⟩
  · rw [wald_stopped_decomposition P Y τ]
    exact hstopM.add hscaled
  · rw [wald_stopped_decomposition P Y τ, integral_add hstopM hscaled,
      hEM0, zero_add, integral_const_mul, het]

end P207
