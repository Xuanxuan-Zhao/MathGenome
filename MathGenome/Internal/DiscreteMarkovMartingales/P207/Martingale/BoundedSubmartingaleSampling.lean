import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.BoundedSubmartingaleSampling
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.Stopping

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

omit m in
/-- At a bounded time, the supplied value on the infinite layer is unused. -/
theorem fullStoppedValue_eq_stoppedValue_of_bounded
    (X : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) (Y : Ω → ℝ)
    {N : ℕ} (hb : ∀ ω, τ ω ≤ N) :
    fullStoppedValue X τ Y = MeasureTheory.stoppedValue X τ := by
  funext ω
  have ht : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hb ω)
  simp [fullStoppedValue, MeasureTheory.stoppedValue, ht]

/-- Bounded stopped values are measurable for the shared stopped sigma algebra. -/
theorem measurable_fullStoppedValue_bounded
    {ℱ : Filtration ℕ m} {τ : Ω → WithTop ℕ}
    (hτ : IsDiscreteStoppingTime ℱ τ) (X : ℕ → Ω → ℝ)
    (ha : Adapted ℱ X) (Y : Ω → ℝ) {N : ℕ} (hb : ∀ ω, τ ω ≤ N) :
    Measurable[stoppedSigma hτ] (fullStoppedValue X τ Y) := by
  have heq : fullStoppedValue X τ Y = fullStoppedValue X τ (fun _ => 0) := by
    rw [fullStoppedValue_eq_stoppedValue_of_bounded X τ Y hb,
      fullStoppedValue_eq_stoppedValue_of_bounded X τ (fun _ => 0) hb]
  rw [heq]
  exact measurable_fullStoppedValue hτ X ha _ measurable_const

/-- Testing bounded sampling on an event in the past of the earlier time.
The increment indicator intersects that event in an event at deterministic time k. -/
theorem submartingale_setIntegral_stoppedValue_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m} {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) {σ τ : Ω → WithTop ℕ}
    (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hle : ∀ ω, σ ω ≤ τ ω) {N : ℕ} (hb : ∀ ω, τ ω ≤ N)
    {A : Set Ω} (hA : MeasurableSet[stoppedSigma hσ] A) :
    (∫ ω in A, MeasureTheory.stoppedValue X σ ω ∂μ) ≤
      ∫ ω in A, MeasureTheory.stoppedValue X τ ω ∂μ := by
  have hσb : ∀ ω, σ ω ≤ N := fun ω => (hle ω).trans (hb ω)
  have hiσ := MeasureTheory.integrable_stoppedValue ℕ hσ hX.integrable hσb
  have hiτ := MeasureTheory.integrable_stoppedValue ℕ hτ hX.integrable hb
  have hC (k : ℕ) : MeasurableSet[ℱ k] {ω | σ ω ≤ k ∧ k < τ ω} := by
    simp_rw [Set.ofPred_and, ← not_le, ← Set.compl_ofPred]
    exact (hσ k).inter (hτ k).compl
  have hB (k : ℕ) : MeasurableSet[ℱ k] (A ∩ {ω | σ ω ≤ k ∧ k < τ ω}) := by
    have heq : A ∩ {ω | σ ω ≤ k ∧ k < τ ω} =
        (A ∩ {ω | σ ω ≤ k}) ∩ {ω | τ ω ≤ k}ᶜ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      tauto
    rw [heq]
    exact (hA.2 k).inter (hτ k).compl
  rw [← sub_nonneg, ← integral_sub' hiτ.integrableOn hiσ.integrableOn,
    MeasureTheory.stoppedValue_sub_eq_sum' hle hb]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_nonneg
    intro k _
    rw [setIntegral_indicator (ℱ.le k _ (hC k)),
      integral_sub' (hX.integrable (k + 1)).integrableOn
        (hX.integrable k).integrableOn, sub_nonneg]
    exact hX.setIntegral_le k.le_succ (hB k)
  · intro k _
    exact ((hX.integrable (k + 1)).sub (hX.integrable k)).indicator
      (ℱ.le k _ (hC k)) |>.integrableOn

/-- The full bounded optional sampling theorem of paper.tex, §7.1 (W39). -/
theorem bounded_submartingale_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ)
    (σ τ : Ω → WithTop ℕ)
    (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (N : ℕ) (hle : ∀ ω, σ ω ≤ τ ω) (hb : ∀ ω, τ ω ≤ N)
    (Yσ Yτ : Ω → ℝ) :
    Integrable (fullStoppedValue X σ Yσ) μ ∧
    Integrable (fullStoppedValue X τ Yτ) μ ∧
    Measurable[stoppedSigma hσ] (fullStoppedValue X σ Yσ) ∧
    Measurable[stoppedSigma hτ] (fullStoppedValue X τ Yτ) ∧
    fullStoppedValue X σ Yσ ≤ᵐ[μ] μ[fullStoppedValue X τ Yτ | stoppedSigma hσ] ∧
    (∫ ω, fullStoppedValue X σ Yσ ω ∂μ) ≤
      ∫ ω, fullStoppedValue X τ Yτ ω ∂μ := by
  have hσb : ∀ ω, σ ω ≤ N := fun ω => (hle ω).trans (hb ω)
  have hiσ := integrable_fullStoppedValue_bounded hσ X Yσ μ hX.2.1 N hσb
  have hiτ := integrable_fullStoppedValue_bounded hτ X Yτ μ hX.2.1 N hb
  have hmσ := measurable_fullStoppedValue_bounded hσ X hX.1 Yσ hσb
  have hmτ := measurable_fullStoppedValue_bounded hτ X hX.1 Yτ hb
  have hm : stoppedSigma hσ ≤ m := MeasureTheory.IsStoppingTime.measurableSpace_le hσ
  have htest : ∀ A, MeasurableSet[stoppedSigma hσ] A →
      (∫ ω in A, fullStoppedValue X σ Yσ ω ∂μ) ≤
        ∫ ω in A, fullStoppedValue X τ Yτ ω ∂μ := by
    intro A hA
    rw [fullStoppedValue_eq_stoppedValue_of_bounded X σ Yσ hσb,
      fullStoppedValue_eq_stoppedValue_of_bounded X τ Yτ hb]
    exact submartingale_setIntegral_stoppedValue_le μ
      ((submartingale_iff_library μ ℱ X).mp hX) hσ hτ hle hb hA
  refine ⟨hiσ, hiτ, hmσ, hmτ, ?_, ?_⟩
  · apply ae_le_of_ae_le_trim (hm := hm)
    apply ae_le_of_forall_setIntegral_le (hiσ.trim hm hmσ.stronglyMeasurable)
      (integrable_condExp.trim hm stronglyMeasurable_condExp)
    intro A hA _
    rw [← setIntegral_trim hm hmσ.stronglyMeasurable hA,
      ← setIntegral_trim hm stronglyMeasurable_condExp hA,
      setIntegral_condExp hm hiτ hA]
    exact htest A hA
  · simpa only [setIntegral_univ] using htest Set.univ MeasurableSet.univ

end P207
