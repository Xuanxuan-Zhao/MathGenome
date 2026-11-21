import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.Stopping
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UIMartingaleClosure
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.TerminalStoppedRepresentation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- On the infinite layer the stopped sigma algebra contains all the information
of the terminal sigma algebra. -/
private theorem stoppedSigma_inter_top_iff {ℱ : Filtration ℕ m}
    {ρ : Ω → WithTop ℕ} (hρ : IsDiscreteStoppingTime ℱ ρ) (A : Set Ω) :
    MeasurableSet[stoppedSigma hρ] ({ω | ρ ω = ⊤} ∩ A) ↔
      MeasurableSet[terminalSigma ℱ] ({ω | ρ ω = ⊤} ∩ A) := by
  constructor
  · exact fun h => h.1
  · intro hA
    refine ⟨hA, fun n => ?_⟩
    change MeasurableSet[ℱ n] (({ω | ρ ω = ⊤} ∩ A) ∩
      {ω | ρ ω ≤ (n : WithTop ℕ)})
    have he : ({ω | ρ ω = ⊤} ∩ A) ∩ {ω | ρ ω ≤ (n : WithTop ℕ)} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨ht, _⟩, hn⟩
      simp [ht] at hn
    rw [he]
    exact @MeasurableSet.empty Ω (ℱ n)

/-- A closed process at an arbitrary stop is the conditional expectation of its
terminal variable, including on a possibly nonnull infinite layer. -/
theorem closed_martingale_fullStoppedValue (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hM : Adapted ℱ M) (hYm : Measurable[terminalSigma ℱ] Y)
    (hYi : Integrable Y μ) (hclose : ∀ n, M n =ᵐ[μ] μ[Y | ℱ n])
    (ρ : Ω → WithTop ℕ) (hρ : IsDiscreteStoppingTime ℱ ρ) :
    Measurable[stoppedSigma hρ] (fullStoppedValue M ρ Y) ∧
      Integrable (fullStoppedValue M ρ Y) μ ∧
      (∫ ω, |fullStoppedValue M ρ Y ω| ∂μ) ≤ ∫ ω, |Y ω| ∂μ ∧
      fullStoppedValue M ρ Y =ᵐ[μ] μ[Y | stoppedSigma hρ] := by
  have hrep : fullStoppedValue M ρ Y =ᵐ[μ] μ[Y | stoppedSigma hρ] := by
    have hcover : (Set.univ : Set Ω) = ⋃ i : WithTop ℕ, {ω | ρ ω = i} := by
      ext ω
      simp
    nth_rw 1 [← @Measure.restrict_univ Ω _ μ]
    rw [hcover, ae_eq_restrict_iUnion_iff]
    intro i
    cases i with
    | coe n =>
      have hc : μ[Y | stoppedSigma hρ] =ᵐ[μ.restrict {ω | ρ ω = (n : WithTop ℕ)}]
          μ[Y | ℱ n] := condExp_stopping_time_ae_eq_restrict_eq hρ n
      have he : M n =ᵐ[μ.restrict {ω | ρ ω = (n : WithTop ℕ)}] μ[Y | ℱ n] :=
        ae_restrict_of_ae (hclose n)
      filter_upwards [hc, he,
        ae_restrict_mem (μ := μ) (ℱ.le n _ (stopping_layer_measurable hρ n))]
        with ω hc he hω
      rw [fullStoppedValue_at_finite M ρ Y n ω hω, he, hc]
    | top =>
      have ht : MeasurableSet[stoppedSigma hρ] {ω | ρ ω = ⊤} :=
        (measurableSet_singleton (⊤ : WithTop ℕ)).preimage
          (MeasureTheory.IsStoppingTime.measurable hρ)
      have hc : μ[Y | stoppedSigma hρ] =ᵐ[μ.restrict {ω | ρ ω = ⊤}]
          μ[Y | terminalSigma ℱ] :=
        condExp_ae_eq_restrict_of_measurableSpace_eq_on
          (MeasureTheory.IsStoppingTime.measurableSpace_le hρ)
          (iSup_le ℱ.le) ht (stoppedSigma_inter_top_iff hρ)
      have hy : μ[Y | terminalSigma ℱ] = Y :=
        condExp_of_stronglyMeasurable (iSup_le ℱ.le) hYm.stronglyMeasurable hYi
      rw [hy] at hc
      filter_upwards [hc, ae_restrict_mem (μ := μ)
        (MeasureTheory.IsStoppingTime.measurableSpace_le hρ _ ht)] with ω hc hω
      rw [fullStoppedValue_at_top M ρ Y ω hω, hc]
  refine ⟨measurable_fullStoppedValue hρ M hM Y hYm,
    integrable_condExp.congr hrep.symm, ?_, hrep⟩
  calc
    (∫ ω, |fullStoppedValue M ρ Y ω| ∂μ) = ∫ ω, |μ[Y | stoppedSigma hρ] ω| ∂μ :=
      integral_congr_ae (hrep.fun_comp abs)
    _ ≤ ∫ ω, |Y ω| ∂μ := integral_abs_condExp_le Y

/-- The arbitrary-stop representation for a UI martingale and its fixed terminal
representative from `ui_martingale_terminal`. -/
theorem ui_martingale_fullStoppedValue (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ)
    (hM : IsMartingale M ℱ μ) (hui : Martingale.SourceUniformIntegrable μ M)
    (ρ : Ω → WithTop ℕ) (hρ : IsDiscreteStoppingTime ℱ ρ) :
    Measurable[stoppedSigma hρ] (fullStoppedValue M ρ (ℱ.limitProcess M μ)) ∧
      Integrable (fullStoppedValue M ρ (ℱ.limitProcess M μ)) μ ∧
      (∫ ω, |fullStoppedValue M ρ (ℱ.limitProcess M μ) ω| ∂μ) ≤
        ∫ ω, |ℱ.limitProcess M μ ω| ∂μ ∧
      fullStoppedValue M ρ (ℱ.limitProcess M μ) =ᵐ[μ]
        μ[ℱ.limitProcess M μ | stoppedSigma hρ] := by
  obtain ⟨hYm, hYi, _, _, hclose⟩ := ui_martingale_terminal μ ℱ M hM hui
  exact closed_martingale_fullStoppedValue μ ℱ M (ℱ.limitProcess M μ)
    hM.1 hYm hYi hclose ρ hρ

end P207
