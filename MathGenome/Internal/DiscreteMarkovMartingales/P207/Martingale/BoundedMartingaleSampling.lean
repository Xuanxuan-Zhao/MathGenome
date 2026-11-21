import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.BoundedMartingaleSampling
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.BoundedSubmartingaleSampling

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

/-- Negating both the process and its supplied terminal value negates the full
stopped value, including on the infinite layer. -/
theorem fullStoppedValue_neg {Ω : Type u} (M : ℕ → Ω → ℝ)
    (τ : Ω → WithTop ℕ) (Y : Ω → ℝ) :
    fullStoppedValue (-M) τ (-Y) = -fullStoppedValue M τ Y := by
  funext ω
  simp only [fullStoppedValue, Pi.neg_apply]
  split <;> rfl

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- The bounded martingale sampling identity, with integrability and
measurability at both stops, for all finite deterministic horizons. -/
theorem bounded_martingale_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (σ τ : Ω → WithTop ℕ)
    (hσ : IsDiscreteStoppingTime ℱ σ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (N : ℕ) (hle : ∀ ω, σ ω ≤ τ ω) (hb : ∀ ω, τ ω ≤ N)
    (Yσ Yτ : Ω → ℝ) :
    Integrable (fullStoppedValue M σ Yσ) μ ∧
    Integrable (fullStoppedValue M τ Yτ) μ ∧
    Measurable[stoppedSigma hσ] (fullStoppedValue M σ Yσ) ∧
    Measurable[stoppedSigma hτ] (fullStoppedValue M τ Yτ) ∧
    μ[fullStoppedValue M τ Yτ | stoppedSigma hσ] =ᵐ[μ]
      fullStoppedValue M σ Yσ ∧
    (∫ ω, fullStoppedValue M τ Yτ ω ∂μ) =
      ∫ ω, fullStoppedValue M σ Yσ ω ∂μ := by
  have hlib := (martingale_iff_library μ ℱ M).mp hM
  have hsub := (submartingale_iff_library μ ℱ M).mpr hlib.submartingale
  have hneg := (submartingale_iff_library μ ℱ (-M)).mpr hlib.neg.submartingale
  obtain ⟨hiσ, hiτ, hmσ, hmτ, hlo, he⟩ :=
    bounded_submartingale_sampling μ ℱ M hsub σ τ hσ hτ N hle hb Yσ Yτ
  have hn := bounded_submartingale_sampling μ ℱ (-M) hneg σ τ hσ hτ N hle hb
    (-Yσ) (-Yτ)
  simp only [fullStoppedValue_neg] at hn
  obtain ⟨_, _, _, _, hneglo, hne⟩ := hn
  refine ⟨hiσ, hiτ, hmσ, hmτ, ?_, ?_⟩
  · filter_upwards [hlo, hneglo,
      condExp_neg (fullStoppedValue M τ Yτ) (stoppedSigma hσ) (μ := μ)]
      with ω hp hn hc
    rw [hc] at hn
    exact le_antisymm (neg_le_neg_iff.mp hn) hp
  · simp only [Pi.neg_apply, integral_neg] at hne
    exact le_antisymm (neg_le_neg_iff.mp hne) he

end P207
