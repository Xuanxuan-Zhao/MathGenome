import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.SubmartingaleAEConvergence
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal NNReal

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- The first-moment bound in §6.4 gives an integrable real terminal limit.
No convergence in L¹ is claimed. -/
theorem submartingale_ae_convergence (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ)
    (hbdd : ∃ C : ℝ, ∀ n, (∫ ω, |X n ω| ∂μ) ≤ C) :
    ∃ Xlim : Ω → ℝ, Measurable[terminalSigma ℱ] Xlim ∧ Integrable Xlim μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω)) := by
  obtain ⟨C, hC⟩ := hbdd
  have hlib := (submartingale_iff_library μ ℱ X).mp hX
  have hnorm : ∀ n, eLpNorm (X n) 1 μ ≤ (Real.toNNReal C : ℝ≥0∞) := by
    intro n
    rw [eLpNorm_one_eq_lintegral_enorm (hX.2.1 n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hX.2.1 n)]
    simpa only [Real.norm_eq_abs, ENNReal.ofReal] using ENNReal.ofReal_le_ofReal (hC n)
  refine ⟨ℱ.limitProcess X μ, ?_, ?_, hlib.ae_tendsto_limitProcess hnorm⟩
  · exact ℱ.stronglyMeasurable_limitProcess.measurable
  · exact memLp_one_iff_integrable.mp (hlib.memLp_limitProcess hnorm)

/-- For a submartingale, the positive-part bound controls the negative part
because its expectations are bounded below by its time-zero expectation. -/
theorem submartingale_moment_bound_iff (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ) :
    (∃ C : ℝ, ∀ n, (∫ ω, |X n ω| ∂μ) ≤ C) ↔
      ∃ C : ℝ, ∀ n, (∫ ω, (X n ω)⁺ ∂μ) ≤ C := by
  have hlib := (submartingale_iff_library μ ℱ X).mp hX
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun n => le_trans ?_ (hC n)⟩
    apply integral_mono (hX.2.1 n).pos_part (hX.2.1 n).abs
    intro ω
    exact max_le (le_abs_self _) (abs_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨2 * C - ∫ ω, X 0 ω ∂μ, fun n => ?_⟩
    have hexp : (∫ ω, X 0 ω ∂μ) ≤ ∫ ω, X n ω ∂μ := by
      calc
        _ ≤ ∫ ω, μ[X n | ℱ 0] ω ∂μ :=
          integral_mono_ae (hX.2.1 0) integrable_condExp
            (hlib.ae_le_condExp (Nat.zero_le n))
        _ = _ := integral_condExp (ℱ.le 0)
    rw [integral_abs_eq_two_mul_integral_posPart_sub_integral (hX.2.1 n)]
    linarith [hC n]

end P207
