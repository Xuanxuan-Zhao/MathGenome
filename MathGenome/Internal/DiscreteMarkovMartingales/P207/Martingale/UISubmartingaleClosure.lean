import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.SubmartingaleAEConvergence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.Vitali
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UISubmartingaleClosure

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- The submartingale test-event inequalities pass to any integrable L¹ limit. -/
theorem submartingale_le_condExp_of_L1_convergence
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ)
    (Y : Ω → ℝ) (hY : Integrable Y μ)
    (hL1 : Tendsto (fun k => ∫ ω, |X k ω - Y ω| ∂μ) atTop (𝓝 0))
    (n : ℕ) : X n ≤ᵐ[μ] μ[Y | ℱ n] := by
  have hlib := (submartingale_iff_library μ ℱ X).mp hX
  have heL1 : Tendsto (fun k => eLpNorm (X k - Y) 1 μ) atTop (𝓝 0) := by
    have heq (k : ℕ) : eLpNorm (X k - Y) 1 μ =
        ENNReal.ofReal (∫ ω, |X k ω - Y ω| ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hX.2.1 k).sub hY).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm ((hX.2.1 k).sub hY)]
      simp only [Pi.sub_apply, Real.norm_eq_abs]
    simpa only [heq, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hL1
  have htest (s : Set Ω) (hs : MeasurableSet[ℱ n] s) :
      (∫ ω in s, X n ω ∂μ) ≤ ∫ ω in s, Y ω ∂μ := by
    apply ge_of_tendsto (tendsto_setIntegral_of_L1' Y
      (Eventually.of_forall hX.2.1) heL1 s)
    filter_upwards [eventually_ge_atTop n] with k hk
    calc
      (∫ ω in s, X n ω ∂μ) ≤ ∫ ω in s, μ[X k | ℱ n] ω ∂μ :=
        setIntegral_mono_ae (hX.2.1 n).integrableOn integrable_condExp.integrableOn
          (hlib.ae_le_condExp hk)
      _ = ∫ ω in s, X k ω ∂μ := setIntegral_condExp (ℱ.le n) (hX.2.1 k) hs
  apply ae_le_of_ae_le_trim (hm := ℱ.le n)
  apply ae_le_of_forall_setIntegral_le
    ((hX.2.1 n).trim (ℱ.le n) (hlib.stronglyMeasurable n))
    (integrable_condExp.trim (ℱ.le n) stronglyMeasurable_condExp)
  intro s hs _
  rw [← setIntegral_trim (ℱ.le n) (hlib.stronglyMeasurable n) hs,
    ← setIntegral_trim (ℱ.le n) stronglyMeasurable_condExp hs,
    setIntegral_condExp (ℱ.le n) hY hs]
  exact htest s hs

/-- A uniformly integrable real submartingale converges almost surely and in
L¹ to an integrable terminal-measurable variable which conditionally dominates
it at every finite time. -/
theorem ui_submartingale_terminal_closure
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m)
    (X : ℕ → Ω → ℝ) (hX : IsSubmartingale X ℱ μ)
    (hui : Martingale.SourceUniformIntegrable μ X) :
    ∃ Xlim : Ω → ℝ, Measurable[terminalSigma ℱ] Xlim ∧ Integrable Xlim μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Xlim ω))) ∧
      Tendsto (fun n => ∫ ω, |X n ω - Xlim ω| ∂μ) atTop (𝓝 0) ∧
      ∀ n, X n ≤ᵐ[μ] μ[Xlim | ℱ n] := by
  obtain ⟨C, hC⟩ := Martingale.sourceUniformIntegrable_bounded μ X hui
  have hbdd : ∃ C : ℝ, ∀ n, (∫ ω, |X n ω| ∂μ) ≤ C :=
    ⟨C, by simpa only [Real.norm_eq_abs] using hC⟩
  obtain ⟨Y, hmY, hiY, hae⟩ := submartingale_ae_convergence μ ℱ X hX hbdd
  have hprob := tendstoInMeasure_of_tendsto_ae
    (fun n => (hX.2.1 n).aestronglyMeasurable) hae
  have hL1 : Tendsto (fun n => ∫ ω, |X n ω - Y ω| ∂μ) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs] using
      (Martingale.vitali_forward μ X Y hX.2.1 hprob hui).2.2
  exact ⟨Y, hmY, hiY, hae, hL1,
    submartingale_le_condExp_of_L1_convergence μ ℱ X hX Y hiY hL1⟩

end P207
