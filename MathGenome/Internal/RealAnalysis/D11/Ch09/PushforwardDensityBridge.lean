import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.PushforwardDensityBridge
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportNonnegative
import MathGenome.Internal.RealAnalysis.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.D11.Ch15.DensityChangeIntegral

/-! A supplied pushforward density, paper.tex:3037–3052.
First transport nonnegative functions and their norms. Before forming a
finite scalar product, reset the density to zero on its measurable null
infinite-value set; this preserves both the density measure and every
weighted nonnegative integral. No density existence theorem is used.
-/

open MeasureTheory
open scoped ENNReal
universe u v

namespace D11.Ch09.PushforwardDensityBridge

open D11.Ch09.Pushforward
open D11.Ch05.DensityMeasureDomains
open D11.Ch05.NonnegativeIntegral
open D11.Ch06.ScalarIntegral

theorem nonnegative_bridge {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (h g : Y → ℝ≥0∞) (hh : Measurable h) (hg : Measurable g)
    (heq : pushforward u hu μ = densityMeasure ν h) :
    nonnegativeIntegral μ (g ∘ u) =
      nonnegativeIntegral ν (fun y => g y * h y) := by
  rw [← D11.Ch09.TransportNonnegative.transport_nonnegative u hu μ g hg, heq]
  exact D11.Ch15.DensityChangeIntegral.nonnegative_change ν h g hh hg

/-- A finite measurable representative on the same sigma-algebra, including
the exact exceptional set and equality of the resulting measures. -/
theorem finite_density_modification :
    Specs.D11.Ch09.PushforwardDensityBridge.finite_density_modification := by
  intro Y _ ν h hh hfin
  have hae : (fun y => ENNReal.ofReal (h y).toReal) =ᵐ[ν] h := by
    filter_upwards [hfin] with y hy
    exact ENNReal.ofReal_toReal hy.ne
  refine ⟨measurableSet_eq_fun hh measurable_const, ?_, hh.ennreal_toReal,
    (fun _ => ENNReal.toReal_nonneg), ?_, ?_, hae, ?_⟩
  · have hne : ∀ᵐ y ∂ν, h y ≠ ∞ := hfin.mono fun _ hy => hy.ne
    simpa only [ae_iff, not_not] using hne
  · intro y hy
    rw [hy, ENNReal.toReal_top]
  · intro y hy
    exact ENNReal.ofReal_toReal hy.ne
  · exact withDensity_congr_ae hae

theorem scalar_integrable_iff {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (h : Y → ℝ≥0∞) (g : Y → 𝕜) (hh : Measurable h)
    (hfin : ∀ᵐ y ∂ν, h y < ∞) (hg : Measurable g)
    (heq : pushforward u hu μ = densityMeasure ν h) :
    scalarIntegrable μ (g ∘ u) ↔
      nonnegativeIntegral ν (fun y => ENNReal.ofReal ‖g y‖ * h y) < ∞ := by
  rw [← D11.Ch09.TransportIntegrable.transport_integrable_iff u hu μ g hg, heq]
  exact D11.Ch15.DensityChangeIntegral.positive_scalar_integrable_iff ν h g hh hfin hg

theorem scalar_bridge {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y)
    (h : Y → ℝ≥0∞) (g : Y → 𝕜) (hh : Measurable h)
    (hfin : ∀ᵐ y ∂ν, h y < ∞) (hg : Measurable g)
    (heq : pushforward u hu μ = densityMeasure ν h)
    (hw : nonnegativeIntegral ν (fun y => ENNReal.ofReal ‖g y‖ * h y) < ∞) :
    ∃ (hc : scalarIntegrable μ (g ∘ u))
      (hp : scalarIntegrable ν (fun y => (h y).toReal • g y)),
      scalarIntegral μ (g ∘ u) hc =
        scalarIntegral ν (fun y => (h y).toReal • g y) hp := by
  obtain ⟨_, _, hm, hnonneg, _, _, hae, hmeasure⟩ :=
    finite_density_modification ν h hh hfin
  -- Replace the extended density before invoking scalar change of measure.
  let h₀ : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (h y).toReal
  change densityMeasure ν h₀ = densityMeasure ν h at hmeasure
  have hm₀ : Measurable h₀ := hm.ennreal_ofReal
  have hfin₀ : ∀ᵐ y ∂ν, h₀ y < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweight : nonnegativeIntegral ν (fun y => ENNReal.ofReal ‖g y‖ * h₀ y) =
      nonnegativeIntegral ν (fun y => ENNReal.ofReal ‖g y‖ * h y) := by
    simp only [integral_eq_lintegral]
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    exact congrArg (fun t => ENNReal.ofReal ‖g y‖ * t) hy
  have hw₀ : nonnegativeIntegral ν (fun y => ENNReal.ofReal ‖g y‖ * h₀ y) < ∞ :=
    hweight.trans_lt hw
  obtain ⟨hgd, hp₀, hd⟩ :=
    D11.Ch15.DensityChangeIntegral.positive_scalar_change ν h₀ g hm₀ hfin₀ hg hw₀
  change scalarIntegrable (densityMeasure ν h₀) g at hgd
  change scalarIntegrable ν (fun y => (h₀ y).toReal • g y) at hp₀
  have hgpush : scalarIntegrable (pushforward u hu μ) g := by
    rw [heq, ← hmeasure]
    exact hgd
  obtain ⟨hc, ht⟩ :=
    D11.Ch09.TransportIntegrable.transport_integral u hu μ g hgpush
  have hp : scalarIntegrable ν (fun y => (h y).toReal • g y) := by
    simpa only [h₀, ENNReal.toReal_ofReal (hnonneg _)] using hp₀
  refine ⟨hc, hp, ?_⟩
  change (∫ x, g (u x) ∂μ) = ∫ y, (h y).toReal • g y ∂ν
  change (∫ y, g y ∂pushforward u hu μ) = ∫ x, g (u x) ∂μ at ht
  change (∫ y, g y ∂densityMeasure ν h₀) = ∫ y, (h₀ y).toReal • g y ∂ν at hd
  rw [← ht, heq, ← hmeasure]
  simpa only [h₀, ENNReal.toReal_ofReal (hnonneg _)] using hd

end D11.Ch09.PushforwardDensityBridge
