import MathGenome.Internal.FourierSobolev.Specs.P102.U2.Marcinkiewicz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.Marcinkiewicz

open MeasureTheory
open scoped ENNReal NNReal

universe u v w

namespace P102.U2

open ExpandedFA.Interpolation
open ExpandedFA.Interpolation.MarcinkiewiczSpec

/-- The essential supremum convention agrees with the extended L-infinity norm
for the measurable outputs supplied by sublinearity. -/
lemma weakSizeInfinity_eq_eLpNorm {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] (μ : Measure X) (f : X → F)
    (hf : AEStronglyMeasurable f μ) : weakSizeInfinity μ f = eLpNorm f ∞ μ := by
  rw [eLpNorm_exponent_top hf]
  simp only [weakSizeInfinity, eLpNormEssSup, ofReal_norm]

/-- The project's weak-norm hypothesis gives every level estimate required by
library interpolation. No positivity of the endpoint constant is used. -/
lemma endpointEstimate_of_weakSize {X Y E F : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure X) (ν : Measure Y) (r : ℝ≥0∞) (M : ℝ≥0)
    (f : X → E) (g : Y → F) (hg : AEStronglyMeasurable g ν)
    (h : (if r = ∞ then weakSizeInfinity ν g else weakSize ν r.toReal g) ≤
      (M : ℝ≥0∞) * eLpNorm f r μ) : endpointEstimate μ ν r M f g := by
  by_cases hr : r = ∞
  · subst r
    simpa [endpointEstimate, weakSizeInfinity_eq_eLpNorm ν g hg] using h
  · simp only [endpointEstimate, hr, ↓reduceIte]
    simp only [hr, ↓reduceIte] at h
    intro t ht
    change ENNReal.ofReal t * P102.U2.distribution ν g t ^ (1 / r.toReal) ≤ _
    have htbound : ENNReal.ofReal t * P102.U2.distribution ν g t ^ (1 / r.toReal) ≤
        weakSize ν r.toReal g := by
      unfold weakSize
      exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
    exact htbound.trans h

/-- Diagonal Marcinkiewicz interpolation, with a single common operator and a
uniform finite bound. Both zero endpoint bounds and the infinity upper endpoint
are retained. The library theorems prove the truncation and layer-cake estimates;
we supply their endpoint hypotheses from the project's actual weak sizes. -/
theorem marcinkiewicz : MarcinkiewiczSpec.DiagonalInterpolation.{u,v,w} := by
  intro p₀ p₁ p M₀ M₁ hp₀ h₀ h₁
  rcases marcinkiewicz_exponent_coordinates p₀ p₁ p hp₀ h₀ h₁ with
    ⟨hp₀top, hptop, hr₀, hr₀p, hc₀, hc⟩
  have hr₀pos : 0 < p₀.toReal := lt_of_lt_of_le zero_lt_one hr₀
  by_cases hp₁top : p₁ = ∞
  · subst p₁
    obtain ⟨C, hC⟩ := marcinkiewicz_infinity p₀.toReal p.toReal M₀ M₁ hr₀ hr₀p
    refine ⟨C, ?_⟩
    intro X Y 𝕜 instX instY inst𝕜 μ ν T hs hw₀ hw₁ f hf
    have hd : sumDomain μ p₀ ∞ f := by
      rw [← hc₀]
      exact memLp_sumDomain_top hr₀pos hr₀p.le (by simpa only [hc] using hf)
    refine ⟨hd, ?_⟩
    have hC' := @hC X Y 𝕜 instX instY inst𝕜 μ ν
    rw [hc₀, hc] at hC'
    apply hC' T hs ?_ ?_ f hf
    · intro g hg
      exact endpointEstimate_of_weakSize μ ν p₀ M₀ g (T g)
        (hs.measurable g (sumDomain_of_memLp_left hg)) (hw₀ g hg)
    · intro g hg
      exact endpointEstimate_of_weakSize μ ν ∞ M₁ g (T g)
        (hs.measurable g (sumDomain_of_memLp_right hg)) (hw₁ g hg)
  · have hr₁ : p.toReal < p₁.toReal :=
      (ENNReal.toReal_lt_toReal hptop hp₁top).2 h₁
    have hc₁ := ENNReal.ofReal_toReal hp₁top
    obtain ⟨C, hC⟩ := marcinkiewicz_finite p₀.toReal p₁.toReal p.toReal M₀ M₁ hr₀ hr₀p hr₁
    refine ⟨C, ?_⟩
    intro X Y 𝕜 instX instY inst𝕜 μ ν T hs hw₀ hw₁ f hf
    have hd : sumDomain μ p₀ p₁ f := by
      rw [← hc₀, ← hc₁]
      exact memLp_sumDomain hr₀pos hr₀p.le hr₁.le (by simpa only [hc] using hf)
    refine ⟨hd, ?_⟩
    have hC' := @hC X Y 𝕜 instX instY inst𝕜 μ ν
    rw [hc₀, hc₁, hc] at hC'
    apply hC' T hs ?_ ?_ f hf
    · intro g hg
      exact endpointEstimate_of_weakSize μ ν p₀ M₀ g (T g)
        (hs.measurable g (sumDomain_of_memLp_left hg)) (hw₀ g hg)
    · intro g hg
      exact endpointEstimate_of_weakSize μ ν p₁ M₁ g (T g)
        (hs.measurable g (sumDomain_of_memLp_right hg)) (hw₁ g hg)

end P102.U2
