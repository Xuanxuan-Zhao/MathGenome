import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.AlmostUniformImplications

/-!
Consequences of almost-uniform convergence (paper.tex:2270–2284).

The failure set has outer measure below every positive real bound: it is
contained in every removed set on whose complement convergence is uniform.
The accepted ordinary-a.e. bridge then supplies a measurable null envelope
in the original sigma-algebra. This also works for nonmeasurable functions.
For global convergence in measure, eventual deviation sets are contained in
a single removed set of arbitrarily small measure.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

universe u v

namespace D11.Ch07.AlmostUniformImplications

open D11.Ch07.ConvergenceDefinitions
open D11.Ch04.AeCommonException

variable {X : Type u} {E : Type v} [NormedAddCommGroup E]

/-- Uniform convergence on a set implies convergence at each of its points. -/
private theorem pointwise_of_uniform_on (f : ℕ → X → E) (g : X → E)
    (A : Set X) (h : uniformConvergesOn f g A) (x : X) (hx : x ∈ A) :
    Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by simpa only [dist_eq_norm] using hN n hn x hx⟩

variable [MeasurableSpace X]

theorem almost_uniform_implies_ae (μ : Measure X) (f : ℕ → X → E) (g : X → E)
    (h : almostUniformConverges μ f g) : aeConverges μ f g := by
  apply (almostEverywhere_iff_native μ _).mpr
  rw [ae_iff]
  apply le_antisymm _ bot_le
  by_contra hpos
  obtain ⟨δ, _, hδ, hδμ⟩ := ENNReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hpos)
  obtain ⟨A, _, hμA, hA⟩ := h δ (ENNReal.ofReal_pos.mp hδ)
  have hsub : {x | ¬ Tendsto (fun n => f n x) atTop (𝓝 (g x))} ⊆ A := by
    intro x hx
    by_contra hxA
    exact hx (pointwise_of_uniform_on f g Aᶜ hA x hxA)
  exact (lt_asymm hδμ) ((measure_mono hsub).trans_lt hμA)

theorem almost_uniform_implies_inMeasure (μ : Measure X)
    (f : ℕ → X → E) (g : X → E) (h : almostUniformConverges μ f g) :
    inMeasureConverges μ f g := by
  intro ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨δ, _, hδ, hδη⟩ := ENNReal.lt_iff_exists_real_btwn.mp hη
  obtain ⟨A, _, hμA, hA⟩ := h δ (ENNReal.ofReal_pos.mp hδ)
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun n hn => (measure_mono ?_).trans (hμA.le.trans hδη.le)⟩
  intro x hx
  by_contra hxA
  exact (not_lt_of_ge (hN n hn x hxA).le) hx

end D11.Ch07.AlmostUniformImplications
