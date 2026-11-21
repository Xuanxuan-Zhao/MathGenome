import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Independent statements for paper.tex:3417–3431. All representatives are
measurable on the original space. The finite exponent is real and at least
one. The convergence in measure is global, at every positive threshold.
The infinity conclusion retains the entire sequence on one measurable
conull set. No size or completeness condition is imposed on the measure.

The first two bridges identify norm convergence of the represented classes
with the earlier power-integral and essential-supremum predicates. The last
bridge transports this identification to the ordinary raw-function quotient
through any of the isometries specified by the upstream construction.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch10.LpConvergenceMeasure
open Specs.D11.Ch10.QuotientConstruction
open Specs.D11.Ch07.ConvergenceDefinitions

def finite_norm_iff_representative : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p)
    (f : ℕ → Raw (𝕜 := 𝕜) μ (ENNReal.ofReal p))
    (g : Raw (𝕜 := 𝕜) μ (ENNReal.ofReal p)),
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp⟩
    Tendsto (fun n => (f n).property.2.toLp (f n).val) atTop
      (𝓝 (g.property.2.toLp g.val)) ↔
      lpConverges_value μ p (fun n => (f n).val) g.val

def infinity_norm_iff_representative : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → Raw (𝕜 := 𝕜) μ ∞) (g : Raw (𝕜 := 𝕜) μ ∞),
    Tendsto (fun n => (f n).property.2.toLp (f n).val) atTop
      (𝓝 (g.property.2.toLp g.val)) ↔
      linftyConverges_value μ (fun n => (f n).val) g.val

def finite_convergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ)
    (f : ℕ → X → 𝕜) (g : X → 𝕜), lpConverges_value μ p f g →
    inMeasureConverges_value μ f g ∧
      ∃ ns : ℕ → ℕ, StrictMono ns ∧ aeConverges_value μ (fun n => f (ns n)) g

def infinity_convergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (g : X → 𝕜), linftyConverges_value μ f g →
    ∃ A : Set X, MeasurableSet A ∧ μ Aᶜ = 0 ∧ uniformConvergesOn_value f g A

def quotient_convergence_bridge : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (G : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p)),
    letI := G
    ∀ (V : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p)),
    letI := V
    ∀ F : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
    (∀ h : Raw (𝕜 := 𝕜) μ p, F (classOf h) = h.property.2.toLp h.val) →
    ∀ (f : ℕ → Raw (𝕜 := 𝕜) μ p) (g : Raw (𝕜 := 𝕜) μ p),
    Tendsto (fun n => classOf (f n)) atTop (𝓝 (classOf g)) ↔
      Tendsto (fun n => (f n).property.2.toLp (f n).val) atTop
        (𝓝 (g.property.2.toLp g.val))

end Specs.D11.Ch10.LpConvergenceMeasure
