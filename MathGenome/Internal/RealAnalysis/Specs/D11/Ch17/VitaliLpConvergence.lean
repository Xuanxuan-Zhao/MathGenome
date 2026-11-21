import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Independent statements for paper.tex:5274–5282. The candidate limit is
only assumed measurable, with finite real or complex values. Membership of that
representative in the source Lp space is part of the conclusion on the left.
The quotient limit is identified with it almost everywhere, not pointwise.
All convergence in measure is global. No size assumption on μ is implicit. -/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u v
noncomputable section
namespace Specs.D11.Ch17.VitaliLpConvergence
open Specs.D11.Ch17.UniformControls Specs.D11.Ch07.ConvergenceDefinitions

def vitali_lp_convergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∀ (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ) (G : ℕ → X → 𝕜) (f : X → 𝕜),
      (∀ n, Measurable (G n)) → (∀ n, G n =ᵐ[μ] F n) → Measurable f →
      ((f ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p ∧
        ∃ g : Lp 𝕜 (ENNReal.ofReal p) μ, f =ᵐ[μ] g ∧ Tendsto F atTop (𝓝 g)) ↔
        inMeasureConverges_value μ G f ∧ lpUiSmall_value μ p G ∧
          lpSpatialTails_value μ p G)

/-- Taking the whole space as the truncation makes spatial tails automatic.
This includes an empty family, the empty space, and zero measure. -/
def finite_measure_spatial_tails : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (G : ι → X → 𝕜),
    μ univ < ∞ → lpFamily_value μ p G → lpSpatialTails_value μ p G

def finite_measure_vitali_lp_convergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ) (hp : 1 ≤ p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
    ∀ (F : ℕ → Lp 𝕜 (ENNReal.ofReal p) μ) (G : ℕ → X → 𝕜) (f : X → 𝕜),
      μ univ < ∞ → (∀ n, Measurable (G n)) →
      (∀ n, G n =ᵐ[μ] F n) → Measurable f →
      ((f ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p ∧
        ∃ g : Lp 𝕜 (ENNReal.ofReal p) μ, f =ᵐ[μ] g ∧ Tendsto F atTop (𝓝 g)) ↔
        inMeasureConverges_value μ G f ∧ lpUiSmall_value μ p G)

/-- The literal representative formulation from Chapter 7: the left side
includes finite p-power integral of f and convergence of the error integrals.
There is no integrability premise on f. -/
def vitali_lp_convergence_on_representatives : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ), 1 ≤ p →
    ∀ (G : ℕ → X → 𝕜) (f : X → 𝕜),
      (∀ n, G n ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p) → Measurable f →
      (lpConverges_value μ p G f ↔ inMeasureConverges_value μ G f ∧
        lpUiSmall_value μ p G ∧ lpSpatialTails_value μ p G)

def finite_measure_vitali_lp_convergence_on_representatives : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (p : ℝ), 1 ≤ p →
    ∀ (G : ℕ → X → 𝕜) (f : X → 𝕜), μ univ < ∞ →
      (∀ n, G n ∈ Specs.D11.Ch10.LpDefinition.rawLp_value μ p) → Measurable f →
      (lpConverges_value μ p G f ↔ inMeasureConverges_value μ G f ∧
        lpUiSmall_value μ p G)

end Specs.D11.Ch17.VitaliLpConvergence
