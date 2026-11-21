import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-! Independent statements for paper.tex:2405–2435.
`RCLike` includes both real and complex scalars. All representatives are finite
and measurable on the original space. The convergence predicate is the upstream
strict, global deviation-measure definition. Only products require finite mass.
The measurability conclusions also keep the resulting functions in this class. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
namespace Specs.D11.Ch07.MeasureOperations
open Specs.D11.Ch07.ConvergenceDefinitions

def linear_combination : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f g : ℕ → X → 𝕜) (F G : X → 𝕜) (a b : 𝕜),
    (∀ n, Measurable (f n)) → (∀ n, Measurable (g n)) →
    Measurable F → Measurable G →
    inMeasureConverges_value μ f F → inMeasureConverges_value μ g G →
    (∀ n, Measurable (fun x => a * f n x + b * g n x)) ∧
    Measurable (fun x => a * F x + b * G x) ∧
    inMeasureConverges_value μ (fun n x => a * f n x + b * g n x)
      (fun x => a * F x + b * G x)

def product : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f g : ℕ → X → 𝕜) (F G : X → 𝕜),
    μ univ < ∞ →
    (∀ n, Measurable (f n)) → (∀ n, Measurable (g n)) →
    Measurable F → Measurable G →
    inMeasureConverges_value μ f F → inMeasureConverges_value μ g G →
    (∀ n, Measurable (fun x => f n x * g n x)) ∧
    Measurable (fun x => F x * G x) ∧
    inMeasureConverges_value μ (fun n x => f n x * g n x) (fun x => F x * G x)

def uniformlyContinuous_composition : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (f : ℕ → X → 𝕜) (F : X → 𝕜) (φ : 𝕜 → 𝕜),
    (∀ n, Measurable (f n)) → Measurable F →
    UniformContinuous φ → inMeasureConverges_value μ f F →
    (∀ n, Measurable (φ ∘ f n)) ∧ Measurable (φ ∘ F) ∧
    inMeasureConverges_value μ (fun n => φ ∘ f n) (φ ∘ F)

end Specs.D11.Ch07.MeasureOperations
