import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-!
Independent statements for paper.tex:2126–2142. The strict deviation set,
p-power integral, and both norm convergence predicates are the shared
representative-level objects. In particular convergence is global, with no
finiteness, sigma-finiteness, completeness, or nonemptiness assumption.
Real and complex scalars are covered by `RCLike`; their norm is respectively
absolute value and modulus. All measure estimates remain extended-valued.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u
noncomputable section
namespace Specs.D11.Ch07.NormToMeasure

open Specs.D11.Ch07.ConvergenceDefinitions

/-- The quantitative estimate, with the literal coefficient ε^(-p).
No integrability assumption is needed for this extended inequality. -/
def deviation_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f g : X → 𝕜) (p ε : ℝ),
    Measurable f → Measurable g → 1 ≤ p → 0 < ε →
    μ (deviationSet_value f g ε) ≤
      ENNReal.ofReal (ε ^ (-p)) * powerIntegral_value μ p (fun x => f x - g x)

def lp_to_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : ℕ → X → 𝕜) (g : X → 𝕜) (p : ℝ),
    lpConverges_value μ p f g → inMeasureConverges_value μ f g

def linfty_to_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : ℕ → X → 𝕜) (g : X → 𝕜),
    linftyConverges_value μ f g → inMeasureConverges_value μ f g

end Specs.D11.Ch07.NormToMeasure
