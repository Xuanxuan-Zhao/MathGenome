import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.UniformControls
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Independent types for paper.tex:5218–5229 and 5236–5244.
The predicates are the accepted shared predicates, with no finiteness,
atomlessness, nonzero-measure or nonempty-family assumption in the first
two implications. Only the third implication assumes finite total mass. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch17.DefinitionComparison
open Specs.D11.Ch17.UniformControls

def tail_implies_small : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
    uiTail_value μ F → uiSmall_value μ F

def small_and_bound_implies_tail : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
    uiSmall_value μ F → uniformL1Bound_value μ F → uiTail_value μ F

def tail_implies_bound_of_finite : Prop :=
  ∀ {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ι → X → 𝕜),
    μ univ < ∞ → uiTail_value μ F → uniformL1Bound_value μ F

/-- The actual unbounded sequence on the one-point probability space.
Both the exact individual norms and the infinite tail suprema are included. -/
def atomic_ui_counterexample : Prop :=
  let μ : Measure Unit := Measure.dirac ()
  let F : ℕ → Unit → ℝ := fun n _ => (n : ℝ)
  μ univ = 1 ∧ uiSmall_value μ F ∧
    (∀ n, absoluteIntegral_value μ (F n) univ = (n : ℝ≥0∞)) ∧
    integralSup_value μ F univ = ∞ ∧
    (∀ R, amplitudeSup_value μ F R = ∞) ∧
    ¬ uniformL1Bound_value μ F ∧ ¬ uiTail_value μ F

end Specs.D11.Ch17.DefinitionComparison
