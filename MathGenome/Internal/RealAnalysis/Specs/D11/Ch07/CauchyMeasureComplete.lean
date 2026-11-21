import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.SubsequenceUniqueness

/-! Independent statement of paper.tex:2204–2241. The target field includes
both ℝ and ℂ. The limit is a finite scalar at every point and is measurable
on the original sigma-algebra, with a specified zero value on a measurable
null exceptional envelope. No total-mass or measure-completeness assumption
is imposed. Uniqueness uses the ordinary a.e. relation. -/
open Set Filter MeasureTheory
open scoped Topology
universe u
namespace Specs.D11.Ch07.CauchyMeasureComplete
open Specs.D11.Ch07.ConvergenceDefinitions
open Specs.D11.Ch04.AeCommonException

def complete_in_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : ℕ → X → 𝕜),
    (∀ n, Measurable (f n)) → cauchyInMeasure_value μ f →
    ∃ (g : X → 𝕜) (N : Set X) (ns : ℕ → ℕ),
      Measurable g ∧ MeasurableSet N ∧ μ N = 0 ∧
      (∀ x ∈ N, g x = 0) ∧ StrictMono ns ∧
      (∀ x ∉ N, Tendsto (fun j => f (ns j) x) atTop (𝓝 (g x))) ∧
      aeConverges_value μ (fun j => f (ns j)) g ∧
      inMeasureConverges_value μ f g ∧
      (∀ h : X → 𝕜, inMeasureConverges_value μ f h → aeEq_value μ g h)
end Specs.D11.Ch07.CauchyMeasureComplete
