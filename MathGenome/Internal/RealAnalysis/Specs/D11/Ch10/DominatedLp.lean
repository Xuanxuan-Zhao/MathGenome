import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-! Independent statements of paper.tex:3431–3447. Finite exponents mean
real `1 ≤ p`. The conclusions include ordinary measurable raw membership
of the sequence, limit, and errors, and convergence of the original power
norm. The normed-group generalization specializes to both real and complex
scalars with their usual Borel and second-countability instances. No size
or completeness hypothesis is imposed on the measure. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
namespace Specs.D11.Ch10.DominatedLp
open Specs.D11.Ch10.LpDefinition
open Specs.D11.Ch07.ConvergenceDefinitions
open Specs.D11.Ch04.AeCommonException

def dominated_ae : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) (p : ℝ) (F : ℕ → X → E) (f : X → E) (g : X → ℝ),
    1 ≤ p → (∀ n, Measurable (F n)) → Measurable f →
    g ∈ rawLp_value μ p → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖F n x‖ ≤ g x)) →
    aeConverges_value μ F f →
    (∀ n, F n ∈ rawLp_value μ p) ∧ f ∈ rawLp_value μ p ∧
    (∀ n, (fun x => F n x - f x) ∈ rawLp_value μ p) ∧
    Tendsto (fun n => powerNorm_value μ p (fun x => F n x - f x)) atTop (𝓝 0)

def dominated_inMeasure : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure X) (p : ℝ) (F : ℕ → X → E) (f : X → E) (g : X → ℝ),
    1 ≤ p → (∀ n, Measurable (F n)) → Measurable f →
    g ∈ rawLp_value μ p → (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖F n x‖ ≤ g x)) →
    inMeasureConverges_value μ F f →
    (∀ n, F n ∈ rawLp_value μ p) ∧ f ∈ rawLp_value μ p ∧
    (∀ n, (fun x => F n x - f x) ∈ rawLp_value μ p) ∧
    Tendsto (fun n => powerNorm_value μ p (fun x => F n x - f x)) atTop (𝓝 0)

end Specs.D11.Ch10.DominatedLp
