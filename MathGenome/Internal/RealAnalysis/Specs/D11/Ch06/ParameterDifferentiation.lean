import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent statement of paper.tex:2011–2041.
The statement works on every open parameter set, in particular every open
interval. `F x` is an ambient representative of the function on that set;
no value or regularity outside `I` is constrained or used. The common
scalar-integrability predicate includes actual measurability and finite
absolute integral on the original measurable space. All displayed integrals
are evaluated at parameters where integrability is assumed or concluded.
There is no joint-measurability, completeness or measure-size hypothesis. -/

open Set MeasureTheory
universe u
noncomputable section
namespace Specs.D11.Ch06.ParameterDifferentiation
open Specs.D11.Ch06.ScalarIntegral

def parameter_differentiation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (I : Set ℝ) (F : X → ℝ → ℝ) (g : X → ℝ),
    IsOpen I →
    (∀ t ∈ I, scalarIntegrable_value μ (fun x => F x t)) →
    (∀ x, DifferentiableOn ℝ (F x) I) →
    scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    (∀ x, ∀ s ∈ I, ∀ t ∈ I, s ≠ t →
      |(F x t - F x s) / (t - s)| ≤ g x) →
    DifferentiableOn ℝ (fun t => ∫ x, F x t ∂μ) I ∧
    ∀ t ∈ I,
      scalarIntegrable_value μ (fun x => deriv (F x) t) ∧
      HasDerivAt (fun t => ∫ x, F x t ∂μ) (∫ x, deriv (F x) t ∂μ) t ∧
      deriv (fun t => ∫ x, F x t ∂μ) t = ∫ x, deriv (F x) t ∂μ

end Specs.D11.Ch06.ParameterDifferentiation
