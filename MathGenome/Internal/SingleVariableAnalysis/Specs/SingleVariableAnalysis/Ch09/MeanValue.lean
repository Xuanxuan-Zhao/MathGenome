import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Topology.ContinuousOn

/-! Independent statements of K03.09.mean_value, paper.tex:2492–2507.
All integrals are the upstream proper Darboux integrals, with integrability
witnesses rather than default values. Continuity is relative to the closed
interval, including its endpoints. Neither statement requires positive total
weight, and singleton intervals are included. -/
namespace Specs.SingleVariableAnalysis.Ch09.MeanValue
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- The real weighted mean value is attained at a point of the interval.
Existence of the product integral is part of the conclusion. -/
def realWeightedMeanValue : Prop :=
  ∀ (f g : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    ContinuousOn f (Set.Icc a b) →
    ∀ hg : realIntegrableValue g a b,
    (∀ x ∈ Set.Icc a b, 0 ≤ g x) →
    ∃ hfg : realIntegrableValue (fun x => f x * g x) a b,
      ∃ c ∈ Set.Icc a b,
        realIntegralValue _ hfg = f c * realIntegralValue g hg

/-- For complex values the conclusion is the weighted triangle and supremum
bounds. No exact intermediate-point equality is asserted. -/
def complexWeightedNormBound : Prop :=
  ∀ (f : ℝ → ℂ) (g : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    ContinuousOn f (Set.Icc a b) →
    ∀ hg : realIntegrableValue g a b,
    (∀ x ∈ Set.Icc a b, 0 ≤ g x) →
    ∃ hfg : complexIntegrableValue (fun x => f x * (g x : ℂ)) a b,
    ∃ hng : realIntegrableValue (fun x => ‖f x‖ * g x) a b,
      ‖complexIntegralValue _ hfg‖ ≤ realIntegralValue _ hng ∧
      realIntegralValue _ hng ≤
        sSup ((fun x => ‖f x‖) '' Set.Icc a b) * realIntegralValue g hg

end Specs.SingleVariableAnalysis.Ch09.MeanValue
