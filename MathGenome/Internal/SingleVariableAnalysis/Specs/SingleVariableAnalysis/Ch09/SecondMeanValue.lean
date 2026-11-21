import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Order.Monotone.Basic

/-! Independent statements of K03.09.second_mean_value (paper.tex:2506–2535)
and its reflected use at paper.tex:4858–4867. The integrability and values are
proper Darboux integrability and its common lower/upper integral. No continuity
or endpoint convention is imposed on the monotone weight. -/
namespace Specs.SingleVariableAnalysis.Ch09.SecondMeanValue
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- Nonnegative nonincreasing weights, including jumps and zero initial value. -/
def antitoneWeight : Prop :=
  ∀ (f g : ℝ → ℝ) {a b : ℝ} (hf : realIntegrableValue f a b),
    (∀ x ∈ Set.Icc a b, 0 ≤ g x) → AntitoneOn g (Set.Icc a b) →
    ∃ hg : realIntegrableValue g a b,
    ∃ hgf : realIntegrableValue (fun x => g x * f x) a b,
    ∃ ξ ∈ Set.Icc a b, ∃ hξ : realIntegrableValue f a ξ,
      realIntegralValue _ hgf = g a * realIntegralValue f hξ

/-- Reflected form: the normalization uses the actual final endpoint value. -/
def monotoneWeight : Prop :=
  ∀ (f g : ℝ → ℝ) {a b : ℝ} (hf : realIntegrableValue f a b),
    (∀ x ∈ Set.Icc a b, 0 ≤ g x) → MonotoneOn g (Set.Icc a b) →
    ∃ hg : realIntegrableValue g a b,
    ∃ hgf : realIntegrableValue (fun x => g x * f x) a b,
    ∃ ξ ∈ Set.Icc a b, ∃ hξ : realIntegrableValue f ξ b,
      realIntegralValue _ hgf = g b * realIntegralValue f hξ

end Specs.SingleVariableAnalysis.Ch09.SecondMeanValue
