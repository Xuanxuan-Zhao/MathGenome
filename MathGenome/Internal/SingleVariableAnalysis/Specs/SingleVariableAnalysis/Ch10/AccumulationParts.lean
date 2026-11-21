import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.Accumulation
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Proper accumulation integration by parts, paper.tex:3052–3077.
The derivative is a real-variable derivative. Continuity on the closed
interval and a continuous derivative extension express C¹ on that interval;
only interior derivatives are needed by the formula. The conclusion supplies
all integrability witnesses, including every initial segment. F is defined on
the interval by those actual Darboux values; its values outside are immaterial.
-/
namespace Specs.SingleVariableAnalysis.Ch10.AccumulationParts
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- Real scalar version, including singleton intervals. -/
def realParts : Prop :=
  ∀ (f g g' : ℝ → ℝ) {a b : ℝ} (hf : realIntegrableValue f a b),
    ContinuousOn g (Set.Icc a b) → ContinuousOn g' (Set.Icc a b) →
    (∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) →
    ∃ H : ∀ x : Set.Icc a b, realIntegrableValue f a x,
    ∃ F : ℝ → ℝ,
      (∀ x : Set.Icc a b, F x = realIntegralValue f (H x)) ∧
      ∃ hfg : realIntegrableValue (fun x => f x * g x) a b,
      ∃ hFg' : realIntegrableValue (fun x => F x * g' x) a b,
        realIntegralValue _ hfg = F b * g b - realIntegralValue _ hFg'

/-- Complex scalar version. The proof may use distinct real mean-value tags
for the two components of g. No derivative of F is stipulated. -/
def complexParts : Prop :=
  ∀ (f g g' : ℝ → ℂ) {a b : ℝ} (hf : complexIntegrableValue f a b),
    ContinuousOn g (Set.Icc a b) → ContinuousOn g' (Set.Icc a b) →
    (∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) →
    ∃ H : ∀ x : Set.Icc a b, complexIntegrableValue f a x,
    ∃ F : ℝ → ℂ,
      (∀ x : Set.Icc a b, F x = complexIntegralValue f (H x)) ∧
      ∃ hfg : complexIntegrableValue (fun x => f x * g x) a b,
      ∃ hFg' : complexIntegrableValue (fun x => F x * g' x) a b,
        complexIntegralValue _ hfg = F b * g b - complexIntegralValue _ hFg'

end Specs.SingleVariableAnalysis.Ch10.AccumulationParts
