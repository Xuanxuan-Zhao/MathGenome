import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.AccumulationParts
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.Cauchy

/-! Abel's test, K03.10.abel. All integrals are proper Darboux truncations
and their finite one-sided limits, including conditionally convergent ones.
A real C¹ multiplier is described by its continuous derivative extension;
only interior derivatives are needed. Monotonicity allows either direction.
The quantitative statement includes zero bounds and degenerate intervals. -/
namespace Specs.SingleVariableAnalysis.Ch10.Abel
open _root_.SingleVariableAnalysis
open OneEndpoint
open Specs.SingleVariableAnalysis.Ch08.Integral

/-- Multiplication by a real function in the two canonical scalar fields. -/
def weighted (k : ScalarKind) : (ℝ → S.scalarValue k) → (ℝ → ℝ) → ℝ → S.scalarValue k :=
  match k with
  | .real => fun f g x => (show ℝ from f x) * g x
  | .complex => fun f g x => (show ℂ from f x) * (g x : ℂ)

/-- Uniform finite-tail estimate from small accumulation integrals. -/
def tailEstimate : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (g g' : ℝ → ℝ)
    (R S ε B : ℝ) (hf : scalarIntegrableValue k f R S),
    0 ≤ ε → 0 ≤ B →
    ContinuousOn g (Set.Icc R S) → ContinuousOn g' (Set.Icc R S) →
    (∀ x ∈ Set.Ioo R S, HasDerivAt g (g' x) x) →
    (MonotoneOn g (Set.Icc R S) ∨ AntitoneOn g (Set.Icc R S)) →
    (∀ x ∈ Set.Icc R S, |g x| ≤ B) →
    (∀ x ∈ Set.Icc R S, ∀ hx : scalarIntegrableValue k f R x,
      ‖scalarIntegralValue k f hx‖ ≤ ε) →
    ∃ hfg : scalarIntegrableValue k (weighted k f g) R S,
      ‖scalarIntegralValue k (weighted k f g) hfg‖ ≤ 3 * B * ε

/-- Abel convergence on the full half-line; no absolute convergence is assumed. -/
def convergence : Prop :=
  ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (g g' : ℝ → ℝ) (a B : ℝ),
    rightConvergesValue k f a ⊤ →
    ContinuousOn g (Set.Ici a) → ContinuousOn g' (Set.Ici a) →
    (∀ x ∈ Set.Ioi a, HasDerivAt g (g' x) x) →
    (MonotoneOn g (Set.Ici a) ∨ AntitoneOn g (Set.Ici a)) →
    (∀ x ∈ Set.Ici a, |g x| ≤ B) →
    rightConvergesValue k (weighted k f g) a ⊤

/-- The explanatory finite multiplier limit and the exact splitting identity
from the end of the source proof; neither asserts a limit interchange. -/
def multiplierLimitAndSplit : Prop :=
  ∀ (g : ℝ → ℝ) (a B : ℝ),
    (MonotoneOn g (Set.Ici a) ∨ AntitoneOn g (Set.Ici a)) →
    (∀ x ∈ Set.Ici a, |g x| ≤ B) →
    ∃ ℓ : ℝ, Filter.Tendsto g Filter.atTop (nhds ℓ) ∧
      ∀ (k : ScalarKind) (f : ℝ → S.scalarValue k) (x : ℝ),
        weighted k f g x = weighted k f (fun _ => ℓ) x +
          weighted k f (fun t => g t - ℓ) x

end Specs.SingleVariableAnalysis.Ch10.Abel
