import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions

/-!
Independent statement for paper.tex:2192–2202 (D11.07.summable_errors_ae).
The norm is real absolute value or complex modulus. The sum and the
nonnegative integrals take values in `[0, ∞]`, so finiteness does not use
the totalized scalar integral. All functions are finite scalar-valued and
measurable for the original sigma-algebra. The conclusion uses the shared
ordinary a.e. predicate, with a measurable null envelope in that algebra.
No finiteness, sigma-finiteness, completeness or nonemptiness is assumed.
-/
open MeasureTheory
open scoped ENNReal

universe u
noncomputable section
namespace Specs.D11.Ch07.SummableErrors

open _root_.Specs.D11.Ch05.NonnegativeIntegral

/-- Summable absolute integral errors imply convergence almost everywhere,
for both real and complex scalars on an arbitrary positive measure space. -/
def summable_errors_ae : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : ℕ → X → 𝕜) (g : X → 𝕜),
    (∀ n, Measurable (f n)) → Measurable g →
    (∑' n, nonnegativeIntegral_value μ
      (fun x => ENNReal.ofReal ‖f n x - g x‖)) < ∞ →
    ConvergenceDefinitions.aeConverges_value μ f g

end Specs.D11.Ch07.SummableErrors
