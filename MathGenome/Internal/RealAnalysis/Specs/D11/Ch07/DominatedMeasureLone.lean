import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.DominatedConvergence

/-!
Independent statement for paper.tex:2362–2381, dominated convergence in measure.
The convergence hypothesis is global, with strict deviation thresholds. All
scalar functions are finite and measurable in the original sigma-algebra.
There is no assumption on total mass, sigma-finiteness or completeness.

The shared conclusion includes integrability of the sequence, the limit and
each absolute error, convergence of the nonnegative absolute-error integrals,
and convergence of the scalar integrals evaluated with integrability proofs.
`RCLike` specializes to both real and complex scalars.
-/
open Filter MeasureTheory
open scoped Topology
universe u

namespace Specs.D11.Ch07.DominatedMeasureLone

open Specs.D11.Ch07.ConvergenceDefinitions
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch04.AeCommonException

/-- An integrable common bound upgrades global convergence in measure to L¹
and scalar integral convergence on an arbitrary positive measure space. -/
def dominated_convergence_in_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (F n)) → Measurable f → scalarIntegrable_value μ g →
    (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖F n x‖ ≤ g x)) →
    inMeasureConverges_value μ F f →
    Specs.D11.Ch06.DominatedConvergence.convergenceConclusions μ F f

end Specs.D11.Ch07.DominatedMeasureLone
