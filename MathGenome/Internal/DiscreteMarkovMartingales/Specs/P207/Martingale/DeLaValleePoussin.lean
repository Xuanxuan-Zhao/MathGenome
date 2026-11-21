import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.UniformIntegrability
import Mathlib.Analysis.Convex.Function

/-! Independent specification of paper.tex, §6.2 (W31), equivalence of (1)
and (3). A real-valued function restricted to `Ici 0` is a finite-valued
function on the nonnegative half-line. Extended nonnegative integrals and
suprema express the moment bound, also for an empty index type.

The finite-measure formulation includes every probability space. The normed
group formulation includes every real or complex Banach space, without a
separability assumption. Integrability of the given family is explicit.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

universe u v w

namespace Specs.P207.Martingale.DeLaValleePoussin

def criterionType : Prop :=
  ∀ {Ω : Type u} {E : Type v} {I : Type w}
    [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : I → Ω → E),
    (∀ i, Integrable (X i) μ) →
    (UniformIntegrability.SourceUniformIntegrableValue μ X ↔
      ∃ Φ : ℝ → ℝ,
        (∀ t, 0 ≤ t → 0 ≤ Φ t) ∧
        MonotoneOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧
        Tendsto (fun t => Φ t / t) atTop atTop ∧
        (⨆ i, ∫⁻ x, ENNReal.ofReal (Φ ‖X i x‖) ∂μ) < ∞)

end Specs.P207.Martingale.DeLaValleePoussin
