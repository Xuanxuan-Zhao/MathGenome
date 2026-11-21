import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.UniformIntegrabilityInterfaces
import Mathlib.Analysis.Convex.Function

/-! The equivalence of conditions (1) and (3) in Theorem 1.10.
A real-valued function restricted to `Ici 0` represents a finite function
on the nonnegative half-line. The integral and its supremum are extended
nonnegative integrals, so empty families and unbounded suprema are meaningful.
The integrability hypothesis is exactly the source's `H ⊆ L¹(μ)`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

universe u v

namespace Specs.ProbabilityFoundations.Ch01.DeLaValleePoussin

def criterionType : Prop :=
  ∀ {S : Type u} {E : Type v} [MeasurableSpace S] [NormedAddCommGroup E]
    (μ : Measure S) [IsFiniteMeasure μ] (H : Set (S → E)),
    (∀ f ∈ H, Integrable f μ) →
    (UniformIntegrabilityInterfaces.SourceUniformIntegrableValue μ H ↔
      ∃ Φ : ℝ → ℝ,
        MonotoneOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧
        (∀ t, 0 ≤ t → 0 ≤ Φ t) ∧ Φ 0 = 0 ∧
        Tendsto (fun t => Φ t / t) atTop atTop ∧
        (⨆ f ∈ H, ∫⁻ x, ENNReal.ofReal (Φ ‖f x‖) ∂μ) < ∞)

end Specs.ProbabilityFoundations.Ch01.DeLaValleePoussin
