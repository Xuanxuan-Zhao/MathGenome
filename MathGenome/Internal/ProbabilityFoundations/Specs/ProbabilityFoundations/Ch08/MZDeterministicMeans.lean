import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Specs.ProbabilityFoundations.Ch08.MZDeterministicMeans
universe u
open Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation

/-- The deterministic drift below exponent one. No first moment is assumed. -/
noncomputable def subunitType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 1 → Integrable (fun ω => |X 0 ω| ^ p) P →
    Tendsto (fun n => (∑ k ∈ Finset.range n, ∫ ω, truncated p X k ω ∂P) /
      weight p n) atTop (𝓝 0)

/-- The centered deterministic drift for exponents strictly between one and two. -/
noncomputable def centeredType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    1 < p → p < 2 → Integrable (fun ω => |X 0 ω| ^ p) P →
    Tendsto (fun n => ((∑ k ∈ Finset.range n, ∫ ω, truncated p X k ω ∂P) -
      (n : ℝ) * (∫ ω, X 0 ω ∂P)) / weight p n) atTop (𝓝 0)

end Specs.ProbabilityFoundations.Ch08.MZDeterministicMeans
