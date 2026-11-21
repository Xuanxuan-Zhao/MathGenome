import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-! Moment necessity in Theorem `thm:mz-strong` (paper.tex:2986–2988,
3026–3034). The specified probability space need not be complete. Index `k`
is the source's index `k+1`, and `range n` contains the first n variables.
The finite limit may depend on the sample point. -/
namespace Specs.ProbabilityFoundations.Ch08.MZFiniteLimitMoment
universe u

noncomputable def finiteLimitMomentType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p c : ℝ) (Z : Ω → ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 2 →
    (∀ᵐ ω ∂P, Tendsto
      (fun n => ((∑ k ∈ Finset.range n, X k ω) - (n : ℝ) * c) /
        Ch08.MarcinkiewiczZygmundTruncation.weight p n) atTop (𝓝 (Z ω))) →
    Integrable (fun ω => |X 0 ω| ^ p) P

end Specs.ProbabilityFoundations.Ch08.MZFiniteLimitMoment
