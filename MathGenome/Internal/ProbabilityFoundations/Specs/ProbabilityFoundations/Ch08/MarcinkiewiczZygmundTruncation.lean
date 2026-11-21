import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.IndependenceInterfaces
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.ProbabilityBounds
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-! The truncation stage of `thm:mz-strong`, paper.tex:2992–3008.
`X k` is the source's `X_{k+1}`. Thus `range n` contains exactly the first
n variables, while the truncation level at index k is `(k+1)^(1/p)`.
Only the p-th absolute moment is assumed; first moments of X are not assumed.
The measure and sigma algebra are the original, possibly incomplete ones. -/
namespace Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation
universe u

noncomputable def weight (p : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (1 / p)

noncomputable def truncated {Ω : Type u} (p : ℝ) (X : ℕ → Ω → ℝ)
    (k : ℕ) : Ω → ℝ :=
  {ω | |X k ω| ≤ weight p (k + 1)}.indicator (X k)

noncomputable def truncationProbabilitiesType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 2 → Integrable (fun ω => |X 0 ω| ^ p) P →
    (∑' k, P {ω | X k ω ≠ truncated p X k ω}) < ∞

noncomputable def weightedVariancesType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 2 → Integrable (fun ω => |X 0 ω| ^ p) P →
    Summable (fun k => Ch01.ProbabilityBounds.realVarianceValue P (truncated p X k) /
      ((k + 1 : ℕ) : ℝ) ^ (2 / p))

noncomputable def centeredTruncationType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    Ch02.IndependenceInterfaces.IndependentRandomElementsValue P X →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 2 → Integrable (fun ω => |X 0 ω| ^ p) P →
    ∀ᵐ ω ∂P, Tendsto
      (fun n => (weight p n)⁻¹ * ∑ k ∈ Finset.range n,
        (truncated p X k ω - ∫ t, truncated p X k t ∂P)) atTop (𝓝 0)

noncomputable def eventuallyConstantDifferenceType : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    0 < p → p < 2 → Integrable (fun ω => |X 0 ω| ^ p) P →
    ∀ᵐ ω ∂P, ∃ c : ℝ, ∀ᶠ n in atTop,
      (∑ k ∈ Finset.range n, X k ω) -
        (∑ k ∈ Finset.range n, truncated p X k ω) = c

end Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation
