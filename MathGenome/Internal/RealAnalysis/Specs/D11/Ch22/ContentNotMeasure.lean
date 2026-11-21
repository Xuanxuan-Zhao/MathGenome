import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.OuterVolume

/-! Independent statements for paper.tex:6164–6172.

The square is the shared closed box in `Point 2`, with its Euclidean l2
metric. Unrestricted content omits the diameter bound from the shared scale
content definition. Empty sequence entries represent unused cover slots and
have cost zero; every nonempty entry has cost one at exponent zero.
-/

noncomputable section
open Set Metric
open scoped NNReal ENNReal

universe u

namespace Specs.D11.Ch22.ContentNotMeasure
open _root_.D11.Ch03

def unrestrictedContentType : Type (u + 1) :=
  {X : Type u} → [MetricSpace X] → ℝ≥0 → Set X → ℝ≥0∞

/-- The infimum over all at most countable covers by arbitrary subsets,
without any upper bound on their diameters. -/
def unrestrictedContentValue : unrestrictedContentType :=
  fun {X} _ s E =>
    ⨅ (U : ℕ → Set X) (_ : E ⊆ ⋃ n, U n),
      ∑' n, ⨆ _ : (U n).Nonempty, ediam (U n) ^ (s : ℝ)

def squareDiameterStatement : Prop :=
  ediam (closedBox (0 : Fin 2 → ℝ) 1) = ENNReal.ofReal (Real.sqrt 2)

/-- Large-scale diameter content differs from the small-scale Hausdorff
outer mass, even on the compact unit square. -/
def contentNotMeasureStatement : Prop :=
  unrestrictedContentValue 1 (closedBox (0 : Fin 2 → ℝ) 1) ≤
      ENNReal.ofReal (Real.sqrt 2) ∧
    HausdorffOuterMeasure.outerMeasureValue 1 (closedBox (0 : Fin 2 → ℝ) 1) = ∞

end Specs.D11.Ch22.ContentNotMeasure
