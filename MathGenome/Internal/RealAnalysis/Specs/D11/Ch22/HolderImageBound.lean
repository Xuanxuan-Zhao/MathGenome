import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.DimensionDefinition

/-!
Independent statements of paper.tex:6066–6071, D11.22.holder_image_bound.
The metric spaces and subsets are arbitrary. All masses are the shared outer
masses, with no measurability condition on the domain or its image. Positive
real parameters are represented by nonnegative reals with strict positivity
hypotheses. Both dimensions are extended nonnegative reals, including infinity;
the shared definition assigns dimension zero to the empty set.
-/

noncomputable section

open Set
open scoped NNReal ENNReal

universe u v

namespace Specs.D11.Ch22.HolderImageBound

/-- The full coefficient-one quantitative estimate for every positive exponent. -/
def measureImageStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (α C : ℝ≥0),
    0 < α → α ≤ 1 → 0 < C →
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) →
    ∀ s : ℝ≥0, 0 < s →
      HausdorffOuterMeasure.outerMeasureValue (s / α) (f '' E) ≤
        (C : ℝ≥0∞) ^ ((s / α : ℝ≥0) : ℝ) *
          HausdorffOuterMeasure.outerMeasureValue s E

/-- The dimension estimate, without finiteness or nonemptiness hypotheses. -/
def dimensionImageStatement : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (α C : ℝ≥0),
    0 < α → α ≤ 1 → 0 < C →
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) →
    DimensionDefinition.dimensionValue (f '' E) ≤
      DimensionDefinition.dimensionValue E / (α : ℝ≥0∞)

end Specs.D11.Ch22.HolderImageBound
