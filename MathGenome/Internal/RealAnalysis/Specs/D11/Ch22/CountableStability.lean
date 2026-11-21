import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.DimensionDefinition

/-!
Independent specification for paper.tex:6093–6099,
`D11.22.countable_stability`.

All sets are arbitrary subsets of genuine metric spaces. The dimension is the
shared infimum of zero exponents for coefficient-one diameter-cover outer mass.
The index type may be any countable type, including an empty type: its supremum
in `ℝ≥0∞` is then zero. No measurable structure is imposed.
-/

noncomputable section

open Set
open scoped NNReal ENNReal

universe u v

namespace Specs.D11.Ch22.CountableStability

def monotoneStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X],
    Monotone (DimensionDefinition.dimensionValue (X := X))

def countableUnionStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] {ι : Type v} [Countable ι] (E : ι → Set X),
    DimensionDefinition.dimensionValue (⋃ i, E i) =
      ⨆ i, DimensionDefinition.dimensionValue (E i)

def singletonStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (x : X),
    DimensionDefinition.dimensionValue ({x} : Set X) = 0

def countableSetStatement : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X),
    E.Countable → DimensionDefinition.dimensionValue E = 0

end Specs.D11.Ch22.CountableStability
