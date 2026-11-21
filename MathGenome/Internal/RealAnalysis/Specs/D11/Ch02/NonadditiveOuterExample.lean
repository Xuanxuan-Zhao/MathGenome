import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.Caratheodory

/-!
Independent specification of paper.tex:745–755. The two distinct points `a,b`
are represented by `false,true : Bool`; `univ` is therefore exactly `{a,b}`.
The cost is defined on every subset, without an ambient measurable space.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch02.NonadditiveOuterExample

/-- The source set function, before proving the outer-measure axioms. -/
noncomputable def cost (E : Set Bool) : ℝ≥0∞ :=
  if E = ∅ then 0 else 1

/-- All assertions of the nonadditive two-point example, including the exact
Carathéodory sigma-algebra and the whole-space witness against each singleton. -/
def nonadditive_outer_example : Prop :=
  ∃ m : OuterMeasure Bool,
    (∀ E : Set Bool, m E = cost E) ∧
    Monotone (fun E : Set Bool => m E) ∧
    (∀ E : ℕ → Set Bool, m (⋃ n, E n) ≤ ∑' n, m (E n)) ∧
    Disjoint ({false} : Set Bool) {true} ∧
    m univ = 1 ∧
    m {false} + m {true} = 2 ∧
    m univ ≠ m {false} + m {true} ∧
    (∀ b : Bool, m univ ≠ m (univ ∩ {b}) + m (univ \ {b})) ∧
    (∀ S : Set Bool,
      _root_.Specs.D11.Ch02.Caratheodory.isMeasurable_value m S ↔
        S = ∅ ∨ S = univ) ∧
    {S : Set Bool |
      MeasurableSet[_root_.Specs.D11.Ch02.Caratheodory.measurableSpace_value m] S} =
        {∅, univ}

end Specs.D11.Ch02.NonadditiveOuterExample
