import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarInterfaces

/-! Independent statement of the negative-set extraction lemma
(`paper.tex`, label `d11:14:negative-extraction`). -/

open Set MeasureTheory

universe u

namespace Specs.D11.Ch14.NegativeExtraction

/-- Every measurable set contains a measurable negative set of no larger
signed measure. Real-valued signed measures have finite scalar values;
no positivity or sigma-finiteness is assumed. -/
def negative_extraction : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (E : Set α), MeasurableSet E →
    ∃ N : Set α, N ⊆ E ∧
      Specs.D11.Ch14.ScalarInterfaces.negativeSet_value ν N ∧ ν N ≤ ν E

end Specs.D11.Ch14.NegativeExtraction
