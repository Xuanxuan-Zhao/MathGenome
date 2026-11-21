import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarInterfaces

/-! Independent statements of `paper.tex:4589`, Hahn decomposition.
The variation below is the raw supremum of measurable finite-partition costs;
its being a measure is not a hypothesis or part of its definition. -/

open Set MeasureTheory
open scoped symmDiff

universe u

namespace Specs.D11.Ch14.Hahn

open Specs.D11.Ch14.ScalarInterfaces

/-- A measurable positive/negative partition exists for every real-valued
countably additive signed measure on every measurable space. -/
def hahn_exists : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α),
    ∃ P N : Set α, positiveSet_value ν P ∧ negativeSet_value ν N ∧
      Disjoint P N ∧ P ∪ N = univ

/-- For any two Hahn partitions, every measurable subset of the symmetric
difference of their positive parts has signed measure zero, and the raw
partition variation of that symmetric difference is zero. -/
def hahn_unique : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (ν : SignedMeasure α)
    (P N P' N' : Set α),
    positiveSet_value ν P → negativeSet_value ν N →
    Disjoint P N → P ∪ N = univ →
    positiveSet_value ν P' → negativeSet_value ν N' →
    Disjoint P' N' → P' ∪ N' = univ →
    (∀ A : Set α, MeasurableSet A → A ⊆ P ∆ P' → ν A = 0) ∧
      partitionVariation_value ν (P ∆ P') = 0

end Specs.D11.Ch14.Hahn
