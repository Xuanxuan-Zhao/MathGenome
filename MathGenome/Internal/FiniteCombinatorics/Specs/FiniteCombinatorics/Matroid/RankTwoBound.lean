import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ParallelClasses

/-! The finite-field bound in paper.tex W73. Simplicity is stated explicitly:
every ground element is a nonloop, and related nonloops are equal. The ambient
space in a representation is arbitrary; only the matroid ground is finite. -/
namespace FiniteCombinatorics.Matroid.Expected
universe u v w
open Set

def rankTwoBoundOfRepresents : Prop :=
  ∀ {α : Type u} (K : Type v) [Field K] [Finite K]
    {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) [M.Finite] (v : α → V),
    Represents K M v →
    (∀ e ∈ M.E, M.IsNonloop e) →
    (∀ e ∈ M.E, ∀ f ∈ M.E, ParallelRelated M e f → e = f) →
    rank M M.E = 2 → M.E.ncard ≤ Nat.card K + 1

def rankTwoBound : Prop :=
  ∀ {α : Type u} (K : Type v) [Field K] [Finite K]
    (M : _root_.Matroid α) [M.Finite],
    Representable.{u,v,w} K M →
    (∀ e ∈ M.E, M.IsNonloop e) →
    (∀ e ∈ M.E, ∀ f ∈ M.E, ParallelRelated M e f → e = f) →
    rank M M.E = 2 → M.E.ncard ≤ Nat.card K + 1

end FiniteCombinatorics.Matroid.Expected
