import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic

/-! The cycle-space assertions of W43. All graphs are finite and simple;
no nonemptiness or connectivity assumption is imposed. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.BinarySpaces.Cycles
open Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations

/-- The fundamental cycles themselves, with the specified nonforest-edge
indexing, are a basis of the space spanned by all simple cycles. -/
def fundamentalCycles_basisType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G),
  ∃ b : Module.Basis (NonforestEdgeValue G F) (ZMod 2) (cycleSpaceValue G),
    ∀ e, (b e).val = fundamentalCycleValue G F e

/-- Equality with the even-degree edge subsets, in the common edge coordinates. -/
def cycleSpace_iff_evenDegreeType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (S : Set (EdgeValue G)),
  edgeIndicatorValue G S ∈ cycleSpaceValue G ↔ EvenDegreeValue G S

/-- Addition before subtraction preserves the integer formula m - n + c,
including the empty graph. -/
def cycleSpace_dimensionType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Module.finrank (ZMod 2) (cycleSpaceValue G) + Nat.card V =
    Nat.card (EdgeValue G) + Nat.card G.ConnectedComponent

/-- Every nonforest edge uses the unique path in the fixed forest. -/
def nonforest_unique_pathType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G)
    (e : NonforestEdgeValue G F),
  ∃! _p : F.val.Path e.val.val.out.2 e.val.val.out.1,
    True

end Specs.FiniteCombinatorics.Graph.BinarySpaces.Cycles
