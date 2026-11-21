import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Basic

/-! The cut-space conclusions of paper.tex W43, in the adopted common-edge
coordinates. Empty graphs and isolated vertices are included throughout. -/
universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.BinarySpaces.Cuts
attribute [local instance] Classical.propDecidable
open Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations

/-- The cut uses the component of one endpoint in the forest with that edge
removed. Among all forest edges its support is precisely the deleted edge. -/
def fundamentalCut_forest_supportType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G)
    (e f : ForestEdgeValue G F),
    fundamentalCutValue G F e f.val = if e = f then 1 else 0

def cutSpace_exists_cutType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (x : EdgeVectorValue G),
    x ∈ cutSpaceValue G → ∃ S : Set V, x = cutVectorValue G S

def fundamentalCuts_basisType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G),
    ∃ b : Module.Basis (ForestEdgeValue G F) (ZMod 2) (cutSpaceValue G),
      ∀ e, (b e).val = fundamentalCutValue G F e

/-- The additive formula avoids a truncated-subtraction ambiguity at n = 0. -/
def cutSpace_dimensionType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    Module.finrank (ZMod 2) (cutSpaceValue G) + Nat.card G.ConnectedComponent = Nat.card V

def cycle_cut_orthogonalType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (x y : EdgeVectorValue G),
    x ∈ cycleSpaceValue G → y ∈ cutSpaceValue G → dotProductValue G x y = 0

/-- The equivalent edge-subset parity statement uses the actual common edges. -/
def evenDegree_cut_intersectionType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (H : Set (EdgeValue G)) (S : Set V),
    EvenDegreeValue G H → Even (Nat.card {e : EdgeValue G // e ∈ H ∧ e ∈ cutEdgesValue G S})

end Specs.FiniteCombinatorics.Graph.BinarySpaces.Cuts
