import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Blocks.Foundations

/-! The block membership assertions of paper.tex, W38. Blocks and cut vertices
are exactly those defined in the preceding paragraph of the source. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Blocks.Membership
open Specs.FiniteCombinatorics.Graph.Blocks.Foundations

/-- Each edge, represented by either ordering of its endpoints, lies in a unique block. -/
def edge_unique_blockType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : V),
    G.Adj a b → ∃! B : BlockValue G, B.val.Adj a b

/-- Distinct blocks have at most one common vertex. -/
def distinct_blocks_intersectionType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (B C : BlockValue G),
    B ≠ C → (B.val.verts ∩ C.val.verts).Subsingleton

/-- A vertex is shared by two distinct blocks exactly when it cuts its own component. -/
def cutVertex_iff_mem_two_blocksType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    CutVertexValue G v ↔ ∃ B C : BlockValue G,
      B ≠ C ∧ v ∈ B.val.verts ∧ v ∈ C.val.verts

end Specs.FiniteCombinatorics.Graph.Blocks.Membership
