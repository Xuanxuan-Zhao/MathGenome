import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Module.Pi

/-! Independent definitions for the binary edge spaces in paper.tex, W43.
The edge index is the subtype of the common graph's unordered edge set.
No connectivity or nonemptiness hypothesis is imposed on the graph.
A spanning forest has the same vertices and preserves all reachability. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations

/-- The very same unordered edges used by the graph foundation. -/
def EdgeType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u
abbrev EdgeValue : EdgeType := fun {_} _ G => G.edgeSet

def EdgeVectorType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u
abbrev EdgeVectorValue : EdgeVectorType := fun {_} _ G => EdgeValue G → ZMod 2

def edgeIndicatorType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Set (EdgeValue G) → EdgeVectorValue G
def edgeIndicatorValue : edgeIndicatorType := fun {_} _ _ S e => by
  classical
  exact if e ∈ S then 1 else 0

def edgeSupportType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  EdgeVectorValue G → Set (EdgeValue G)
def edgeSupportValue : edgeSupportType := fun {_} _ _ x => {e | x e ≠ 0}

/-- Every binary coordinate is zero or one, so indicators identify all subsets
with the whole coordinate vector space, including when there are no edges. -/
def edgeSetEquivType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Set (EdgeValue G) ≃ EdgeVectorValue G
def edgeSetEquivValue : edgeSetEquivType := fun {_} _ G => {
  toFun := edgeIndicatorValue G
  invFun := edgeSupportValue G
  left_inv := by
    classical
    intro S
    ext e
    simp [edgeSupportValue, edgeIndicatorValue]
  right_inv := by
    classical
    intro x
    funext e
    dsimp only [edgeIndicatorValue, edgeSupportValue, Set.mem_ofPred_eq]
    have h : x e = 0 ∨ x e = 1 := by
      have hlt := (x e).isLt
      change (x e).val < 2 at hlt
      have hv : (x e).val = 0 ∨ (x e).val = 1 := by omega
      rcases hv with hv | hv
      · left; exact Fin.ext hv
      · right; exact Fin.ext hv
    rcases h with h | h <;> simp [h]
}

/-- Exactly one endpoint lies in the vertex set. The existential form makes
independence of an ordering of an unordered edge explicit. -/
def cutEdgesType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Set V → Set (EdgeValue G)
def cutEdgesValue : cutEdgesType := fun {_} _ _ S =>
  {e | ∃ a b, e.val = s(a, b) ∧ a ∈ S ∧ b ∉ S}

def cutVectorType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Set V → EdgeVectorValue G
def cutVectorValue : cutVectorType := fun {_} _ G S =>
  edgeIndicatorValue G (cutEdgesValue G S)

def cutSpaceType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Submodule (ZMod 2) (EdgeVectorValue G)
def cutSpaceValue : cutSpaceType := fun {_} _ G =>
  Submodule.span (ZMod 2) (Set.range (cutVectorValue G))

/-- Edge sets of walks are taken without multiplicity. For a simple cycle,
this is exactly its edge indicator. -/
def walkVectorType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {a b : V}, G.Walk a b → EdgeVectorValue G
def walkVectorValue : walkVectorType := fun {_} _ G {_ _} p =>
  edgeIndicatorValue G {e | e.val ∈ p.edges}

def cycleSpaceType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Submodule (ZMod 2) (EdgeVectorValue G)
def cycleSpaceValue : cycleSpaceType := fun {_} _ G =>
  Submodule.span (ZMod 2) {x | ∃ (a : _) (p : G.Walk a a),
    p.IsCycle ∧ x = walkVectorValue G p}

def dotProductType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  EdgeVectorValue G → EdgeVectorValue G → ZMod 2
def dotProductValue : dotProductType := fun {_} _ G x y =>
  letI := Fintype.ofFinite (EdgeValue G)
  ∑ e, x e * y e

/-- Degree in an edge subset counts precisely its incident unordered edges. -/
def EvenDegreeType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Set (EdgeValue G) → Prop
def EvenDegreeValue : EvenDegreeType := fun {_} _ G S =>
  ∀ v, Even (Nat.card {e : EdgeValue G // e ∈ S ∧ v ∈ e.val})

/-- Acyclic spanning subgraph with exactly the original components. -/
def SpanningForestType := ∀ {V : Type u} [Finite V], SimpleGraph V → Type u
abbrev SpanningForestValue : SpanningForestType := fun {_} _ G =>
  {F : SimpleGraph _ // F ≤ G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable}

def NonforestEdgeType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  SpanningForestValue G → Type u
abbrev NonforestEdgeValue : NonforestEdgeType := fun {_} _ G F =>
  {e : EdgeValue G // e.val ∉ F.val.edgeSet}

def ForestEdgeType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  SpanningForestValue G → Type u
abbrev ForestEdgeValue : ForestEdgeType := fun {_} _ G F =>
  {e : EdgeValue G // e.val ∈ F.val.edgeSet}

/-- The forest path from the second endpoint back to the first. Its existence
uses preservation of components, and not connectedness of the whole graph. -/
def forestPathType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  (F : SpanningForestValue G) (e : EdgeValue G),
  F.val.Path e.val.out.2 e.val.out.1
def forestPathValue : forestPathType := fun {_} _ G F e =>
  Classical.choice (by
    suffices h : F.val.Reachable e.val.out.2 e.val.out.1 from
      h.elim_path (fun p => ⟨p⟩)
    rw [F.property.2.2]
    have ha : G.Adj e.val.out.1 e.val.out.2 := by
      change s(e.val.out.1, e.val.out.2) ∈ G.edgeSet
      rw [Sym2.mk_fst_out_snd_out]
      exact e.property
    exact ha.symm.reachable)

/-- Close the unique forest path with the new edge. The implementation proves
that this closed walk is a simple cycle. -/
def fundamentalCycleWalkType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  (F : SpanningForestValue G) (e : NonforestEdgeValue G F),
  G.Walk e.val.val.out.1 e.val.val.out.1
def fundamentalCycleWalkValue : fundamentalCycleWalkType := fun {_} _ G F e =>
  SimpleGraph.Walk.cons (by
    change s(e.val.val.out.1, e.val.val.out.2) ∈ G.edgeSet
    rw [Sym2.mk_fst_out_snd_out]
    exact e.val.property)
    ((forestPathValue G F e.val).val.mapLe F.property.1)

def fundamentalCycleType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  (F : SpanningForestValue G), NonforestEdgeValue G F → EdgeVectorValue G
def fundamentalCycleValue : fundamentalCycleType := fun {_} _ G F e =>
  walkVectorValue G (fundamentalCycleWalkValue G F e)

/-- One side is the component of the first endpoint after removing the edge.
This selects just that side of its forest tree, even in disconnected graphs. -/
def fundamentalCutSideType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  (F : SpanningForestValue G), ForestEdgeValue G F → Set V
def fundamentalCutSideValue : fundamentalCutSideType := fun {_} _ _ F e =>
  {v | (F.val.deleteEdges {e.val.val}).Reachable e.val.val.out.1 v}

def fundamentalCutType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  (F : SpanningForestValue G), ForestEdgeValue G F → EdgeVectorValue G
def fundamentalCutValue : fundamentalCutType := fun {_} _ G F e =>
  cutVectorValue G (fundamentalCutSideValue G F e)

/-! Expected propositions are full types, not assumed certificates. -/
def indicator_symmDiffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (S T : Set (EdgeValue G)),
  edgeIndicatorValue G (symmDiff S T) = edgeIndicatorValue G S + edgeIndicatorValue G T

def cut_membershipType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (S : Set V) (a b : V)
  (h : G.Adj a b),
  (⟨s(a, b), h⟩ : EdgeValue G) ∈ cutEdgesValue G S ↔
    (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)

def exists_spanningForestType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V), Nonempty (SpanningForestValue G)

def forestPath_uniqueType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G)
  (e : EdgeValue G) (p : F.val.Path e.val.out.2 e.val.out.1),
  p = forestPathValue G F e

def fundamentalCycle_isCycleType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G)
  (e : NonforestEdgeValue G F), (fundamentalCycleWalkValue G F e).IsCycle

def fundamentalCut_separatesType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (F : SpanningForestValue G)
  (e : ForestEdgeValue G F),
  e.val.val.out.1 ∈ fundamentalCutSideValue G F e ∧
  e.val.val.out.2 ∉ fundamentalCutSideValue G F e

end Specs.FiniteCombinatorics.Graph.BinarySpaces.Foundations
