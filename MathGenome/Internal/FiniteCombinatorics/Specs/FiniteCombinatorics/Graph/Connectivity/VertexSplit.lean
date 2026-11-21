import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Foundations
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

/-! The concrete finite vertex-splitting construction in W48, paper.tex
lines 1748–1778. The two endpoints are unsplit. Transit identities are ordered
original edges; no assumed transport or small-cut certificate is used. -/

open scoped BigOperators
noncomputable section
universe u
namespace FiniteCombinatorics.Graph.VertexSplitSpec
open FiniteCombinatorics.Directed FiniteCombinatorics.Graph.Flows

variable {V : Type u} [Fintype V]

abbrev Internal (s t : V) := {v : V // v ≠ s ∧ v ≠ t}
abbrev Vertex (s t : V) := Fin 2 ⊕ (Internal s t × Bool)
abbrev Edge (G : SimpleGraph V) := {e : V × V // G.Adj e.1 e.2}
abbrev Arc (G : SimpleGraph V) (s t : V) := Internal s t ⊕ Edge G

instance (s t : V) : Fintype (Internal s t) := by
  classical
  unfold Internal
  infer_instance
instance (s t : V) : Fintype (Vertex s t) := by unfold Vertex; infer_instance
instance (G : SimpleGraph V) : Fintype (Edge G) := by
  classical
  unfold Edge
  infer_instance
instance (G : SimpleGraph V) (s t : V) : Fintype (Arc G s t) := by unfold Arc; infer_instance

def source (s t : V) : Vertex s t := .inl 0
def sink (s t : V) : Vertex s t := .inl 1

def input (s t v : V) : Vertex s t := by
  classical
  exact if hs : v = s then source s t else
    if ht : v = t then sink s t else .inr (⟨v, hs, ht⟩, false)

def output (s t v : V) : Vertex s t := by
  classical
  exact if hs : v = s then source s t else
    if ht : v = t then sink s t else .inr (⟨v, hs, ht⟩, true)

def original (s t : V) : Vertex s t → V
  | .inl i => if i = 0 then s else t
  | .inr v => v.1.val

def graph (G : SimpleGraph V) (s t : V) : Digraph (Vertex s t) (Arc G s t) where
  tail a := match a with
    | .inl v => .inr (v, false)
    | .inr e => output s t e.val.1
  head a := match a with
    | .inl v => .inr (v, true)
    | .inr e => input s t e.val.2

def capacityNat (G : SimpleGraph V) (s t : V) : Arc G s t → ℕ
  | .inl _ => 1
  | .inr _ => Fintype.card V

def network (G : SimpleGraph V) (s t : V) : Network (Vertex s t) (Arc G s t) where
  graph := graph G s t
  capacity a := capacityNat G s t a
  capacity_nonneg a := Nat.cast_nonneg _
  source := source s t
  sink := sink s t
  source_ne_sink := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj h)

def splitArcs (G : SimpleGraph V) (s t : V) : Finset (Arc G s t) := by
  classical
  exact Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

def initialCut (s t : V) : Set (Vertex s t) :=
  {x | x = source s t ∨ ∃ v : Internal s t, x = .inr (v, false)}

def separator (G : SimpleGraph V) (s t : V) (U : Set (Vertex s t)) : Finset V := by
  classical
  exact ((Finset.univ : Finset (Internal s t)).filter
    (fun v => Sum.inr (v, false) ∈ U ∧ Sum.inr (v, true) ∉ U)).image Subtype.val

abbrev DirectedPath (G : SimpleGraph V) (s t : V) :=
  Directed.Spec.path (graph G s t) (source s t) (sink s t)

/-- Remove the split steps and retain the ordered endpoints of every transit. -/
def transitSequence (G : SimpleGraph V) (s t : V) (l : List (Arc G s t)) : List (V × V) :=
  l.filterMap (fun a => match a with
    | .inl _ => none
    | .inr e => some e.val)

/-- Complete ordered path transport, with split-arc occurrence equivalence.
The sublist assertion states that the projected vertices occur in their original
order, represented by output copies, in the original directed path. -/
def path_transport : Prop := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
  (s t : V), s ≠ t → ¬G.Adj s t →
  ∃ (project : DirectedPath G s t → G.Path s t)
    (lift : G.Path s t → DirectedPath G s t),
    (∀ p, project (lift p) = p) ∧
    (∀ p, (project p).val.darts.map (fun d => (d.fst, d.snd)) =
      transitSequence G s t (Directed.Spec.arcs p.val)) ∧
    (∀ p, ((project p).val.support.map (output s t)).Sublist
      (Directed.Spec.vertices p.val)) ∧
    (∀ p (v : Internal s t), v.val ∈ (project p).val.support ↔
      Sum.inl v ∈ Directed.Spec.arcs p.val) ∧
    (∀ p : DirectedPath G s t, ∃ a ∈ splitArcs G s t, a ∈ Directed.Spec.arcs p.val)

def initial_cut : Prop := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
  (s t : V), s ≠ t → ¬G.Adj s t →
  Flows.Spec.isCut (network G s t) (initialCut s t) ∧
  Flows.Spec.outgoing (network G s t) (initialCut s t) = splitArcs G s t ∧
  Flows.Spec.cutCapacity (network G s t) (initialCut s t) = ((Fintype.card V - 2 : ℕ) : ℝ)

def small_cut : Prop := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
  (s t : V), s ≠ t → ¬G.Adj s t →
  ∀ U : Set (Vertex s t), Flows.Spec.isCut (network G s t) U →
    Flows.Spec.cutCapacity (network G s t) U ≤ ((Fintype.card V - 2 : ℕ) : ℝ) →
    (∀ e : Edge G, Sum.inr e ∉ Flows.Spec.outgoing (network G s t) U) ∧
    s ∉ separator G s t U ∧ t ∉ separator G s t U ∧
    ((separator G s t U).card : ℝ) = Flows.Spec.cutCapacity (network G s t) U ∧
    (∀ p : G.Path s t, ∃ v ∈ separator G s t U, v ∈ p.val.support) ∧
    (∀ v : Internal s t, v.val ∈ separator G s t U ↔
      Sum.inl v ∈ Flows.Spec.outgoing (network G s t) U)

/-- Natural capacities, including their values on both kinds of original arc. -/
def capacities : Prop := ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (s t : V),
  (∀ a, (network G s t).capacity a = (capacityNat G s t a : ℝ)) ∧
  (∀ v : Internal s t, capacityNat G s t (.inl v) = 1) ∧
  (∀ e : Edge G, capacityNat G s t (.inr e) = Fintype.card V) ∧
  (∀ a, a ∈ splitArcs G s t ↔ ∃ v : Internal s t, a = .inl v)

end FiniteCombinatorics.Graph.VertexSplitSpec
