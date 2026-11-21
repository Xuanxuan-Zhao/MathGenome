import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-! Independent interfaces for the definitions preceding W39, its zero-edge clauses,
and Hamilton cycles. Closed walks may have length zero. All edges are undirected
(`Sym2 V`); isolated vertices are allowed. -/

universe u
noncomputable section
namespace Specs.FiniteCombinatorics.Graph.Euler.Foundations

def IsTrailType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {a b : V}, G.Walk a b → Prop

def IsTrailValue : IsTrailType := fun {_} _ _ {_ _} p => p.IsTrail

def IsEulerTrailType := IsTrailType

def IsEulerTrailValue : IsEulerTrailType := fun {_} _ G {_ _} p =>
  IsTrailValue G p ∧ ∀ e, e ∈ G.edgeSet → e ∈ p.edges

def IsClosedType := IsTrailType

def IsClosedValue : IsClosedType := fun {_} _ _ {a b} _ => a = b

def IsOpenType := IsTrailType

def IsOpenValue : IsOpenType := fun {_} _ _ {a b} _ => a ≠ b

def edgeSupportVerticesType := ∀ {V : Type u} [Finite V], SimpleGraph V → Set V

def edgeSupportVerticesValue : edgeSupportVerticesType := fun {_} _ G =>
  {v | 0 < Specs.FiniteCombinatorics.Graph.Foundations.degreeValue G v}

def edgeSupportType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  SimpleGraph (edgeSupportVerticesValue G)

def edgeSupportValue : edgeSupportType := fun {_} _ G => G.induce (edgeSupportVerticesValue G)

def IsHamiltonCycleType := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
  {a : V}, G.Walk a a → Prop

def IsHamiltonCycleValue : IsHamiltonCycleType := fun {_} _ _ {_} p =>
  p.IsCycle ∧ ∀ v, v ∈ p.support

def HamiltonCycleType := ∀ {V : Type u} [Finite V], (G : SimpleGraph V) → V → Type u

def HamiltonCycleValue : HamiltonCycleType := fun {_} _ G a =>
  {p : G.Walk a a // IsHamiltonCycleValue G p}

def trail_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b),
    IsTrailValue G p ↔ p.edges.Nodup

def eulerTrail_iffType : Prop :=
  ∀ {V : Type u} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (p : G.Walk a b),
    IsEulerTrailValue G p ↔ ∀ e, e ∈ G.edgeSet → p.edges.count e = 1

def eulerTrail_mathlibType : Prop :=
  ∀ {V : Type u} [Finite V] [DecidableEq V] (G : SimpleGraph V)
    {a b : V} (p : G.Walk a b), IsEulerTrailValue G p ↔ p.IsEulerian

def eulerTrail_edgeSetType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b),
    IsEulerTrailValue G p ↔ IsTrailValue G p ∧ p.edgeSet = G.edgeSet

def closed_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b),
    IsClosedValue G p ↔ a = b

def open_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) {a b : V} (p : G.Walk a b),
    IsOpenValue G p ↔ a ≠ b

def edgeSupportVertices_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    v ∈ edgeSupportVerticesValue G ↔
      0 < Specs.FiniteCombinatorics.Graph.Foundations.degreeValue G v

def edgeSupportVertices_iff_exists_adjType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (v : V),
    v ∈ edgeSupportVerticesValue G ↔ ∃ w, G.Adj v w

def edgeSupport_adjacencyType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a b : edgeSupportVerticesValue G),
    (edgeSupportValue G).Adj a b ↔ G.Adj a.val b.val

def hamiltonCycle_iffType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) {a : V} (p : G.Walk a a),
    IsHamiltonCycleValue G p ↔
      3 ≤ p.length ∧ p.support.dropLast.Nodup ∧ ∀ v, v ∈ p.support

def hamiltonCycle_mathlibType : Prop :=
  ∀ {V : Type u} [Finite V] [DecidableEq V] (G : SimpleGraph V) {a : V} (p : G.Walk a a),
    IsHamiltonCycleValue G p ↔ p.IsHamiltonianCycle

def nil_closed_eulerTrailType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (_h : G.edgeSet = ∅) (a : V),
    IsEulerTrailValue G (.nil : G.Walk a a) ∧ IsClosedValue G (.nil : G.Walk a a)

def zero_length_closed_eulerTrailType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (_h : G.edgeSet = ∅)
    {a b : V} (p : G.Walk a b), p.length = 0 →
    IsEulerTrailValue G p ∧ IsClosedValue G p

def exists_closed_eulerTrail_of_no_edgesType : Prop :=
  ∀ {V : Type u} [Finite V] [Nonempty V] (G : SimpleGraph V), G.edgeSet = ∅ →
    ∃ (a : V) (p : G.Walk a a), IsEulerTrailValue G p ∧ IsClosedValue G p ∧ p.length = 0

def empty_no_walkType : Prop :=
  ∀ {V : Type u} [Finite V] [IsEmpty V] (G : SimpleGraph V),
    ¬ ∃ (a b : V), Nonempty (G.Walk a b)

end Specs.FiniteCombinatorics.Graph.Euler.Foundations
