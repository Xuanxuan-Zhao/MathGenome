import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations

/-! Independent W48 vertex-Menger interface. Paths are the shared Mathlib
vertex-simple paths. A family is a finite set of paths (no repeated members).
A separator is a finite set, excludes both endpoints, and meets every path.
The deletion interpretation is specified explicitly in `separator_iff_deletion`.
The final proposition includes both attained extrema and the disconnected case. -/

universe u
noncomputable section
namespace FiniteCombinatorics.Graph.VertexMengerSpec
variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- The vertices of a simple path other than its two endpoints. -/
def interior (p : G.Path s t) : Finset V := by
  classical
  exact p.val.support.toFinset.filter (fun v => v ≠ s ∧ v ≠ t)

/-- Pairwise internally vertex-disjoint simple paths. -/
def IsPacking (P : Finset (G.Path s t)) : Prop :=
  (P : Set (G.Path s t)).Pairwise (fun p q => Disjoint (interior p) (interior q))

/-- Endpoint-excluding vertex separators, in their equivalent path-hitting form. -/
def IsSeparator (G : SimpleGraph V) (s t : V) (S : Finset V) : Prop :=
  s ∉ S ∧ t ∉ S ∧ ∀ p : G.Path s t, ∃ v ∈ S, v ∈ p.val.support

/-- An actual maximum packing, an actual minimum separator, and their equality. -/
def EqualWitnesses (G : SimpleGraph V) (s t : V) : Prop :=
  ∃ (P : Finset (G.Path s t)) (S : Finset V),
    IsPacking P ∧ IsSeparator G s t S ∧ P.card = S.card ∧
    (∀ Q : Finset (G.Path s t), IsPacking Q → Q.card ≤ P.card) ∧
    (∀ T : Finset V, IsSeparator G s t T → S.card ≤ T.card)

/-- The graph obtained by deleting S has the surviving vertices as its type. -/
def AvoidingReachable (G : SimpleGraph V) (s t : V) (S : Finset V)
    (hs : s ∉ S) (ht : t ∉ S) : Prop :=
  (G.induce {v | v ∉ S}).Reachable ⟨s, hs⟩ ⟨t, ht⟩

def separator_iff_deletion : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (s t : V) (S : Finset V)
    (hs : s ∉ S) (ht : t ∉ S),
    IsSeparator G s t S ↔ ¬ AvoidingReachable G s t S hs ht

def packing_le_separator : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (s t : V)
    (P : Finset (G.Path s t)) (S : Finset V),
    IsPacking P → IsSeparator G s t S → P.card ≤ S.card

def extrema_attained : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s t : V),
    s ≠ t → ¬G.Adj s t →
    (∃ P : Finset (G.Path s t), IsPacking P ∧
      ∀ Q : Finset (G.Path s t), IsPacking Q → Q.card ≤ P.card) ∧
    (∃ S : Finset V, IsSeparator G s t S ∧
      ∀ T : Finset V, IsSeparator G s t T → S.card ≤ T.card)

/-- Nonadjacency yields an endpoint-excluding separator of size n-2,
and bounds the cardinality of every internally disjoint family. -/
def internal_bound : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s t : V),
    s ≠ t → ¬G.Adj s t →
    (∃ S : Finset V, IsSeparator G s t S ∧ S.card = Nat.card V - 2) ∧
    (∀ P : Finset (G.Path s t), IsPacking P → P.card ≤ Nat.card V - 2)

def disconnected_zero : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s t : V),
    ¬G.Reachable s t →
    EqualWitnesses G s t ∧
    (∀ P : Finset (G.Path s t), IsPacking P → P.card = 0) ∧
    IsSeparator G s t ∅

def equal_card_suffices : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (s t : V)
    (P : Finset (G.Path s t)) (S : Finset V),
    IsPacking P → IsSeparator G s t S → P.card = S.card → EqualWitnesses G s t

/-- W48, with no endpoint separator, nonadjacency, both attained extrema,
and zero for an already separated pair. -/
def vertex_menger : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (s t : V),
    s ≠ t → ¬G.Adj s t →
    EqualWitnesses G s t ∧
    (¬G.Reachable s t →
      (∀ P : Finset (G.Path s t), IsPacking P → P.card = 0) ∧
      IsSeparator G s t ∅)

end FiniteCombinatorics.Graph.VertexMengerSpec
