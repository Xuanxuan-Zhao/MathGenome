import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Foundations
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Allowed-edge coordinates for paper.tex, Scope and conventions, W35 and
Bipartite assignment and its dual (W40--W43). The two summands keep the
parts disjoint, including when their underlying types coincide. No vertex
is discarded, even when it has no allowed neighbor. There are no hypotheses
of nonemptiness, perfect matchability, or positivity of weights.
-/

set_option linter.checkUnivs false

universe u v
noncomputable section
open scoped BigOperators
namespace Specs.P205.Matching

abbrev BipartiteGraph (L : Type u) (R : Type v) := L → R → Prop
variable {L : Type u} {R : Type v}

abbrev Edge (G : BipartiteGraph L R) := {p : L × R // G p.1 p.2}

instance edgeFintype [Fintype L] [Fintype R] (G : BipartiteGraph L R) :
    Fintype (Edge G) := Fintype.ofFinite _

/-- A simple graph on all vertices, with precisely the allowed cross edges. -/
def graph (G : BipartiteGraph L R) : SimpleGraph (L ⊕ R) where
  Adj a b := match a, b with
    | .inl i, .inr j => G i j
    | .inr j, .inl i => G i j
    | _, _ => False
  symm := ⟨by intro a b; cases a <;> cases b <;> simp⟩
  loopless := ⟨by intro a; cases a <;> simp⟩

def incident {G : BipartiteGraph L R} (v : L ⊕ R) (e : Edge G) : Prop :=
  match v with
  | .inl i => i = e.val.1
  | .inr j => j = e.val.2

/-- Endpoint-injectivity on each side; in particular the empty set is a matching. -/
def IsMatching {G : BipartiteGraph L R} (M : Set (Edge G)) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e.val.1 = f.val.1 → e = f) ∧
  (∀ e ∈ M, ∀ f ∈ M, e.val.2 = f.val.2 → e = f)

def Covered {G : BipartiteGraph L R} (M : Set (Edge G)) (v : L ⊕ R) : Prop :=
  ∃ e ∈ M, incident v e

def IsPerfectMatching {G : BipartiteGraph L R} (M : Set (Edge G)) : Prop :=
  IsMatching M ∧ ∀ v, Covered M v

def indicator {G : BipartiteGraph L R} (M : Set (Edge G)) : Edge G → ℝ := by
  classical
  exact fun e => if e ∈ M then 1 else 0

/-- Unsigned integer vertex--edge incidence; exactly two ones per column. -/
def incidence (G : BipartiteGraph L R) : Matrix (L ⊕ R) (Edge G) ℤ := by
  classical
  exact fun v e => if incident v e then 1 else 0

/-- Number of chosen incident edges, with isolates having degree zero. -/
def degree {G : BipartiteGraph L R} (M : Set (Edge G)) (v : L ⊕ R) : ℕ :=
  Nat.card {e : Edge G // e ∈ M ∧ incident v e}

def load [Fintype L] [Fintype R] {G : BipartiteGraph L R}
    (x : Edge G → ℝ) (v : L ⊕ R) : ℝ :=
  ∑ e, (incidence G v e : ℝ) * x e

def totalWeight [Fintype L] [Fintype R] {G : BipartiteGraph L R}
    (w x : Edge G → ℝ) : ℝ := ∑ e, w e * x e

def matchingWeight [Fintype L] [Fintype R] {G : BipartiteGraph L R}
    (w : Edge G → ℝ) (M : Set (Edge G)) : ℝ := totalWeight w (indicator M)

def potentialSum [Fintype L] [Fintype R] (u : L → ℝ) (v : R → ℝ) : ℝ :=
  (∑ i, u i) + ∑ j, v j

/-- Free potentials: no sign conditions are imposed. -/
def FreeFeasible {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (u : L → ℝ) (v : R → ℝ) : Prop :=
  ∀ e, w e ≤ u e.val.1 + v e.val.2

def NonnegativeFeasible {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (u : L → ℝ) (v : R → ℝ) : Prop :=
  FreeFeasible w u v ∧ (∀ i, 0 ≤ u i) ∧ ∀ j, 0 ≤ v j

def slack {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (u : L → ℝ) (v : R → ℝ) (e : Edge G) : ℝ :=
  u e.val.1 + v e.val.2 - w e

def Tight {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (u : L → ℝ) (v : R → ℝ) (e : Edge G) : Prop :=
  u e.val.1 + v e.val.2 = w e

def UsesTightEdges {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (M : Set (Edge G)) (u : L → ℝ) (v : R → ℝ) : Prop :=
  ∀ e ∈ M, Tight w u v e

/-- The unordered edge corresponding to an allowed coordinate. -/
def edgePair {G : BipartiteGraph L R} (e : Edge G) : Sym2 (L ⊕ R) :=
  s(Sum.inl e.val.1, Sum.inr e.val.2)

def edgeSet {G : BipartiteGraph L R} (M : Set (Edge G)) : Set (Sym2 (L ⊕ R)) :=
  edgePair '' M

/-- Read the allowed coordinates of an arbitrary Mathlib subgraph. -/
def coordinates {G : BipartiteGraph L R} (H : (graph G).Subgraph) : Set (Edge G) :=
  {e | H.Adj (.inl e.val.1) (.inr e.val.2)}

/-- The subgraph with these edges and exactly their incident vertices. -/
def subgraph {G : BipartiteGraph L R} (M : Set (Edge G)) : (graph G).Subgraph where
  verts := {v | Covered M v}
  Adj a b := ∃ e ∈ M,
    (a = .inl e.val.1 ∧ b = .inr e.val.2) ∨
    (a = .inr e.val.2 ∧ b = .inl e.val.1)
  adj_sub := by
    rintro a b ⟨e, he, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩ <;> exact e.property
  edge_vert := by
    rintro a b ⟨e, he, h | h⟩ <;> rcases h with ⟨rfl, rfl⟩ <;> exact ⟨e, he, rfl⟩
  symm := ⟨by
    rintro a b ⟨e, he, h | h⟩
    · exact ⟨e, he, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨e, he, Or.inl ⟨h.2, h.1⟩⟩⟩

/- Expected types for the public definitions; their expected values are the
independent definitions above. -/
def BipartiteGraphType := Type u → Type v → Type (max u v)

def EdgeType := ∀ {L : Type u} {R : Type v}, BipartiteGraph L R → Type (max u v)

def graphType := ∀ {L : Type u} {R : Type v}, BipartiteGraph L R → SimpleGraph (L ⊕ R)

def incidentType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (L ⊕ R) → Edge G → Prop

def IsMatchingType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → Prop

def CoveredType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → (L ⊕ R) → Prop

def IsPerfectMatchingType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → Prop

def indicatorType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → Edge G → ℝ

def incidenceType := ∀ {L : Type u} {R : Type v}, (G : BipartiteGraph L R) → Matrix (L ⊕ R) (Edge G) ℤ

def degreeType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → (L ⊕ R) → ℕ

def loadType := ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R], {G : BipartiteGraph L R} → (Edge G → ℝ) → (L ⊕ R) → ℝ

def matchingWeightType := ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R], {G : BipartiteGraph L R} → (Edge G → ℝ) → Set (Edge G) → ℝ

def totalWeightType := ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R], {G : BipartiteGraph L R} → (Edge G → ℝ) → (Edge G → ℝ) → ℝ

def potentialSumType := ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R], (L → ℝ) → (R → ℝ) → ℝ

def FreeFeasibleType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Prop

def NonnegativeFeasibleType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Prop

def slackType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Edge G → ℝ

def TightType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Edge G → Prop

def UsesTightEdgesType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (Edge G → ℝ) → Set (Edge G) → (L → ℝ) → (R → ℝ) → Prop

def edgePairType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Edge G → Sym2 (L ⊕ R)

def edgeSetType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → Set (Sym2 (L ⊕ R))

def coordinatesType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → (graph G).Subgraph → Set (Edge G)

def subgraphType := ∀ {L : Type u} {R : Type v}, {G : BipartiteGraph L R} → Set (Edge G) → (graph G).Subgraph

/- Full propositions for representation and incidence transport. -/
def graph_adj_lrType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (i : L) (j : R), (graph G).Adj (.inl i) (.inr j) ↔ G i j

def graph_adj_llType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (i k : L), ¬ (graph G).Adj (.inl i) (.inl k)

def graph_adj_rrType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (j k : R), ¬ (graph G).Adj (.inr j) (.inr k)

def edgePair_injectiveType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, Function.Injective (@edgePair L R G)

def edgePair_mem_graphType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (e : Edge G), edgePair e ∈ (graph G).edgeSet

def edgePair_rangeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, Set.range (@edgePair L R G) = (graph G).edgeSet

def edgeSet_subsetType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (M : Set (Edge G)), edgeSet M ⊆ (graph G).edgeSet

def subgraph_edgeSetType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (M : Set (Edge G)), (subgraph M).edgeSet = edgeSet M

def coordinates_subgraphType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (M : Set (Edge G)), coordinates (subgraph M) = M

def edgeSet_coordinatesType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, ∀ (H : (graph G).Subgraph), edgeSet (coordinates H) = H.edgeSet

def covered_iff_saturatedType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)) (v : L ⊕ R), Covered M v ↔ FiniteCombinatorics.Graph.Matching.Saturated (edgeSet M) v

def matching_iff_mathGenomeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), IsMatching M ↔ FiniteCombinatorics.Graph.Matching.IsMatching (graph G) (edgeSet M)

def matching_iff_mathlibType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), IsMatching M ↔ (subgraph M).IsMatching

def perfect_iff_mathGenomeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), IsPerfectMatching M ↔
      FiniteCombinatorics.Graph.Matching.IsPerfectMatching (graph G) (edgeSet M)

def perfect_iff_mathlibType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), IsPerfectMatching M ↔ (subgraph M).IsPerfectMatching

def subgraph_coordinatesType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ {H : (graph G).Subgraph} (_h : H.IsMatching), subgraph (coordinates H) = H

def indicator_zero_oneType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)) (e : Edge G), indicator M e = 0 ∨ indicator M e = 1

def incidence_leftType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (e : Edge G), incidence G (.inl e.val.1) e = 1

def incidence_rightType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (e : Edge G), incidence G (.inr e.val.2) e = 1

def empty_matchingType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], IsMatching (∅ : Set (Edge G))

def matching_iff_degreeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), IsMatching M ↔ ∀ v, degree M v ≤ 1

def covered_iff_degree_posType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)) (v : L ⊕ R), Covered M v ↔ 0 < degree M v

def perfect_iff_degreeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), IsPerfectMatching M ↔ ∀ v, degree M v = 1

def edge_transportType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∃ f : Edge G ≃ (graph G).edgeSet,
    ∀ e, (f e).val = edgePair e

def matching_transportType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∃ f : {M : Set (Edge G) // IsMatching M} ≃
    {H : (graph G).Subgraph // H.IsMatching},
    (∀ M, (f M).val = subgraph M.val) ∧
    (∀ H, (f.symm H).val = coordinates H.val)

def perfect_transportType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∃ f : {M : Set (Edge G) // IsPerfectMatching M} ≃
    {H : (graph G).Subgraph // H.IsPerfectMatching},
    (∀ M, (f M).val = subgraph M.val) ∧
    (∀ H, (f.symm H).val = coordinates H.val)

def load_indicatorType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)) (v : L ⊕ R), load (indicator M) v = (degree M v : ℝ)

def preimage_edgeSetType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (M : Set (Edge G)), edgePair ⁻¹' edgeSet M = M

def edgeSet_preimageType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (S : Set (Sym2 (L ⊕ R))) (_hS : S ⊆ (graph G).edgeSet), edgeSet ((@edgePair L R G) ⁻¹' S) = S

def matching_preimage_mathGenomeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (S : Set (Sym2 (L ⊕ R)))
    (_hS : S ⊆ (graph G).edgeSet), IsMatching ((@edgePair L R G) ⁻¹' S) ↔
      FiniteCombinatorics.Graph.Matching.IsMatching (graph G) S

def perfect_preimage_mathGenomeType : Prop :=
  ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], ∀ (S : Set (Sym2 (L ⊕ R)))
    (_hS : S ⊆ (graph G).edgeSet), IsPerfectMatching ((@edgePair L R G) ⁻¹' S) ↔
      FiniteCombinatorics.Graph.Matching.IsPerfectMatching (graph G) S

end Specs.P205.Matching
