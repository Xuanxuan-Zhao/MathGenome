import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.Foundations
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Independent propositions for paper.tex W58 (lines 2134–2154).
Bipartiteness uses Mathlib's two-colorability predicate; cycles are the shared
vertex-simple closed walks, and the chromatic number is the shared natural minimum.
No nonemptiness assumption is imposed on the characterization. -/

universe u
namespace Specs.FiniteCombinatorics.Graph.Coloring.Bipartite

/-- An odd closed walk contains an odd simple cycle using only its edges. -/
def odd_closed_walk_exists_odd_cycleType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (a : V) (p : G.Walk a a),
    Odd p.length → ∃ (b : V) (c : Specs.FiniteCombinatorics.Graph.Foundations.CycleValue G b),
      Odd c.val.length ∧ ∀ e ∈ c.val.edges, e ∈ p.edges

def bipartite_iff_no_odd_cycleType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    G.IsBipartite ↔ ∀ (a : V) (c : Specs.FiniteCombinatorics.Graph.Foundations.CycleValue G a), ¬ Odd c.val.length

def bipartite_two_coloringType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    G.IsBipartite → Nonempty (Foundations.KColoringValue G 2)

def bipartite_chromaticNumber_le_twoType : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
    G.IsBipartite → Foundations.chromaticNumberValue G ≤ 2

end Specs.FiniteCombinatorics.Graph.Coloring.Bipartite
