import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GraphicRank
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteDefinition
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial

/-! The chromatic specialization of W77, with the original unordered edge
labels. All spanning graphs retain their full vertex type, including isolated
vertices. The incidence matroid is independent of the field and orientation
by the upstream graphic-incidence theorem. -/
universe u v
noncomputable section
namespace FiniteCombinatorics.Matroid.Graphic

/-- Finiteness of the indexed graph associated to a finite simple graph. -/
theorem simpleFinite {V : Type u} [Finite V] (G : SimpleGraph V) :
    Specs.FiniteCombinatorics.Graph.MultigraphFoundation.IsFiniteValue
      (_root_.Graph.ofSimpleGraph G) := ⟨Set.toFinite _, Set.toFinite _⟩

/-- A fixed choice of endpoints, used only to select the canonical incidence
presentation. Its matroid is independent of this choice. -/
def simpleOrientation {V : Type u} (G : SimpleGraph V) :
    Orientation (_root_.Graph.ofSimpleGraph G) where
  tail e := Classical.choose ((_root_.Graph.ofSimpleGraph G).exists_isLink_of_mem_edgeSet e.property)
  head e := Classical.choose (Classical.choose_spec
    ((_root_.Graph.ofSimpleGraph G).exists_isLink_of_mem_edgeSet e.property))
  link e := Classical.choose_spec (Classical.choose_spec
    ((_root_.Graph.ofSimpleGraph G).exists_isLink_of_mem_edgeSet e.property))

/-- The cycle matroid on exactly the graph's original unordered edge labels. -/
def cycleMatroid {V : Type u} [Finite V] (G : SimpleGraph V) : _root_.Matroid (Sym2 V) :=
  incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) ℚ (simpleOrientation G)

instance cycleMatroidFinite {V : Type u} [Finite V] (G : SimpleGraph V) :
    (cycleMatroid G).Finite := by unfold cycleMatroid; infer_instance

end FiniteCombinatorics.Matroid.Graphic
namespace Specs.FiniteCombinatorics.Matroid.TutteChromatic
open _root_.FiniteCombinatorics.Matroid
open _root_.FiniteCombinatorics.Matroid.Graphic
open Polynomial

/-- Polynomial identity, without a nonempty-vertex or nonempty-edge hypothesis. -/
def chromaticSpecialization : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial G =
    (-1 : ℤ[X]) ^ ((cycleMatroid G).eRk (cycleMatroid G).E).toNat *
    X ^ Nat.card G.ConnectedComponent *
    Expected.tutteSubstitute (Expected.tutte (cycleMatroid G)) (1 - X) 0

/-- The substitution formula holds in every incidence presentation of M(G). -/
def chromaticSpecializationIncidence : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : Orientation (_root_.Graph.ofSimpleGraph G)),
  let M := incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o
  Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.chromaticPolynomial G =
    (-1 : ℤ[X]) ^ (M.eRk M.E).toNat * X ^ Nat.card G.ConnectedComponent *
      Expected.tutteSubstitute (Expected.tutte M) (1 - X) 0

/-- The ground consists of the original unordered graph edges. -/
def cycleMatroidGround : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V),
  (cycleMatroid G).E = G.edgeSet

def cycleMatroidIndep : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (A : Set (Sym2 V)),
  (cycleMatroid G).Indep A ↔ Forest (_root_.Graph.ofSimpleGraph G) A

def cycleMatroidInvariant : Prop :=
  ∀ {V : Type u} [Finite V] (G : SimpleGraph V) (K : Type v) [Field K]
    (o : Orientation (_root_.Graph.ofSimpleGraph G)),
  cycleMatroid G = incidenceMatroid (_root_.Graph.ofSimpleGraph G) (simpleFinite G) K o

/-- All components of the spanning subgraph, including isolated vertices. -/
def cycleMatroidRank : Prop := ∀ {V : Type u} [Finite V] (G : SimpleGraph V)
    (A : Finset (Sym2 V)), (A : Set (Sym2 V)) ⊆ G.edgeSet →
  Expected.rank (cycleMatroid G) (A : Set (Sym2 V)) = (Nat.card V : ℤ) -
    (Specs.FiniteCombinatorics.Graph.Coloring.ChromaticPolynomial.spanningComponentCount A : ℤ)

/-- The right side of W77 reduces to the edgeless chromatic polynomial. -/
def edgelessSpecialization : Prop := ∀ {V : Type u} [Finite V],
  let G : SimpleGraph V := ⊥
  (-1 : ℤ[X]) ^ ((cycleMatroid G).eRk (cycleMatroid G).E).toNat *
    X ^ Nat.card G.ConnectedComponent *
    Expected.tutteSubstitute (Expected.tutte (cycleMatroid G)) (1 - X) 0 =
      X ^ Nat.card V

/-- No vertices gives the constant polynomial one. -/
def emptySpecialization : Prop := ∀ {V : Type u} [Finite V] [IsEmpty V]
    (G : SimpleGraph V),
  (-1 : ℤ[X]) ^ ((cycleMatroid G).eRk (cycleMatroid G).E).toNat *
    X ^ Nat.card G.ConnectedComponent *
    Expected.tutteSubstitute (Expected.tutte (cycleMatroid G)) (1 - X) 0 = 1

end Specs.FiniteCombinatorics.Matroid.TutteChromatic
