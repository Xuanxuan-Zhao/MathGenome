import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Foundations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! W42: signed incidence and the weighted Laplacian. Edges are exactly the
unordered edges of the common simple-graph interface, rather than ordered arcs.
The two endpoint functions allow an arbitrary, independently chosen orientation
of every edge. No order or characteristic assumption is imposed on the field.
Finite index types carry arbitrary enumerations; simultaneous row and column
reindexing preserves the principal determinant. -/

universe u v w
noncomputable section

namespace FiniteCombinatorics.Graph.Trees

/-- Canonical data shared by Specs and downstream proofs. -/
structure EdgeOrientation {V : Type u} (G : SimpleGraph V) where
  head : G.edgeSet → V
  tail : G.edgeSet → V
  edge_eq : ∀ e, s(tail e, head e) = e.val

end FiniteCombinatorics.Graph.Trees

namespace Specs.FiniteCombinatorics.Graph.Trees.Incidence
open _root_.FiniteCombinatorics.Graph.Trees

def OrientationType := ∀ {V : Type u}, SimpleGraph V → Type u

def OrientationValue : OrientationType := fun {_} G => EdgeOrientation G

def incidenceType := ∀ {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K], EdgeOrientation G → Matrix V G.edgeSet K

def incidenceValue : incidenceType := fun {_} G K _ o => by
  classical
  exact fun x e => if x = o.head e then 1 else if x = o.tail e then -1 else 0

def edgeWeightMatrixType := ∀ {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K], (G.edgeSet → K) → Matrix G.edgeSet G.edgeSet K

def edgeWeightMatrixValue : edgeWeightMatrixType := fun {_} G K _ w => by
  classical
  exact Matrix.diagonal w

def weightedLaplacianType := ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (K : Type v) [Field K], (G.edgeSet → K) → Matrix V V K

def weightedLaplacianValue : weightedLaplacianType := fun {_} G _ K _ w => by
  classical
  exact fun x y => if x = y then ∑ e : G.edgeSet, if x ∈ e.val then w e else 0
    else if h : G.Adj x y then -w ⟨s(x, y), h⟩ else 0

def principalMinorType := ∀ {V : Type u} {K : Type v}, Matrix V V K → (r : V) → Matrix {x : V // x ≠ r} {x : V // x ≠ r} K

def principalMinorValue : principalMinorType := fun {_} {_} M r => M.submatrix Subtype.val Subtype.val

def reducedIncidenceType := ∀ {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K], EdgeOrientation G → (r : V) → Matrix {x : V // x ≠ r} G.edgeSet K

def reducedIncidenceValue : reducedIncidenceType := fun {_} G K _ o r => (incidenceValue G K o).submatrix Subtype.val id

def orientation_existsType : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V), Nonempty (EdgeOrientation G)

def orientation_endpointsType : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (o : EdgeOrientation G) (e : G.edgeSet),
    G.Adj (o.tail e) (o.head e) ∧ o.tail e ≠ o.head e ∧
    ∀ x, x ∈ e.val ↔ x = o.head e ∨ x = o.tail e

def incidence_entriesType : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (K : Type v) [Field K]
    (o : EdgeOrientation G) (e : G.edgeSet),
    incidenceValue G K o (o.head e) e = 1 ∧
    incidenceValue G K o (o.tail e) e = -1 ∧
    ∀ x, x ∉ e.val → incidenceValue G K o x e = 0

def laplacian_entriesType : Prop := by
  classical
  exact ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (K : Type v) [Field K]
    (w : G.edgeSet → K),
    (∀ x, weightedLaplacianValue G K w x x =
      ∑ e : G.edgeSet, if x ∈ e.val then w e else 0) ∧
    (∀ x y (h : G.Adj x y), weightedLaplacianValue G K w x y = -w ⟨s(x, y), h⟩) ∧
    (∀ x y, x ≠ y → ¬G.Adj x y → weightedLaplacianValue G K w x y = 0)

def laplacian_factorizationType : Prop := by
  classical
  exact ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (K : Type v) [Field K]
    (o : EdgeOrientation G) (w : G.edgeSet → K),
    weightedLaplacianValue G K w =
      incidenceValue G K o * edgeWeightMatrixValue G K w * (incidenceValue G K o).transpose

def reduced_factorizationType : Prop := by
  classical
  exact ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (K : Type v) [Field K]
    (o : EdgeOrientation G) (w : G.edgeSet → K) (r : V),
    principalMinorValue (weightedLaplacianValue G K w) r =
      reducedIncidenceValue G K o r * edgeWeightMatrixValue G K w *
        (reducedIncidenceValue G K o r).transpose

/-- Every simultaneous enumeration of the surviving vertices gives the same
principal determinant, including the empty determinant for a singleton graph. -/
def principalMinor_det_reindexType : Prop := by
  classical
  exact ∀ {V : Type u} [Fintype V] {K : Type v} [Field K]
    (M : Matrix V V K) (r : V) {I : Type w} [Fintype I]
    (e : {x : V // x ≠ r} ≃ I),
    (Matrix.reindex e e (principalMinorValue M r)).det = (principalMinorValue M r).det

end Specs.FiniteCombinatorics.Graph.Trees.Incidence
