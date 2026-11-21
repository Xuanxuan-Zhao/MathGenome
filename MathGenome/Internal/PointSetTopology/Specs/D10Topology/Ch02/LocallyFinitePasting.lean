import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.Pasting
import Mathlib.Topology.LocallyFinite

/-!
Independent statements for `paper.tex`, d10:02:locally-finite-closed and
d10:02:locally-finite-pasting. The canonical indexed predicate is Mathlib's
`LocallyFinite`; its equivalence with the paper's open-neighborhood definition
is an explicit obligation. The finite set is a set of indices, so repeated
nonempty members count separately. Subtypes carry their induced topologies.
No finiteness, nonemptiness, or separation assumptions on the spaces or index
type are imposed.
-/

open Set
universe u v w

namespace Specs.D10Topology.Ch02.LocallyFinitePasting

def locallyFinite_iff_open_neighborhood : Prop :=
  ∀ {X : Type u} {I : Type w} [TopologicalSpace X] (A : I → Set X),
    LocallyFinite A ↔ ∀ x : X, ∃ U : Set X,
      IsOpen U ∧ x ∈ U ∧ {i | (A i ∩ U).Nonempty}.Finite

def locallyFinite_iUnion_isClosed : Prop :=
  ∀ {X : Type u} {I : Type w} [TopologicalSpace X] (A : I → Set X),
    LocallyFinite A → (∀ i, IsClosed (A i)) → IsClosed (⋃ i, A i)

/-- The containing family need not itself consist of closed sets. -/
def locallyFinite_iUnion_isClosed_of_subset : Prop :=
  ∀ {X : Type u} {I : Type w} [TopologicalSpace X] (A F : I → Set X),
    LocallyFinite A → (∀ i, F i ⊆ A i) →
    (∀ i, IsClosed (F i)) → IsClosed (⋃ i, F i)

def pasting_continuous_of_locallyFinite_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y),
    (⋃ i, A i) = univ → (∀ i, Continuous (f i)) →
    (∀ i (a : A i), g a.val = f i a) →
    (∀ i, IsClosed (A i)) → LocallyFinite A → Continuous g

def pasting_locallyFinite_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : I → Set X) (f : ∀ i, A i → Y),
    (⋃ i, A i) = univ → (∀ i, Continuous (f i)) →
    (∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) →
    (∀ i, IsClosed (A i)) → LocallyFinite A →
    ∃! g : X → Y, (∀ i (a : A i), g a.val = f i a) ∧ Continuous g

end Specs.D10Topology.Ch02.LocallyFinitePasting
