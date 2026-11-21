import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ContinuityTests

/-!
Independent proposition types for `paper.tex`, d10:02:pasting.
Each `A i` carries the subspace topology induced from X. Covering and
agreement are explicit, and neither the index type nor either space is
assumed nonempty. The first obligation includes construction and uniqueness
among all set maps; the last two include continuity of that unique map.
-/

open Set
universe u v w

namespace Specs.D10Topology.Ch02.Pasting

/-- Compatible functions on an arbitrary cover determine exactly one map.
Continuity is unnecessary for this set-theoretic part of pasting. -/
def pasting_existsUnique : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    (A : I → Set X) (f : ∀ i, A i → Y),
    (⋃ i, A i) = univ →
    (∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) →
    ∃! g : X → Y, ∀ i (a : A i), g a.val = f i a

def pasting_continuous_of_open : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y),
    (⋃ i, A i) = univ → (∀ i, Continuous (f i)) →
    (∀ i (a : A i), g a.val = f i a) →
    (∀ i, IsOpen (A i)) → Continuous g

def pasting_continuous_of_finite_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite I]
    (A : I → Set X) (f : ∀ i, A i → Y) (g : X → Y),
    (⋃ i, A i) = univ → (∀ i, Continuous (f i)) →
    (∀ i (a : A i), g a.val = f i a) →
    (∀ i, IsClosed (A i)) → Continuous g

def pasting_open : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : I → Set X) (f : ∀ i, A i → Y),
    (⋃ i, A i) = univ → (∀ i, Continuous (f i)) →
    (∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) →
    (∀ i, IsOpen (A i)) →
    ∃! g : X → Y, (∀ i (a : A i), g a.val = f i a) ∧ Continuous g

def pasting_finite_closed : Prop :=
  ∀ {X : Type u} {Y : Type v} {I : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite I]
    (A : I → Set X) (f : ∀ i, A i → Y),
    (⋃ i, A i) = univ → (∀ i, Continuous (f i)) →
    (∀ i j x (hi : x ∈ A i) (hj : x ∈ A j),
      f i ⟨x, hi⟩ = f j ⟨x, hj⟩) →
    (∀ i, IsClosed (A i)) →
    ∃! g : X → Y, (∀ i (a : A i), g a.val = f i a) ∧ Continuous g

end Specs.D10Topology.Ch02.Pasting
