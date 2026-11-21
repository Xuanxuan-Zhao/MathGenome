import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures
import Mathlib.Topology.Homotopy.Contractible

/-! The quotient conclusion of paper.tex, Proposition 2.4.
The quotient identifies precisely the points of the given subcomplex, and
has the ordinary quotient topology. The forward homotopy equivalence is
required to be the quotient projection itself. -/

noncomputable section
universe u
open Set Topology ContinuousMap

namespace P202.Cellular

/-- Equality outside `A`, with all points of `A` identified. -/
def collapseSetoid {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) : Setoid X where
  r x y := x = y ∨ (x ∈ A.carrier ∧ y ∈ A.carrier)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | ⟨hx, hy⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx⟩
    trans := by
      intro x y z h k
      rcases h with rfl | ⟨hx, hy⟩
      · exact k
      rcases k with rfl | ⟨_, hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩ }

/-- The space `X/A`, with the quotient topology supplied by `Quotient`. -/
abbrev Collapse {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) := Quotient (collapseSetoid A)

/-- The actual quotient projection. -/
def collapseProjection {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) : C(X, Collapse A) :=
  ⟨Quotient.mk (collapseSetoid A), continuous_quotient_mk'⟩

end P202.Cellular

namespace P202Specs.Topology.ContractibleCollapse
open P202.Cellular

/-- Every nonempty contractible CW subcomplex can be collapsed by a
homotopy equivalence. No dimension or finiteness restriction is imposed. -/
def contractibleCollapse : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CWStructure X] (A : Subcomplex X),
    A.carrier.Nonempty → ContractibleSpace A →
    ∃ e : X ≃ₕ Collapse A, e.toFun = collapseProjection A

end P202Specs.Topology.ContractibleCollapse
