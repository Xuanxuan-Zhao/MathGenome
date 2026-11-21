import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.ResiduallyFinite

namespace Specs.ALG02GroupTheory.Profinite.FreeGroup

universe u

/-- Each nonidentity element of the free group on an arbitrary type of generators
survives in a finite quotient. -/
def existsFiniteQuotient : Prop :=
  ∀ {α : Type u} (g : _root_.FreeGroup α), g ≠ 1 →
    ∃ (Q : Type) (_ : Group Q) (_ : Finite Q) (f : _root_.FreeGroup α →* Q),
      Function.Surjective f ∧ f g ≠ 1

/-- GR02-C05.08. Every free group is residually finite. -/
def residuallyFinite : Prop :=
  ∀ {G : Type u} [Group G] [IsFreeGroup G], Group.ResiduallyFinite G

end Specs.ALG02GroupTheory.Profinite.FreeGroup
