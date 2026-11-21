import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.ResiduallyFinite

namespace Specs.ALG02GroupTheory.Profinite

universe u

/-- GR02-C05.07. Every finitely generated abelian group is residually finite. -/
def FinitelyGeneratedAbelianResiduallyFinite : Prop :=
  ∀ (G : Type u) [CommGroup G] [Group.FG G], Group.ResiduallyFinite G

end Specs.ALG02GroupTheory.Profinite
