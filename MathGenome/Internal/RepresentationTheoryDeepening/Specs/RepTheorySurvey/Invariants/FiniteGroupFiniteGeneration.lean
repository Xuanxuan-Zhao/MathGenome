import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import Mathlib.RingTheory.FiniteType

universe u v w

namespace RepTheorySurvey.Invariants.Specs

/-- Finite-group invariants are of finite type, and the ambient algebra is finite
as a module over the invariant subalgebra. -/
def FiniteGroupFiniteGeneration : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w}
    [Field k] [Group G] [Finite G] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (ρ : GroupAlgebraAction k G A),
    Algebra.FiniteType k (groupFixedSubalgebra ρ) ∧ Module.Finite (groupFixedSubalgebra ρ) A

end RepTheorySurvey.Invariants.Specs
