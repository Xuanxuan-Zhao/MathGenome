import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import Mathlib.RingTheory.FiniteType

open LinearAlgebraicGroups

universe u

namespace RepTheorySurvey.Invariants.Specs

/-- A Reynolds operator preserving finite-dimensional subcomodules gives finite
generation of the invariants of a finite-type rational algebra. -/
def RationalFilteredFiniteGeneration : Prop :=
  ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {H : HopfAlgebraCategory k} (ρ : RationalAlgebraAction H A)
    (R : A →ₗ[k] rationalFixedSubalgebra ρ),
    rationalIsReynolds ρ R →
    (∀ W : Submodule k A, (rationalToRightComodule ρ).IsSubcomodule W →
      FiniteDimensional k W → ∀ x ∈ W, (R x : A) ∈ W) →
    Algebra.FiniteType k (rationalFixedSubalgebra ρ)

end RepTheorySurvey.Invariants.Specs
