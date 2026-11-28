import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.RationalActionComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.RingTheory.FiniteType

open LinearAlgebraicGroups
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive IsSplitTorus)

universe u

namespace RepTheorySurvey.Invariants.Specs

open RationalActionComparison (KPoints HasRegularOrbits)

/-- The algebra of invariants under all base-field points of a connected reductive
group in characteristic zero is of finite type. -/
def ReductiveFiniteGeneration : Prop :=
  ∀ {k A : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left],
    IsReductive G →
    ∀ ρ : GroupAlgebraAction k (KPoints G.val) A,
      HasRegularOrbits (groupRepresentation ρ) →
      Algebra.FiniteType k (groupFixedSubalgebra ρ)

/-- The same finite generation statement holds for rational split torus actions
over an algebraically closed field of arbitrary characteristic. -/
def SplitTorusFiniteGeneration : Prop :=
  ∀ {k A : Type u} [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (T : GroupScheme k), IsSplitTorus T →
    ∀ ρ : GroupAlgebraAction k (KPoints T) A,
      HasRegularOrbits (groupRepresentation ρ) →
      Algebra.FiniteType k (groupFixedSubalgebra ρ)

end RepTheorySurvey.Invariants.Specs
