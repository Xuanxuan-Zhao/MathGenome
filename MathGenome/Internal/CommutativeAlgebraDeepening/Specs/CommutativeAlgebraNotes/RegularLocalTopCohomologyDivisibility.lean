import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.IdealTorsion
import Mathlib.RingTheory.RegularLocalRing.Defs

namespace Specs.CommutativeAlgebraNotes.RegularLocalTopCohomologyDivisibility

open IdealTorsion

universe u

/-- Every nonzero scalar acts surjectively on the top local cohomology of a regular
local ring with support in its maximal ideal. -/
def mulSurjectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → ∀ c : R, c ≠ 0 →
      Function.Surjective (fun x :
        (localCohomology (IsLocalRing.maximalIdeal R) (d : ℤ)).obj (ModuleCat.of R R) =>
        c • x)

end Specs.CommutativeAlgebraNotes.RegularLocalTopCohomologyDivisibility
