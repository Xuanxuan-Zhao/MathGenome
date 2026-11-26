import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularLocalTopClass
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularLocalTopCohomologyDivisibility

open CategoryTheory HomologicalComplex

namespace Specs.CommutativeAlgebraNotes.RegularLocalTopCohomology

open IdealTorsion (localCohomology)
open RegularLocalTopClass (cechFractionClass)

universe u

/-- The reciprocal of the product of a minimal ordered list of maximal-ideal
generators represents a nonzero top local cohomology class. Every nonzero scalar
acts surjectively on the same top local cohomology module. -/
def TopCohomology : Prop :=
  ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) →
    (∀ (rs : List R), rs.length = d → Ideal.span {r | r ∈ rs} = IsLocalRing.maximalIdeal R →
      ∃ (e : localCohomology (IsLocalRing.maximalIdeal R) (rs.length : ℤ) ≅
          (single (ModuleCat.{u} R) (.up ℤ) 0 ⋙ AugmentedCechComplex.tensorFunctor R rs) ⋙
            homologyFunctor (ModuleCat.{u} R) (.up ℤ) (rs.length : ℤ))
        (h : (AugmentedCechComplex.coefficients R rs (ModuleCat.of R R)).d
          (rs.length : ℤ) ((rs.length : ℤ) + 1) = 0),
        e.inv.app (ModuleCat.of R R) (cechFractionClass rs h) ≠ 0) ∧
    (∀ c : R, c ≠ 0 →
      Function.Surjective (fun x :
        (localCohomology (IsLocalRing.maximalIdeal R) (d : ℤ)).obj (ModuleCat.of R R) =>
        c • x))

end Specs.CommutativeAlgebraNotes.RegularLocalTopCohomology
