import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularLocalTopClass
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularLocalTopCohomologyDivisibility
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.RegularLocalTopCohomology

namespace CommutativeAlgebraNotes

universe u

/-- The top local cohomology of a regular local ring contains the nonzero
reciprocal class of a minimal generating list, and every nonzero scalar acts
surjectively on it. -/
theorem regularLocalTopCohomology :
    Specs.CommutativeAlgebraNotes.RegularLocalTopCohomology.TopCohomology.{u} := by
  intro R _ _ d hd
  constructor
  · intro rs hlen hgen
    apply RegularLocalTopClass.topClass_nonzero rs
    · simpa only [hlen] using hd
    · exact hgen
  · exact regularLocalTopCohomology_mul_surjective (R := R) d hd

end CommutativeAlgebraNotes
