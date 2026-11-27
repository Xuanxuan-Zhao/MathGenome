import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Exactness of the augmented Amitsur complex under faithfully flat descent. -/

namespace AmitsurExactnessSpec

universe u v w

/-- Exactness in every integer degree of the augmented complex. -/
def Exact : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (M : ModuleCat.{max u v w} A) (q : ℤ),
    (AmitsurComplexSpec.complex A B M).ExactAt q

/-- The same assertion with the universe of the coefficients independent of both rings. -/
def LiftedExact : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (M : ModuleCat.{w} A) (q : ℤ),
    ((AmitsurComplexSpec.liftedFunctor A B).obj M).ExactAt q

end AmitsurExactnessSpec
