import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.Localization.Submodule

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u v

/-- The G-ring assertion of Theorem 5.14. -/
def isGRing_of_essFiniteTypeType : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] [Algebra.EssFiniteType R B],
    IsGRingValue R →
      letI := Algebra.EssFiniteType.isNoetherianRing R B
      IsGRingValue B

/-- The quasi-excellence assertion of Theorem 5.14. -/
def quasiExcellent_of_essFiniteTypeType : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.EssFiniteType R B], QuasiExcellentValue R → QuasiExcellentValue B

/-- The excellence assertion of Theorem 5.14. -/
def excellent_of_essFiniteTypeType : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.EssFiniteType R B], ExcellentValue R → ExcellentValue B

end CommutativeAlgebraNotes.Excellence.Specs
