import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions

universe u v

namespace CommutativeAlgebraNotes.Excellence.Specs

/-- The finite-algebra assertion of Theorem 5.9. -/
def FiniteAlgebraExcellent : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B], ExcellentValue A → ExcellentValue B

/-- The localization assertion of Theorem 5.9 for any multiplicative set. -/
def LocalizedExcellent : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B], ExcellentValue A → ExcellentValue B

end CommutativeAlgebraNotes.Excellence.Specs
