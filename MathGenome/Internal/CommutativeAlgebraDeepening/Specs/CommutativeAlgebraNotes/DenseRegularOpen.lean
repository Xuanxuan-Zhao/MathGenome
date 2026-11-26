import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u v

/-- A nonempty open of the spectrum on which all prime-local rings are regular. -/
def HasNonemptyRegularOpen (A : Type v) [CommRing A] : Prop :=
  ∃ U : Set (PrimeSpectrum A), IsOpen U ∧ U.Nonempty ∧ U ⊆ regularLocusValue A

def denseRegularOpen_fieldType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A], HasNonemptyRegularOpen A

def denseRegularOpen_intType : Prop :=
  ∀ (A : Type v) [CommRing A] [IsDomain A]
    [Algebra.FiniteType ℤ A], HasNonemptyRegularOpen A

def denseRegularOpen_completeLocalType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing A] [IsDomain A]
    [Algebra R A] [Algebra.FiniteType R A], HasNonemptyRegularOpen A

end CommutativeAlgebraNotes.Excellence.Specs
