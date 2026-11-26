import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u v

def isOpen_regularLocus_fieldType : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A], IsOpen (regularLocusValue A)

def isOpen_regularLocus_intType : Prop :=
  ∀ (A : Type v) [CommRing A] [Algebra.FiniteType ℤ A],
    IsOpen (regularLocusValue A)

def isOpen_regularLocus_completeLocalType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A], IsOpen (regularLocusValue A)

end CommutativeAlgebraNotes.Excellence.Specs
