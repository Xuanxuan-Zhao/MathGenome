import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions

/-! The G-ring assertions of Theorem 5.7. -/

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u v

def completeLocal_isGRingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R], IsGRingValue R

def finiteTypeField_isGRingType : Prop :=
  ∀ (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R],
    letI := Algebra.FiniteType.isNoetherianRing k R
    IsGRingValue R

def finiteTypeInt_isGRingType : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R],
    letI := Algebra.FiniteType.isNoetherianRing ℤ R
    IsGRingValue R

end CommutativeAlgebraNotes.Excellence.Specs
