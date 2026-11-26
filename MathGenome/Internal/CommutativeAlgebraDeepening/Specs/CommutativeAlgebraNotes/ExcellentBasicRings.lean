import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions

/-! The excellence assertions for the basic rings in Theorem 5.9. -/

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u v

def completeLocal_excellentType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R], ExcellentValue R

def field_excellentType : Prop :=
  ∀ (k : Type u) [Field k], ExcellentValue k

def int_excellentType : Prop :=
  ExcellentValue ℤ

def finiteTypeField_excellentType : Prop :=
  ∀ (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R], ExcellentValue R

def finiteTypeInt_excellentType : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R], ExcellentValue R

end CommutativeAlgebraNotes.Excellence.Specs
