import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
Theorem 6.8 (`paper.tex:1115–1129`).  The fields, fraction-field models and
finite extensions are arbitrary.  The scalar towers only express compatibility
of the displayed structure maps; no separability or perfection is required.
-/
namespace P103.Specs.Ch06.AffineIntegralClosureFinite

universe u v w x

/-- Finiteness and the affine domain conclusion, over every base field. -/
def affine_integral_closureType : Prop :=
  ∀ (k : Type u) (A : Type v) (K : Type w) (L : Type x)
    [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra k L] [IsScalarTower k A L] [Module.Finite K L],
    Module.Finite A (integralClosure A L) ∧
      Algebra.FiniteType k (integralClosure A L) ∧ IsDomain (integralClosure A L)

/-- The normalization reduction identifies the actual integral-element sets.
It also transfers finiteness back to the larger ring. -/
def normalization_reductionType : Prop :=
  ∀ (B : Type u) (A : Type v) (L : Type w)
    [CommRing B] [CommRing A] [CommRing L]
    [Algebra B A] [Algebra A L] [Algebra B L] [IsScalarTower B A L]
    [Module.Finite B A],
    (integralClosure A L).restrictScalars B = integralClosure B L ∧
      (Module.Finite B (integralClosure B L) → Module.Finite A (integralClosure A L))

end P103.Specs.Ch06.AffineIntegralClosureFinite
