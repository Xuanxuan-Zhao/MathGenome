import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.Localization.FractionRing

/-! The characteristic-zero integer case of the generic formal fibre theorem. -/

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence.Specs

universe u

/-- The generic base change of the completion of the prime local ring. -/
noncomputable abbrev integerGenericFiber (A : Type u) [CommRing A] [IsDomain A]
    (p : Ideal A) [p.IsPrime] : Type u :=
  let R := Localization.AtPrime p
  let T := AdicCompletion (IsLocalRing.maximalIdeal R) R
  FractionRing A ⊗[A] T

def integerGenericFormalFiberType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
    Function.Injective (algebraMap ℤ A) →
    ∀ (p : Ideal A) [p.IsPrime], GeometricallyRegularValue (FractionRing A) (integerGenericFiber A p)

end CommutativeAlgebraNotes.Excellence.Specs
