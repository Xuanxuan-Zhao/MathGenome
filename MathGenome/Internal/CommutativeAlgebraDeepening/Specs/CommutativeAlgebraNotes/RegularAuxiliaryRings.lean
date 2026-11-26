import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.Separable

/-! The auxiliary-ring assertions of Lemma 5.2. -/

universe u v w

open scoped TensorProduct

namespace CommutativeAlgebraNotes.Excellence.Specs

def regularRing_polynomialType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R],
    RegularRingValue R → RegularRingValue (Polynomial R)

def regularRing_mvPolynomialType : Prop :=
  ∀ (R : Type u) (ι : Type v) [CommRing R] [IsNoetherianRing R] [Finite ι],
    RegularRingValue R → RegularRingValue (MvPolynomial ι R)

def regularRing_separableScalarExtensionType : Prop :=
  ∀ (k : Type u) (L : Type v) (R : Type w) [Field k] [Field L] [CommRing R]
    [Algebra k L] [Algebra k R] [Module.Finite k L] [Algebra.IsSeparable k L]
    [IsNoetherianRing R], RegularRingValue R → RegularRingValue (L ⊗[k] R)

def regularLocalRing_completionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    IsRegularLocalRing R → IsRegularLocalRing (AdicCompletion (IsLocalRing.maximalIdeal R) R)

def regularRing_completionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    IsRegularLocalRing R → RegularRingValue (AdicCompletion (IsLocalRing.maximalIdeal R) R)

end CommutativeAlgebraNotes.Excellence.Specs
