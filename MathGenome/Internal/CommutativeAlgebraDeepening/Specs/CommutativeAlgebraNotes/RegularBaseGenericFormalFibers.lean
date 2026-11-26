import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions
import Mathlib.RingTheory.Localization.FractionRing

namespace CommutativeAlgebraNotes.Excellence.Specs

open scoped TensorProduct
open IsLocalRing
open _root_.Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions

/-- The generic formal fibre, presented with its fraction field as the left
tensor factor so the scalar action is the canonical left tensor action. -/
abbrev GenericFormalFiber (S : Type*) [CommRing S] (K : Type*) [Field K]
    [Algebra S K] (q : Ideal S) [q.IsPrime] :=
  K ⊗[S] AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)

/-- The characteristic-zero case of the regular-base argument in Theorem 5.7. -/
def regularBaseGenericFormalFiberCharZeroType : Prop :=
  ∀ (S K : Type*) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K]
    [Algebra S K] [IsFractionRing S K] [CharZero K],
    RegularRingValue S → ∀ (q : Ideal S) [q.IsPrime],
      GeometricallyRegularValue K (GenericFormalFiber S K q)

/-- The positive-characteristic case over a field of arbitrary imperfection
degree. Both the power-series and polynomial variable sets may be empty. -/
def regularBaseGenericFormalFiberCharPType : Prop :=
  ∀ (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (r s : ℕ),
    let S := CoefficientTowerBase k r s
    ∀ (q : Ideal S) [q.IsPrime],
      GeometricallyRegularValue (FractionRing S) (GenericFormalFiber S (FractionRing S) q)

end CommutativeAlgebraNotes.Excellence.Specs
