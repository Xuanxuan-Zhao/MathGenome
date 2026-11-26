import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.OrderedValuationGroups
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.Order.GroupWithZero.WithZero

namespace Specs.CommutativeAlgebraNotes.NoetherianValuationRings

open OrderedValuationGroups (valueGroup)
open scoped WithZero

universe u v

/-- A valuation ring is Noetherian exactly in the field case or the integer value-group case. -/
def NoetherianIff : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    IsNoetherianRing V ↔ IsField V ∨ Nonempty (valueGroup V ≃+o ℤ)

/-- The integer value-group case gives a discrete valuation ring. -/
def DiscreteValuationRingOfValueGroupInt : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    Nonempty (valueGroup V ≃+o ℤ) → IsDiscreteValuationRing V

/-- The intrinsic value group of a valuation ring is trivial exactly in the field case. -/
def FieldIffTrivialValueGroup : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    IsField V ↔ Subsingleton (valueGroup V)

/-- The same ordered group condition in Mathlib's multiplicative convention with zero. -/
def IntegerValueGroupConventions : Prop :=
  ∀ {K : Type u} [Field K] (V : ValuationSubring K),
    Nonempty (valueGroup V ≃+o ℤ) ↔ Nonempty (V.ValueGroup ≃*o ℤᵐ⁰)

/-- The same additive convention for a valuation domain presented with a fraction field. -/
abbrev fractionFieldValueGroup (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :=
  (Additive (ValuationRing.ValueGroup R K)ˣ)ᵒᵈ

/-- The classification holds for any valuation domain and any choice of its fraction field. -/
def ValuationDomainClassification : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K],
    (IsNoetherianRing R ↔ IsField R ∨ Nonempty (fractionFieldValueGroup R K ≃+o ℤ)) ∧
      (Nonempty (fractionFieldValueGroup R K ≃+o ℤ) → IsDiscreteValuationRing R)

end Specs.CommutativeAlgebraNotes.NoetherianValuationRings
