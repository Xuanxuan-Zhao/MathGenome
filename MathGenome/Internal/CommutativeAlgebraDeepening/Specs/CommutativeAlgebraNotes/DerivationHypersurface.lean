import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExtendDerivations
import Mathlib.Algebra.Polynomial.Basic

/-! Lemma 5.3 and its principal-quotient criterion used in Lemma 5.13. -/

universe u v

namespace CommutativeAlgebraNotes.Excellence.Specs

/-- The principal quotient is regular if the defining element has unit derivative.
Regularity is tested at primes, so this includes the zero quotient. -/
def regularRing_quotient_span_singleton_of_isUnit_derivationType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
    RegularRingValue R → ∀ (D : Derivation ℤ R R) (g : R), IsUnit (D g) →
      RegularRingValue (R ⧸ Ideal.span {g})

/-- Regularity of the quotient by the monic binomial (T^n-f), for (nge 1). -/
def regularRing_quotient_X_pow_sub_C_of_isUnit_derivationType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
    RegularRingValue R → ∀ (D : Derivation ℤ R R) (f : R), IsUnit (D f) →
      ∀ (n : ℕ), 1 ≤ n →
        RegularRingValue (Polynomial R ⧸ Ideal.span {Polynomial.X ^ n - Polynomial.C f})

/-- The extension and regularity assertions of Lemma 5.3. -/
def derivations_and_regular_hypersurfaceType : Prop :=
  _root_.Specs.CommutativeAlgebraNotes.DerivationLocalization.{u, v} ∧
    _root_.Specs.CommutativeAlgebraNotes.DerivationAdicCompletion.{u} ∧
    regularRing_quotient_X_pow_sub_C_of_isUnit_derivationType.{u}

end CommutativeAlgebraNotes.Excellence.Specs
