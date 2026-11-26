import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Defs

namespace Specs.CommutativeAlgebraNotes

/-- The quotient-rule extension along any localization map. -/
def DerivationLocalization : Prop :=
  ∀ {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] (D : Derivation ℤ R R),
    ∃ E : Derivation ℤ L L,
      (∀ a : R, E (algebraMap R L a) = algebraMap R L (D a)) ∧
      (∀ (a : R) (s : S),
        E (IsLocalization.mk' L a s) =
          IsLocalization.mk' L (D a) s - IsLocalization.mk' L (a * D (s : R)) (s ^ 2))

/-- Differentiation lowers the ideal-power filtration by at most one. -/
def DerivationIdealPower : Prop :=
  ∀ {R : Type*} [CommRing R] (D : Derivation ℤ R R) (I : Ideal R)
    (n : ℕ) {a : R}, a ∈ I ^ (n + 1) → D a ∈ I ^ n

/-- The extension to the adic completion is computed on residues one level down. -/
def DerivationAdicCompletion : Prop :=
  ∀ {R : Type*} [CommRing R] (D : Derivation ℤ R R) (I : Ideal R),
    ∃ E : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      (∀ a : R, E (algebraMap R (AdicCompletion I R) a) =
        algebraMap R (AdicCompletion I R) (D a)) ∧
      (∀ (x : AdicCompletion I R) (n : ℕ) (a : R),
        AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk (I ^ (n + 1)) a →
        AdicCompletion.evalₐ I n (E x) = Ideal.Quotient.mk (I ^ n) (D a))

end Specs.CommutativeAlgebraNotes
