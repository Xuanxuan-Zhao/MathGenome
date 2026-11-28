import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedLie
import Mathlib.RingTheory.Derivation.Lie

/-! The derivation part of Proposition SR07. -/

namespace Specs.LieNotes.SuperRestricted.RestrictedDerivations

universe u v

/-- On the commutator Lie algebra of derivations, endomorphism composition
gives a restricted power in positive characteristic. -/
def derivations_admit_restrictedPowerType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {A : Type v} [CommRing A] [Algebra k A],
    ∃ power : RestrictedLie.restrictedPowerValue k p (Derivation k A A),
      ∀ D : Derivation k A A,
        (power.val D : Module.End k A) = (D : Module.End k A) ^ p

end Specs.LieNotes.SuperRestricted.RestrictedDerivations
