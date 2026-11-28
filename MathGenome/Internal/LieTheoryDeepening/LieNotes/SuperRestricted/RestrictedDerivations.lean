import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedDerivations
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedLie
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RestrictedOperationBoundary

namespace LieNotes.SuperRestricted.RestrictedDerivations

universe u v

/-- The `p`-fold composition of a derivation is again a derivation, and
these powers make the commutator Lie algebra of derivations restricted. -/
theorem derivations_admit_restrictedPower
    {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {A : Type v} [CommRing A] [Algebra k A] :
    ∃ power : RestrictedLie.RestrictedPower k p (Derivation k A A),
      ∀ D : Derivation k A A,
        (power.val D : Module.End k A) = (D : Module.End k A) ^ p :=
  LieAlgebrasAndRepresentations.RestrictedOperationBoundary.associativeDerivations_admit_restrictedPower

end LieNotes.SuperRestricted.RestrictedDerivations
