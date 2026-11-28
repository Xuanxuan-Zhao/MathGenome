import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedMatrices
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedDerivations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WittKillingBoundary

namespace Specs.LieNotes.SuperRestricted.RestrictedWitt

open _root_.LieAlgebrasAndRepresentations

universe u v

/-- On the derivations of the actual quotient, the basis index `j` represents
the source's `D_{j-1}`. Index `1` is fixed by the restricted power. -/
def witt_admits_restrictedPowerType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p],
    ∃ b : Module.Basis (Fin p) k (Witt.Algebra k p),
      (∀ j, b j = Witt.t k p ^ (j : ℕ) • Witt.derivative k p) ∧
      ∃ power : RestrictedLie.restrictedPowerValue k p (Witt.Algebra k p),
        (∀ D : Witt.Algebra k p,
          (power.val D : Module.End k (Witt.Truncated k p)) =
            (D : Module.End k (Witt.Truncated k p)) ^ p) ∧
        ∀ j, power.val (b j) = if (j : ℕ) = 1 then b j else 0

/-- The matrix and derivation conclusions of SR07 and its truncated Witt example. -/
def proposition_SR07Type : Prop :=
  RestrictedMatrices.pow_mem_slType.{u} ∧
  RestrictedMatrices.sl_admits_restrictedPowerType.{u} ∧
  RestrictedDerivations.derivations_admit_restrictedPowerType.{u, v} ∧
  witt_admits_restrictedPowerType.{u}

end Specs.LieNotes.SuperRestricted.RestrictedWitt
