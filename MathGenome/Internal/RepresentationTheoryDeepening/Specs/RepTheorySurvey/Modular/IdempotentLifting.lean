import Mathlib.Algebra.Group.Idempotent
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

namespace RepTheorySurvey.Modular

open Ideal.Quotient

/-- The inverse limit of the quotients by the positive powers of a two-sided ideal.
The index `n` denotes the power `n + 1`. -/
def AdicLimit {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] :=
  { a : (n : ℕ) → R ⧸ (I ^ (n + 1)) //
    ∀ ⦃n m : ℕ⦄ (h : n ≤ m), factorPow I (Nat.succ_le_succ h) (a m) = a n }

/-- The comparison sends an element to its residues in all positive powers. -/
def adicComparison {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] :
    R → AdicLimit I :=
  fun x => ⟨fun n => mk (I ^ (n + 1)) x, fun _ _ _ => rfl⟩

/-- Every compatible family of residues has a unique common lift. -/
def IsAdicCompleteSeparated {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided] : Prop :=
  Function.Bijective (adicComparison I)

end RepTheorySurvey.Modular

namespace Specs.RepTheorySurvey.Modular

open _root_.RepTheorySurvey.Modular

def exists_idempotent_lift_type : Prop :=
  ∀ {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided],
    (∃ n : ℕ, I ^ n = ⊥) ∨ IsAdicCompleteSeparated I →
    ∀ e : R ⧸ I, IsIdempotentElem e →
      ∃ a : R, IsIdempotentElem a ∧ Ideal.Quotient.mk I a = e

def existsUnique_idempotent_lift_type : Prop :=
  ∀ {R : Type*} [CommRing R] (I : Ideal R),
    (∃ n : ℕ, I ^ n = ⊥) ∨ IsAdicCompleteSeparated I →
    ∀ e : R ⧸ I, IsIdempotentElem e →
      ∃! a : R, IsIdempotentElem a ∧ Ideal.Quotient.mk I a = e

end Specs.RepTheorySurvey.Modular
