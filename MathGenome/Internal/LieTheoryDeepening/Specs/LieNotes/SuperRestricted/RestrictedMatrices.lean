import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedLie
import Mathlib.Algebra.Lie.Classical

/-! Specifications for the matrix part of SR07. -/

namespace Specs.LieNotes.SuperRestricted.RestrictedMatrices

open LieAlgebra.SpecialLinear (sl)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)

universe u

/-- The associative power of a traceless matrix is traceless. -/
def pow_mem_slType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p] {n : ℕ}
    (A : sl (Fin n) k), (A.val ^ p) ∈ sl (Fin n) k

/-- The special linear Lie algebra carries the restricted operation
induced by the ordinary power in the full matrix algebra. -/
def sl_admits_restrictedPowerType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p] (n : ℕ),
    ∃ power : restrictedPowerValue k p (sl (Fin n) k),
      ∀ A : sl (Fin n) k, (power.val A).val = A.val ^ p

end Specs.LieNotes.SuperRestricted.RestrictedMatrices
