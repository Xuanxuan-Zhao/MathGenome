import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.RestrictedLie
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Sl2Model
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The matrix basis and restricted powers used in the baby Verma section. -/

namespace Specs.LieNotes.SuperRestricted.RestrictedSlTwo

open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model E F H)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)

universe u

/-- The displayed matrix units and diagonal difference form an ordered basis. -/
def basisType : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ b : Module.Basis (Fin 3) k (Model k),
      b 0 = E k ∧ b 1 = F k ∧ b 2 = H k

/-- The ordinary commutator brackets of the three matrix basis vectors. -/
def bracketsType : Prop :=
  ∀ (k : Type u) [Field k],
    ⁅H k, E k⁆ = (2 : k) • E k ∧
    ⁅H k, F k⁆ = (-2 : k) • F k ∧
    ⁅E k, F k⁆ = H k

/-- The three powers for the restricted operation induced by matrix exponentiation. -/
def matrixRestrictedPowersType : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] {p : ℕ} [CharP k p] (hp : 2 < p),
    letI : NeZero p := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hp)⟩
    ∃ power : restrictedPowerValue k p (Model k),
      (∀ x : Model k, (power.val x).val = x.val ^ p) ∧
        power.val (E k) = 0 ∧ power.val (F k) = 0 ∧ power.val (H k) = H k

end Specs.LieNotes.SuperRestricted.RestrictedSlTwo
