import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification of FT-E04A: the global assertions of Theorem E04,
notes/003/advanced-field-theory.tex:1131–1147, 1153–1155.
The algebra structure specifies the inclusion into the fixed algebraic closure.
The distinguished automorphism is arithmetic Frobenius, with q-power action.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

set_option linter.checkUnivs false in
def globalFrobenius_type :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω], Ω ≃ₐ[k] Ω

def globalFrobenius_value : globalFrobenius_type :=
  fun k Ω _ _ _ _ _ => FiniteField.frobeniusAlgEquivOfAlgebraic k Ω

def globalFrobenius_apply_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (x : Ω), globalFrobenius_value k Ω x = x ^ Fintype.card k

def globalFrobenius_fixes_base_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (a : k),
    globalFrobenius_value k Ω (algebraMap k Ω a) = algebraMap k Ω a

def globalFrobenius_bijective_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω], Function.Bijective (globalFrobenius_value k Ω)

def globalFrobenius_pow_apply_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (d : ℕ) (x : Ω),
    (globalFrobenius_value k Ω ^ d) x = x ^ (Fintype.card k ^ d)

def globalFrobenius_pow_ne_one_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (d : ℕ), 0 < d → globalFrobenius_value k Ω ^ d ≠ 1

def globalFrobenius_exists_moved_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (d : ℕ), 0 < d →
    ∃ x : Ω, (globalFrobenius_value k Ω ^ d) x ≠ x

/-- Mathlib denotes infinite order by `orderOf = 0`. -/
def globalFrobenius_orderOf_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω], orderOf (globalFrobenius_value k Ω) = 0

end Specs.AdvancedFieldTheory
