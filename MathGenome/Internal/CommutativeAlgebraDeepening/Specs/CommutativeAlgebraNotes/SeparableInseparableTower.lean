import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.Logic.Relation

namespace CommutativeAlgebraNotes

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A strict simple adjunction inside `F`. The generator is separable over the
preceding intermediate field or has its `p`th power there. -/
def IsSimpleFieldStep (p : ℕ) (M N : IntermediateField K F) : Prop :=
  ∃ b : F, N = (adjoin M ({b} : Set F)).restrictScalars K ∧
    b ∉ M ∧ (IsSeparable M b ∨ b ^ p ∈ M)

namespace Specs

/-- Reflexive transitive closure gives a finite tower and allows length zero. -/
def finiteExtension_has_simpleTower : Prop :=
  ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] [Module.Finite K F]
    (p : ℕ) [CharP K p], p.Prime →
    Relation.ReflTransGen
      (IsSimpleFieldStep (K := K) (F := F) p) ⊥ ⊤

/-- The binomial defining a degree-`p` step, with its coefficient in the preceding field. -/
def minpoly_eq_X_pow_sub_C_of_pow_mem : Prop :=
  ∀ (K F : Type*) [Field K] [Field F] [Algebra K F]
    (p : ℕ) [CharP K p], p.Prime →
    ∀ (M : IntermediateField K F) (b : F) (a : M), b ∉ M → b ^ p = (a : F) →
      minpoly M b = Polynomial.X ^ p - Polynomial.C a

def finiteExtension_isSeparable_of_charZero : Prop :=
  ∀ (K F : Type*) [Field K] [Field F] [Algebra K F] [Module.Finite K F]
    [CharZero K], Algebra.IsSeparable K F

end Specs
end CommutativeAlgebraNotes
