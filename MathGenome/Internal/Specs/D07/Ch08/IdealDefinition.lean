import MathGenome.Internal.Specs.D07.Ch08.MatrixRing
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Algebra.Ring.Subring.Defs

/-!
Independent specifications for K07.08.ideal_definition, paper.tex:1296–1309.
An additive subgroup records exactly the additive condition. The unbundled
predicates below quantify over the entire ambient ring. A right ideal is
represented canonically by a left ideal of the multiplicative opposite;
two-sidedness of a Mathlib `Ideal` is the additional `Ideal.IsTwoSided` property.
No nontriviality or commutativity is imposed except where explicitly stated.
-/

universe u v

namespace Specs.D07.Ch08.IdealDefinition

def IsLeftIdeal {R : Type u} [Ring R] (H : AddSubgroup R) : Prop :=
  ∀ (r a : R), a ∈ H → r * a ∈ H

def IsRightIdeal {R : Type u} [Ring R] (H : AddSubgroup R) : Prop :=
  ∀ (a r : R), a ∈ H → a * r ∈ H

/-- An unqualified ideal in the source has both absorption properties. -/
def IsTwoSidedIdeal {R : Type u} [Ring R] (H : AddSubgroup R) : Prop :=
  IsLeftIdeal H ∧ IsRightIdeal H

/-- The source definition agrees with Mathlib's bundled left ideals. -/
def LeftIdealCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (H : AddSubgroup R),
    IsLeftIdeal H ↔ ∃ I : Ideal R, I.toAddSubgroup = H

/-- Reversing multiplication identifies right ideals with left ideals,
with membership transported by `MulOpposite.op`. -/
def RightIdealCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (H : AddSubgroup R),
    IsRightIdeal H ↔
      ∃ I : Ideal Rᵐᵒᵖ, ∀ a : R, MulOpposite.op a ∈ I ↔ a ∈ H

/-- A Mathlib left ideal needs precisely right absorption to be two-sided. -/
def TwoSidedIdealCharacterization : Prop :=
  ∀ (R : Type u) [Ring R] (I : Ideal R),
    I.IsTwoSided ↔ IsTwoSidedIdeal I.toAddSubgroup

def CommutativeCoincidence : Prop :=
  ∀ (R : Type u) [CommRing R] (H : AddSubgroup R),
    (IsLeftIdeal H ↔ IsRightIdeal H) ∧
      (IsLeftIdeal H ↔ IsTwoSidedIdeal H)

/-- Proper left, right, and therefore two-sided ideals cannot be unital
subrings with the same underlying additive subgroup. -/
def ProperIdealNotSubring : Prop :=
  ∀ (R : Type u) [Ring R] (H : AddSubgroup R),
    (IsLeftIdeal H ∨ IsRightIdeal H) → H ≠ ⊤ →
      ¬ ∃ S : Subring R, S.toAddSubgroup = H

/-- Exactly the matrices whose columns other than `j` vanish. -/
def columnSubgroup {R : Type u} [Ring R] {n : ℕ} (j : Fin n) :
    AddSubgroup (Matrix (Fin n) (Fin n) R) where
  carrier := {A | ∀ i k, k ≠ j → A i k = 0}
  zero_mem' := by intro i k _; rfl
  add_mem' := by
    intro A B hA hB i k hk
    change A i k + B i k = 0
    rw [hA i k hk, hB i k hk, add_zero]
  neg_mem' := by
    intro A hA i k hk
    change -(A i k) = 0
    rw [hA i k hk, neg_zero]

/-- This is a left ideal over every base ring, including the zero ring. -/
def ColumnLeftIdeal : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ) (j : Fin n),
    IsLeftIdeal (columnSubgroup (R := R) j) ∧
      ∃ I : Ideal (Matrix (Fin n) (Fin n) R),
        I.toAddSubgroup = columnSubgroup j

/-- The actual matrix-unit computation witnessing failure of right absorption.
Distinct indices and a nontrivial base are necessary for nonmembership. -/
def ColumnMatrixUnitWitnesses : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (n : ℕ) (i j : Fin n), i ≠ j →
    Matrix.single i j (1 : R) ∈ columnSubgroup j ∧
    Matrix.single i j (1 : R) * Matrix.single j i (1 : R) =
      Matrix.single i i (1 : R) ∧
    Matrix.single i i (1 : R) ∉ columnSubgroup j

def ColumnNotRight : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (n : ℕ) (i j : Fin n), i ≠ j →
    ¬ IsRightIdeal (columnSubgroup (R := R) j) ∧
    ¬ IsTwoSidedIdeal (columnSubgroup (R := R) j)

/-- This one-sided ideal cannot even be the kernel of a ring map into
an arbitrary ring. Thus it cannot serve as a ring-quotient kernel. -/
def ColumnNotKernel : Prop :=
  ∀ (R : Type u) [Ring R] [Nontrivial R] (n : ℕ) (i j : Fin n), i ≠ j →
    ∀ (S : Type v) [Ring S],
      ¬ ∃ f : Matrix (Fin n) (Fin n) R →+* S,
        ∀ A, A ∈ columnSubgroup j ↔ f A = 0

end Specs.D07.Ch08.IdealDefinition
