import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.SolvableRadical
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Basis.Fin

/-! LA-D01, notes/005/lie-algebras-and-representations.tex, lines 1557–1617.
The chapter assumes a finite-dimensional complex semisimple Lie algebra.
Semisimplicity of the algebra means that its solvable radical is zero.
Over ℂ a semisimple endomorphism is diagonalizable. No nonzero assumption
is imposed on the algebra or its toral subalgebras. -/

universe u
namespace Specs.LieAlgebrasAndRepresentations.MaximalTori

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]

/-- Commuting elements whose adjoint endomorphisms are semisimple. -/
def IsToral_value (H : LieSubalgebra ℂ L) : Prop :=
  IsLieAbelian H ∧ ∀ x : H, (LieAlgebra.ad ℂ L (x : L)).IsSemisimple

def IsToral_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], LieSubalgebra ℂ L → Prop

/-- Maximality is with respect to inclusion among all toral subalgebras. -/
def IsMaximalToral_value (H : LieSubalgebra ℂ L) : Prop :=
  Maximal IsToral_value H

def IsMaximalToral_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L], LieSubalgebra ℂ L → Prop

/-- The centralizer in the original algebra, with its inherited Lie structure. -/
def toralCentralizer_value (H : LieSubalgebra ℂ L) : LieSubalgebra ℂ L where
  carrier := {x | ∀ h : H, ⁅(h : L), x⁆ = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy h; simp [lie_add, hx h, hy h]
  smul_mem' := by intro c x hx h; simp [lie_smul, hx h]
  lie_mem' := by intro x y hx hy h; simp [leibniz_lie, hx h, hy h]

def toralCentralizer_type :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L],
    LieSubalgebra ℂ L → LieSubalgebra ℂ L

def toral_bot_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L], IsToral_value (⊥ : LieSubalgebra ℂ L)

/-- A single finite basis diagonalizes every adjoint operator from H. -/
def toral_simultaneously_diagonalizable_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (H : LieSubalgebra ℂ L), IsToral_value H →
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ L),
      ∀ (h : H) (i : Fin n), ∃ a : ℂ, ⁅(h : L), b i⁆ = a • b i

def exists_maximal_toral_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
      ∃ H : LieSubalgebra ℂ L, IsMaximalToral_value H

def maximal_toral_centralizer_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
      ∀ H : LieSubalgebra ℂ L, IsMaximalToral_value H → toralCentralizer_value H = H

def maximal_toral_ne_bot_type : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    [Nontrivial L], SolvableRadical.IsSemisimple_value ℂ L →
      ∀ H : LieSubalgebra ℂ L, IsMaximalToral_value H → H ≠ ⊥

/-- In the zero algebra the zero subalgebra is maximal and self-centralizing. -/
def zero_algebra_toral_type : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [Subsingleton L],
    IsMaximalToral_value (⊥ : LieSubalgebra ℂ L) ∧
      toralCentralizer_value (⊥ : LieSubalgebra ℂ L) = ⊥

end Specs.LieAlgebrasAndRepresentations.MaximalTori
