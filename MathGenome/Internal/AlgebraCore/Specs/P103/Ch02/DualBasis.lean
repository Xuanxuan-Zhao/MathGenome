import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs

/-! Dual-basis assertions of paper.tex, Theorem 2.3, lines 337–343.
All rings are unital, possibly noncommutative or zero. A sum over an arbitrary
index type is expressed as a sum over any finite set containing the nonzero
coefficients. Pointwise finite support is a separate, explicit condition.
Right modules follow the source convention of left modules over the opposite.
-/

universe u v w

namespace P103.Specs.Ch02.DualBasis

variable {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]

/-- A pointwise finite dual family, with its full reconstruction formula. -/
def IsDualBasis {J : Type w} (p : J → P) (φ : J → P →ₗ[R] R) : Prop :=
  (∀ x, (Function.support (fun j => φ j x)).Finite) ∧
  ∀ x (s : Finset J), (∀ j, φ j x ≠ 0 → j ∈ s) →
    x = ∑ j ∈ s, φ j x • p j

/-- Right multiplication by a scalar, in the opposite-ring representation. -/
def rightMul {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
    [Module Rᵐᵒᵖ P] (x : P) (r : R) : P := MulOpposite.op r • x

/-- The right formula is `x = ∑ p_j φ_j(x)`. A right-linear functional is
represented as a left-linear map into the opposite regular module; its scalar
value in R is obtained by `unop`. This retains the multiplication order. -/
def IsRightDualBasis {R : Type u} [Ring R] {P : Type v} [AddCommGroup P]
    [Module Rᵐᵒᵖ P] {J : Type w} (p : J → P) (φ : J → P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ) : Prop :=
  (∀ x, (Function.support (fun j => MulOpposite.unop (φ j x))).Finite) ∧
  ∀ x (s : Finset J), (∀ j, MulOpposite.unop (φ j x) ≠ 0 → j ∈ s) →
    x = ∑ j ∈ s, rightMul (p j) (MulOpposite.unop (φ j x))

def projective_iff_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P],
    Module.Projective R P ↔
      ∃ (J : Type (max u v w)) (p : J → P) (φ : J → P →ₗ[R] R), IsDualBasis p φ

/-- The converse applies to a family of any cardinality, independently of R and P. -/
def projective_of_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]
    (J : Type w) (p : J → P) (φ : J → P →ₗ[R] R),
    IsDualBasis p φ → Module.Projective R P

def finite_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P],
    ∃ (n : ℕ) (p : Fin n → P) (φ : Fin n → P →ₗ[R] R),
      IsDualBasis p φ ∧ ∀ x, x = ∑ j, φ j x • p j

def right_projective_iff_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P],
    Module.Projective Rᵐᵒᵖ P ↔
      ∃ (J : Type (max u v w)) (p : J → P)
        (φ : J → P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ), IsRightDualBasis p φ

def right_projective_of_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    (J : Type w) (p : J → P) (φ : J → P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ),
    IsRightDualBasis p φ → Module.Projective Rᵐᵒᵖ P

def right_finite_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module Rᵐᵒᵖ P]
    [Module.Finite Rᵐᵒᵖ P] [Module.Projective Rᵐᵒᵖ P],
    ∃ (n : ℕ) (p : Fin n → P) (φ : Fin n → P →ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ),
      IsRightDualBasis p φ ∧
        ∀ x, x = ∑ j, rightMul (p j) (MulOpposite.unop (φ j x))

/-- Every zero module has the empty dual basis, even over the zero ring. -/
def empty_dualBasisType : Prop :=
  ∀ (R : Type u) [Ring R] (P : Type v) [AddCommGroup P] [Module R P]
    [Subsingleton P],
    IsDualBasis (fun j : Empty => j.elim : Empty → P)
      (fun j : Empty => j.elim : Empty → P →ₗ[R] R)

end P103.Specs.Ch02.DualBasis
