import MathGenome.Internal.Specs.D05.M11.Hermitian
import Mathlib.Analysis.Complex.Basic

/-!
Independent statements for K05.11.hermitian_diagonal, paper.tex:1755–1765.
The forms are the canonical first-slot-linear sesquilinear forms fixed upstream.
No Hermitian, positivity, or nondegeneracy assumption is made in polarization.
The algebraic statements hold in arbitrary dimension, hence in particular on all
finite-dimensional spaces in the chapter, including the zero space.
-/

namespace Specs.D05.M11.HermitianDiagonal

/-- Recovery from the diagonal, with the paper's first-slot-linear signs. -/
def polarization : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : Hermitian.sesquilinearForm_value ℂ V) (u v : V),
    let q := fun w => B w w
    B u v = (1 / 4 : ℂ) *
      (q (u + v) - q (u - v) +
        Complex.I * q (u + Complex.I • v) - Complex.I * q (u - Complex.I • v))

/-- Two forms having the same diagonal are equal, even without symmetry. -/
def diagonal_ext : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B C : Hermitian.sesquilinearForm_value ℂ V),
    (∀ v, B v v = C v v) → B = C

/-- The zero-diagonal consequence used later for complex operator forms. -/
def eq_zero_iff_diagonal_zero : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : Hermitian.sesquilinearForm_value ℂ V),
    B = 0 ↔ ∀ v, B v v = 0

/-- Real means the existence of an actual real scalar, with no sign restriction. -/
def hermitian_iff_real_diagonal : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : Hermitian.sesquilinearForm_value ℂ V),
    Hermitian.isHermitian_value B ↔ ∀ v, ∃ r : ℝ, B v v = (r : ℂ)

/-- The real block J = [[0,1],[-1,0]] is nonzero and skew-symmetric,
has identically zero diagonal, and is not symmetric. Thus real diagonal values
cannot recover an arbitrary real form or force its symmetry. -/
def real_skew_counterexample : Prop :=
  ∃ B : LinearMap.BilinForm ℝ (Fin 2 → ℝ),
    (∀ x y, B x y = x 0 * y 1 - x 1 * y 0) ∧
    B ≠ 0 ∧
    (∀ x y, B x y = -B y x) ∧
    (∀ x, B x x = 0) ∧
    ¬ (∀ x y, B y x = B x y)

end Specs.D05.M11.HermitianDiagonal
