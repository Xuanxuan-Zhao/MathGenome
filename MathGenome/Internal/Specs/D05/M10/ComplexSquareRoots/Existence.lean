import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Independent propositions for paper.tex:1614–1620. Invertibility is
invertibility in the endomorphism algebra. There is no positive-dimension,
inner-product, diagonalizability, or additional spectral hypothesis. -/

namespace Specs.D05.M10.ComplexSquareRoots.Existence

/-- Every invertible complex endomorphism in finite dimension has a square root. -/
def exists_square_root : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V), IsUnit T → ∃ R : Module.End ℂ V, R ^ 2 = T

/-- The two specified roots of the identity are distinct on a nonzero space. -/
def identity_roots : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [Nontrivial V],
    (1 : Module.End ℂ V) ^ 2 = 1 ∧ (-1 : Module.End ℂ V) ^ 2 = 1 ∧
      (1 : Module.End ℂ V) ≠ -1

/-- The zero space is included, and its unique endomorphism is its own root. -/
def zero_space : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (T : Module.End ℂ V), T ^ 2 = T

/-- The displayed singular Jordan matrix has no complex matrix square root. -/
def jordan_no_root : Prop :=
  ¬ ∃ R : Matrix (Fin 2) (Fin 2) ℂ, R ^ 2 = !![0, 1; 0, 0]

/-- The same displayed example as an actual operator on the coordinate space. -/
def singular_operator_no_root : Prop :=
  let J : Module.End ℂ (Fin 2 → ℂ) := Matrix.toLin' !![0, 1; 0, 0]
  ¬ IsUnit J ∧ ¬ ∃ R : Module.End ℂ (Fin 2 → ℂ), R ^ 2 = J

end Specs.D05.M10.ComplexSquareRoots.Existence
