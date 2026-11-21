import MathGenome.Internal.Specs.D05.M03.Kernel
import MathGenome.Internal.Specs.D05.M07.Dual
import MathGenome.Internal.Specs.D05.M11.FormMatrix

/-!
K05.11.radicals, paper.tex:1646–1650. Both radicals are subspaces of the
original space, with the paper's order of slots. Coordinates are transported
by the accepted coordinate equivalence; the matrix kernel is a subspace of
coordinate columns, not literally a subspace of the original vector type.
The elementary claims are proved for arbitrary spaces (hence include the
paper's finite-dimensional scope); coordinates use a finite ordered basis.
Alternating means vanishing on the diagonal, in every characteristic.
-/
namespace Specs.D05.M11.Radicals

open Module Matrix

universe u v

def radical_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    LinearMap.BilinForm K V → Submodule K V

/-- The map into the algebraic dual has argument `x` in the first slot. -/
def leftRadical_value : radical_type.{u, v} := fun B => LinearMap.ker B

/-- Interchanging the slots gives the map defining the right radical. -/
def rightRadical_value : radical_type.{u, v} := fun B => LinearMap.ker B.flip

def mem_leftRadical : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (x : V),
    x ∈ leftRadical_value B ↔ ∀ y : V, B x y = 0

def mem_rightRadical : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (y : V),
    y ∈ rightRadical_value B ↔ ∀ x : V, B x y = 0

/-- These equalities also specify the actual algebraic-dual maps. -/
def leftRadical_eq_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V),
    leftRadical_value B = LinearMap.ker (B : V →ₗ[K] Module.Dual K V)

def rightRadical_eq_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V),
    rightRadical_value B = LinearMap.ker (B.flip : V →ₗ[K] Module.Dual K V)

/-- Left-radical coordinates lie in the kernel of the transpose matrix. -/
def left_coordinate_membership : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (x : V),
    x ∈ leftRadical_value B ↔
      M04.Coordinates.coordinates_value b x ∈
        LinearMap.ker (M11.FormMatrix.formMatrix_value b B)ᵀ.mulVecLin

/-- Right-radical coordinates lie in the kernel of the original matrix. -/
def right_coordinate_membership : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (x : V),
    x ∈ rightRadical_value B ↔
      M04.Coordinates.coordinates_value b x ∈
        LinearMap.ker (M11.FormMatrix.formMatrix_value b B).mulVecLin

/-- Equality of subspaces after the explicitly stated coordinate transport. -/
def left_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    (leftRadical_value B).map (M04.Coordinates.coordinates_value b).toLinearMap =
      LinearMap.ker (M11.FormMatrix.formMatrix_value b B)ᵀ.mulVecLin

def right_coordinates : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    (rightRadical_value B).map (M04.Coordinates.coordinates_value b).toLinearMap =
      LinearMap.ker (M11.FormMatrix.formMatrix_value b B).mulVecLin

/-- Fixed matrix and its canonical form for the source's counterexample. -/
def exampleMatrix (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 0, 0]

noncomputable def exampleForm (K : Type*) [Field K] : LinearMap.BilinForm K (Fin 2 → K) :=
  (exampleMatrix K).toBilin'

/-- Its value is the first coordinate of the first vector times the second
coordinate of the second vector, verifying the matrix convention directly. -/
def example_evaluation : Prop :=
  ∀ (K : Type*) [Field K] (x y : Fin 2 → K), exampleForm K x y = x 0 * y 1

def example_left_radical : Prop :=
  ∀ (K : Type*) [Field K],
    (leftRadical_value (exampleForm K) : Set (Fin 2 → K)) = {x | x 0 = 0} ∧
    leftRadical_value (exampleForm K) =
      Submodule.span K {Pi.single (1 : Fin 2) (1 : K)}

def example_right_radical : Prop :=
  ∀ (K : Type*) [Field K],
    (rightRadical_value (exampleForm K) : Set (Fin 2 → K)) = {x | x 1 = 0} ∧
    rightRadical_value (exampleForm K) =
      Submodule.span K {Pi.single (0 : Fin 2) (1 : K)}

def example_radicals_ne : Prop :=
  ∀ (K : Type*) [Field K],
    leftRadical_value (exampleForm K) ≠ rightRadical_value (exampleForm K)

def radicals_eq_of_symmetric : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), B.IsSymm → leftRadical_value B = rightRadical_value B

def radicals_eq_of_alternating : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), B.IsAlt → leftRadical_value B = rightRadical_value B

end Specs.D05.M11.Radicals
