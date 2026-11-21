import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import MathGenome.Internal.Specs.D05.M11.Bilinear
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Basic.Real.Basic

/-!
Independent statements for K05.11.form_matrix, paper.tex:1641–1644.
Columns use the accepted coordinate map, and the accepted change matrix converts
new coordinates to old coordinates. No symmetry, positivity, characteristic or
nondegeneracy assumption is made. A finite ordered basis supplies the paper's
finite dimension hypothesis, including dimension zero.
`x ⬝ᵥ A *ᵥ y` is the scalar matrix expression `xᵀ A y`.
-/
namespace Specs.D05.M11.FormMatrix

open Matrix Module

universe u v

/-- Matrix of a bilinear form in a finite ordered basis. -/
def formMatrix_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    {n : ℕ} → Basis (Fin n) K V → LinearMap.BilinForm K V → Matrix (Fin n) (Fin n) K

/-- Both matrix indices follow the order of the two slots of the form. -/
noncomputable def formMatrix_value : formMatrix_type.{u, v} :=
  fun b B i j => B (b i) (b j)

def matrix_entry : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (i j : Fin n),
    formMatrix_value b B i j = B (b i) (b j)

/-- Bridge to the canonical Mathlib matrix of a bilinear form. -/
def matrix_eq_toMatrix : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    formMatrix_value b B = B.toMatrix b

/-- The coordinate evaluation uses the original vectors in both slots. -/
def coordinate_evaluation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (x y : V),
    B x y = M04.Coordinates.coordinates_value b x ⬝ᵥ
      formMatrix_value b B *ᵥ M04.Coordinates.coordinates_value b y

/-- Each column of the conversion matrix is the corresponding new basis vector. -/
def change_matrix_entry : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b b' : Basis (Fin n) K V) (i j : Fin n),
    M04.ChangeBasis.changeMatrix_value b b' i j =
      M04.Coordinates.coordinates_value b (b' j) i

/-- Both vector columns obey the same new-to-old coordinate conversion. -/
def coordinate_conversion : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b b' : Basis (Fin n) K V) (x : V),
    M04.Coordinates.coordinates_value b x =
      M04.ChangeBasis.changeMatrix_value b b' *ᵥ M04.Coordinates.coordinates_value b' x

/-- A basis change acts on both form slots, giving congruence. -/
def change_of_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b b' : Basis (Fin n) K V) (B : LinearMap.BilinForm K V),
    formMatrix_value b' B = (M04.ChangeBasis.changeMatrix_value b b')ᵀ *
      formMatrix_value b B * M04.ChangeBasis.changeMatrix_value b b'

/-- The displayed transformed evaluation for arbitrary new coordinate columns. -/
def substituted_evaluation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b b' : Basis (Fin n) K V) (B : LinearMap.BilinForm K V) (x' y' : Fin n → K),
    B ((M04.Coordinates.coordinates_value b').symm x')
      ((M04.Coordinates.coordinates_value b').symm y') =
      x' ⬝ᵥ ((M04.ChangeBasis.changeMatrix_value b b')ᵀ *
        formMatrix_value b B * M04.ChangeBasis.changeMatrix_value b b') *ᵥ y'

/-- `[1]` and `[4]` are congruent over R by the invertible matrix `[2]`. -/
def real_one_dimensional_congruence : Prop :=
  let A : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 1)
  let C : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 4)
  let P : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 2)
  IsUnit P ∧ Pᵀ * A * P = C

/-- The same pair admits no invertible similarity witness. -/
def real_one_dimensional_not_similar : Prop :=
  let A : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 1)
  let C : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ => 4)
  ¬ ∃ Q : Matrix (Fin 1) (Fin 1) ℝ, IsUnit Q ∧ Q⁻¹ * A * Q = C

end Specs.D05.M11.FormMatrix
