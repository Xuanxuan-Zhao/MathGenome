import MathGenome.Internal.Specs.D05.M11.Bilinear
import MathGenome.Internal.Specs.D05.M04.ChangeBasis
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
Independent statements for K05.11.hermitian, paper.tex:1733–1739.
The triangular Gram reduction supplement at lines 1739–1753 is allocated to
11.hermitian.triangular_gram.flag_projection and 11.hermitian.triangular_gram
by the current goal contract; it is not an assumption of any statement here.
Scalars may be complex or real (`RCLike`); the algebraic identities below
actually hold without a finite-dimensional ambient space. Coordinate statements
use finite bases and include the empty basis. No positivity is assumed.
`x ⬝ᵥ H *ᵥ star y` denotes the scalar `xᵗ H conjugate(y)` with column coordinates.
-/
noncomputable section

namespace Specs.D05.M11.Hermitian

open Module Matrix
open scoped BigOperators

universe u v

/-- Canonical linear maps in the first slot, conjugate-linear maps in the second. -/
def sesquilinearForm_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [RCLike K] → [AddCommGroup V] →
    [Module K V] → Type (max u v)

abbrev sesquilinearForm_value (K : Type u) (V : Type v) [RCLike K]
    [AddCommGroup V] [Module K V] := V →ₗ[K] V →ₗ⋆[K] K

/-- Hermitian symmetry, with the paper's order of arguments. -/
def isHermitian_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [RCLike K] → [AddCommGroup V] →
    [Module K V] → sesquilinearForm_value K V → Prop

def isHermitian_value {K : Type u} {V : Type v} [RCLike K]
    [AddCommGroup V] [Module K V] (B : sesquilinearForm_value K V) : Prop :=
  ∀ x y, B y x = star (B x y)

/-- The four slotwise axioms characterize exactly the same underlying function. -/
def sesquilinear_iff_axioms : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] (b : V → V → K),
    (∃ B : sesquilinearForm_value K V, ∀ x y, B x y = b x y) ↔
      (∀ x x' y, b (x + x') y = b x y + b x' y) ∧
      (∀ (a : K) x y, b (a • x) y = a * b x y) ∧
      (∀ x y y', b x (y + y') = b x y + b x y') ∧
      (∀ (a : K) x y, b x (a • y) = star a * b x y)

/-- The actual array of values, with no transpose or conjugation inserted. -/
def formMatrix_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [RCLike K] → [AddCommGroup V] →
    [Module K V] → {n : ℕ} → Basis (Fin n) K V →
      sesquilinearForm_value K V → Matrix (Fin n) (Fin n) K

def formMatrix_value {K : Type u} {V : Type v} [RCLike K]
    [AddCommGroup V] [Module K V] {n : ℕ} (e : Basis (Fin n) K V)
    (B : sesquilinearForm_value K V) : Matrix (Fin n) (Fin n) K :=
  fun i j => B (e i) (e j)

/-- Full finite expansion, including conjugation of the second coefficients. -/
def finite_expansion : Prop :=
  ∀ {K V I J : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : sesquilinearForm_value K V) (s : Finset I) (t : Finset J)
    (a : I → K) (b : J → K) (x : I → V) (y : J → V),
    B (∑ i ∈ s, a i • x i) (∑ j ∈ t, b j • y j) =
      ∑ i ∈ s, ∑ j ∈ t, a i * star (b j) * B (x i) (y j)

/-- The displayed coordinate formula for all vectors, not just basis vectors. -/
def matrix_formula : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V) (x y : V),
    B x y = (fun i => e.repr x i) ⬝ᵥ
      formMatrix_value e B *ᵥ (fun j => star (e.repr y j))

/-- Equivalence with the matrix equation, in both directions. -/
def hermitian_iff_matrix : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V),
    isHermitian_value B ↔ (formMatrix_value e B).IsHermitian

/-- Hermitian matrices use exactly H = (conjugate H)ᵗ. -/
def hermitian_matrix_equation : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K),
    H.IsHermitian ↔ H = (H.map star)ᵀ

/-- A real diagonal value is represented by an actual real scalar. -/
def diagonal_real : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : sesquilinearForm_value K V), isHermitian_value B →
      ∀ v, ∃ r : ℝ, B v v = (r : K)

/-- Congruence uses the previously fixed NEW-to-OLD coordinate conversion. -/
def change_basis : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e f : Basis (Fin n) K V) (B : sesquilinearForm_value K V),
    formMatrix_value f B =
      (Specs.D05.M04.ChangeBasis.changeMatrix_value e f)ᵀ * formMatrix_value e B *
        (Specs.D05.M04.ChangeBasis.changeMatrix_value e f).map star

/-- The scalar transpose identity uses A = Hᵗ, even for a non-Hermitian H. -/
def quadratic_transpose_bridge : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (x : Fin n → K),
    x ⬝ᵥ H *ᵥ (star x) = (star x) ⬝ᵥ Hᵀ *ᵥ x

/-- In particular B(v,v) = x* A x for A = Hᵗ and x the coordinates of v. -/
def quadratic_matrix_expression : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V) (v : V),
    B v v = (fun i => star (e.repr v i)) ⬝ᵥ
      (formMatrix_value e B)ᵀ *ᵥ (fun i => e.repr v i)

/-- The transpose bridge preserves the Hermitian matrix condition. -/
def transpose_hermitian : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K),
    Hᵀ.IsHermitian ↔ H.IsHermitian

end Specs.D05.M11.Hermitian
