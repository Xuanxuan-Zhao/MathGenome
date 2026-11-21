import MathGenome.Internal.Specs.D05.M11.Hermitian.TriangularGram.FlagProjection

/-! K05.11.hermitian, paper.tex:1739–1753. Indices start at zero.
All finite bases, including the empty basis, are quantified. `RCLike` covers
both real and complex scalars; no symmetry or positivity is imposed.
The real bilinear statement below also uses the ordinary canonical BilinForm.
-/
noncomputable section
namespace Specs.D05.M11.Hermitian.TriangularGram
open Module Matrix
open scoped BigOperators
open Specs.D05.M11.Hermitian
open Specs.D05.M11.Hermitian.TriangularGram.FlagProjection

/-- Unit upper triangular means exactly zeros below and ones on the diagonal. -/
def UnitUpper {K : Type*} [Zero K] [One K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ i j, j < i → P i j = 0) ∧ ∀ i, P i i = 1

def Lower {K : Type*} [Zero K] {n : ℕ} (L : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, i < j → L i j = 0

def Upper {K : Type*} [Zero K] {n : ℕ} (L : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, j < i → L i j = 0

/-- Actual first-slot-linear congruence, with algebraic transpose. -/
def gramTransform {K : Type*} [RCLike K] {n : ℕ}
    (H P : Matrix (Fin n) (Fin n) K) := Pᵀ * H * P.map star

/-- The columns interpreted as vectors in the original ordered basis. -/
def columns {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (P : Matrix (Fin n) (Fin n) K) (j : Fin n) : V :=
  ∑ i, P i j • e i

/-- Existence and uniqueness against ALL competing unit upper triangular matrices. -/
def exists_unique : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V),
    LeadingNonzero e B →
    ∃! P : Matrix (Fin n) (Fin n) K,
      UnitUpper P ∧ Lower (gramTransform (formMatrix_value e B) P)

/-- Coordinate bridge valid even for singular P and arbitrary forms. -/
def gram_of_columns : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V)
    (P : Matrix (Fin n) (Fin n) K) (i j : Fin n),
    B (columns e P i) (columns e P j) = gramTransform (formMatrix_value e B) P i j

/-- Every solution has determinant one and its columns are the promised basis.
The hypothesis on original leading minors is unnecessary for these consequences. -/
def solution_basis : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V)
    (P : Matrix (Fin n) (Fin n) K),
    UnitUpper P → Lower (gramTransform (formMatrix_value e B) P) →
    P.det = 1 ∧ IsUnit P ∧ ∃ v : Basis (Fin n) K V,
      (∀ j, v j = columns e P j) ∧
      (∀ j, v j - e j ∈ flag e j.castSucc) ∧
      ∀ i j, i < j → B (v i) (v j) = 0

/-- The same P in the Hoffman–Kunze convention, without symmetry assumptions.
The third conjunct is equivalence of the full unique-existence propositions. -/
def convention_bridge : Prop :=
  ∀ {K : Type*} [RCLike K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K),
    (∀ P, (gramTransform H P)ᵀ = P.conjTranspose * Hᵀ * P) ∧
    (∀ k : Fin (n + 1),
      ((Hᵀ).submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det =
      (H.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det) ∧
    ((∃! P, UnitUpper P ∧ Lower (gramTransform H P)) ↔
      ∃! P, UnitUpper P ∧ Upper (P.conjTranspose * Hᵀ * P))

/-- Conjugate transpose is ordinary transpose in the full real convention bridge. -/
def real_convention_bridge : Prop :=
  ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ),
    (∀ P : Matrix (Fin n) (Fin n) ℝ, P.conjTranspose = Pᵀ) ∧
    (∀ P : Matrix (Fin n) (Fin n) ℝ, (Pᵀ * H * P)ᵀ = Pᵀ * Hᵀ * P) ∧
    ((∃! P, UnitUpper P ∧ Lower (Pᵀ * H * P)) ↔
      ∃! P, UnitUpper P ∧ Upper (Pᵀ * Hᵀ * P))

def hoffman_kunze : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V),
    LeadingNonzero e B → ∃! P : Matrix (Fin n) (Fin n) K,
      UnitUpper P ∧ Upper (P.conjTranspose * (formMatrix_value e B)ᵀ * P)

/-- Full ordinary real bilinear specialization, with no star in its conclusion. -/
def real_bilinear : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : Basis (Fin n) ℝ V) (B : LinearMap.BilinForm ℝ V),
    (∀ k : Fin (n + 1), 0 < k.val →
      ((Matrix.of (fun i j => B (e i) (e j))).submatrix
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det ≠ 0) →
    ∃! P : Matrix (Fin n) (Fin n) ℝ,
      UnitUpper P ∧ Lower (Pᵀ * (Matrix.of (fun i j => B (e i) (e j))) * P)

/-- The columns in the ordinary real bilinear formulation are the same basis. -/
def real_solution_basis : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : Basis (Fin n) ℝ V) (B : LinearMap.BilinForm ℝ V)
    (P : Matrix (Fin n) (Fin n) ℝ),
    UnitUpper P → Lower (Pᵀ * Matrix.of (fun i j => B (e i) (e j)) * P) →
    P.det = 1 ∧ IsUnit P ∧ ∃ v : Basis (Fin n) ℝ V,
      (∀ j, v j = columns e P j) ∧
      (∀ j, v j - e j ∈ flag e j.castSucc) ∧
      ∀ i j, i < j → B (v i) (v j) = 0

/-- Empty identity, uniqueness, determinant, and vacuity are explicit. -/
def empty_case : Prop :=
  ∀ {K : Type*} [RCLike K] (H : Matrix (Fin 0) (Fin 0) K),
    (∃! P, UnitUpper P ∧ Lower (gramTransform H P)) ∧
    (∀ P : Matrix (Fin 0) (Fin 0) K, P = 1 ∧ P.det = 1) ∧
    (∀ k : Fin 1, ¬ 0 < k.val)

/-- Hermitian specialization of the SAME transformed matrix; no new rescaling. -/
def hermitian_specialization : Prop :=
  ∀ {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm_value K V)
    (P : Matrix (Fin n) (Fin n) K),
    isHermitian_value B → Lower (gramTransform (formMatrix_value e B) P) →
    (∀ i j, i ≠ j → gramTransform (formMatrix_value e B) P i j = 0) ∧
    ∀ i, ∃ r : ℝ, gramTransform (formMatrix_value e B) P i i = (r : K)

/-- Symmetric real specialization also retains the same P. -/
def real_symmetric_specialization : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : Basis (Fin n) ℝ V) (B : LinearMap.BilinForm ℝ V)
    (P : Matrix (Fin n) (Fin n) ℝ),
    (∀ x y, B y x = B x y) →
    Lower (Pᵀ * (Matrix.of (fun i j => B (e i) (e j))) * P) →
    ∀ i j, i ≠ j → (Pᵀ * (Matrix.of (fun i j => B (e i) (e j))) * P) i j = 0
end Specs.D05.M11.Hermitian.TriangularGram
