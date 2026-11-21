import MathGenome.Internal.Specs.D05.M09.Diagonalizable
import MathGenome.Internal.Specs.D05.M08.Charpoly
import Mathlib.Basic.Complex.Basic

/-!
Independent specifications for K05.09.field_dependence, paper.tex:1314–1315.
The matrices act on coordinate columns by `mulVecLin`. The same matrix formula
is used over each named field; no realification of a complex operator is meant.
The characteristic polynomial and eigenbasis predicates are the canonical
objects used in the upstream specifications. The elementary Jordan and identity
calculations are valid over every field, hence in particular over ℝ and ℂ.
-/

noncomputable section
namespace Specs.D05.M09.FieldDependence

/-- The rotation matrix, with the paper's column and sign conventions. -/
def rotationMatrix (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![0, -1; 1, 0]

def rotation (K : Type*) [Field K] : Module.End K (Fin 2 → K) :=
  (rotationMatrix K).mulVecLin

/-- The unipotent Jordan block, with its one above the diagonal. -/
def jordanMatrix (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K :=
  !![1, 1; 0, 1]

def jordan (K : Type*) [Field K] : Module.End K (Fin 2 → K) :=
  (jordanMatrix K).mulVecLin

def firstVector (K : Type*) [Field K] : Fin 2 → K := ![1, 0]

def complexVectors : Fin 2 → (Fin 2 → ℂ) := ![![1, -Complex.I], ![1, Complex.I]]

def complexEigenvalues : Fin 2 → ℂ := ![Complex.I, -Complex.I]

/-- Formal polynomial equality, valid for both named fields. -/
def rotation_charpoly : Prop :=
  ∀ (K : Type*) [Field K], (rotation K).charpoly = Polynomial.X ^ 2 + 1

def rotation_real_no_roots : Prop :=
  ∀ x : ℝ, Polynomial.eval x (rotation ℝ).charpoly ≠ 0

def rotation_real_no_eigenvalues : Prop :=
  ∀ μ : ℝ, ¬ (rotation ℝ).HasEigenvalue μ

def rotation_real_not_diagonalizable : Prop :=
  ¬ Specs.D05.M09.Diagonalizable.diagonalizable_value ℝ (Fin 2 → ℝ) (rotation ℝ)

/-- The exact vectors and eigenvalues printed in the paper, with nonzeroness. -/
def rotation_complex_eigenvectors : Prop :=
  ∀ j : Fin 2, (rotation ℂ).HasEigenvector (complexEigenvalues j) (complexVectors j)

def rotation_complex_independent : Prop := LinearIndependent ℂ complexVectors

/-- These two particular vectors form a basis and give the stated diagonal. -/
def rotation_complex_eigenbasis : Prop :=
  ∃ b : Module.Basis (Fin 2) ℂ (Fin 2 → ℂ),
    (∀ j, b j = complexVectors j) ∧
    LinearMap.toMatrix b b (rotation ℂ) = Matrix.diagonal complexEigenvalues

def rotation_complex_diagonalizable : Prop :=
  Specs.D05.M09.Diagonalizable.diagonalizable_value ℂ (Fin 2 → ℂ) (rotation ℂ)

def jordan_charpoly : Prop :=
  ∀ (K : Type*) [Field K], (jordan K).charpoly = (Polynomial.X - 1) ^ 2

/-- The full kernel and span equality, rather than just one exhibited vector. -/
def jordan_eigenspace_one : Prop :=
  ∀ (K : Type*) [Field K],
    (jordan K).eigenspace 1 =
      LinearMap.ker (jordan K - (LinearMap.id : Module.End K (Fin 2 → K))) ∧
    (jordan K).eigenspace 1 = Submodule.span K {firstVector K}

/-- All other scalars have zero eigenspace. -/
def jordan_other_eigenspaces : Prop :=
  ∀ (K : Type*) [Field K] (μ : K), μ ≠ 1 → (jordan K).eigenspace μ = ⊥

def jordan_eigenvalue_iff : Prop :=
  ∀ (K : Type*) [Field K] (μ : K), (jordan K).HasEigenvalue μ ↔ μ = 1

def jordan_eigenspace_dimension : Prop :=
  ∀ (K : Type*) [Field K], Module.finrank K ((jordan K).eigenspace 1) = 1

/-- Includes non-diagonalizability over ℂ as well as over ℝ. -/
def jordan_not_diagonalizable : Prop :=
  ∀ (K : Type*) [Field K],
    ¬ Specs.D05.M09.Diagonalizable.diagonalizable_value K (Fin 2 → K) (jordan K)

def identity_charpoly : Prop :=
  ∀ (K : Type*) [Field K],
    (LinearMap.id : Module.End K (Fin 2 → K)).charpoly = (Polynomial.X - 1) ^ 2

/-- The original coordinate basis already gives the diagonal matrix I₂. -/
def identity_diagonal_matrix : Prop :=
  ∀ (K : Type*) [Field K],
    LinearMap.toMatrix (Pi.basisFun K (Fin 2)) (Pi.basisFun K (Fin 2))
      (LinearMap.id : Module.End K (Fin 2 → K)) = Matrix.diagonal (fun _ => 1)

def identity_diagonalizable : Prop :=
  ∀ (K : Type*) [Field K],
    Specs.D05.M09.Diagonalizable.diagonalizable_value K (Fin 2 → K) LinearMap.id

/-- The same repeated-root characteristic polynomial has opposite outcomes. -/
def same_charpoly_different_diagonalizability : Prop :=
  (jordan ℂ).charpoly = (LinearMap.id : Module.End ℂ (Fin 2 → ℂ)).charpoly ∧
  ¬ Specs.D05.M09.Diagonalizable.diagonalizable_value ℂ (Fin 2 → ℂ) (jordan ℂ) ∧
  Specs.D05.M09.Diagonalizable.diagonalizable_value ℂ (Fin 2 → ℂ) LinearMap.id

end Specs.D05.M09.FieldDependence
