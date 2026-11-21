import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M08.Charpoly
import MathGenome.Internal.Specs.D05.M09.Eigenspace
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Ring.Parity

/-!
Independent specifications for K05.09.existence, paper.tex:1317–1326.
Eigenvalues and characteristic polynomials are the canonical objects over the
stated scalar field. The real counterexamples are actual direct sums of the
displayed rotation matrix, with no splitting or eigenvalue certificate assumed.
-/

noncomputable section

namespace Specs.D05.M09.Existence

open Polynomial

def complex_exists : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [Nontrivial V] (T : Module.End ℂ V), ∃ μ : ℂ, T.HasEigenvalue μ

def real_odd_exists : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : Module.End ℝ V), Odd (Module.finrank ℝ V) →
      ∃ μ : ℝ, T.HasEigenvalue μ

/-- The same rotation convention as the preceding entry. -/
def rotation : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- A finite external direct sum, indexed by position within a block and then
by block number, as in Mathlib's `Matrix.blockDiagonal`. -/
def rotationBlocks (m : ℕ) : Matrix (Fin 2 × Fin m) (Fin 2 × Fin m) ℝ :=
  Matrix.blockDiagonal fun _ : Fin m => rotation

def rotation_charpoly : Prop := rotation.charpoly = (X : Polynomial ℝ) ^ 2 + 1

def rotation_blocks_charpoly : Prop :=
  ∀ m : ℕ, (rotationBlocks m).charpoly = ((X : Polynomial ℝ) ^ 2 + 1) ^ m

/-- The polynomial has no real root, also when the family of blocks is empty. -/
def rotation_blocks_no_roots : Prop :=
  ∀ (m : ℕ) (x : ℝ), ((rotationBlocks m).charpoly).eval x ≠ 0

/-- In every even-dimensional real space there is an operator with the exact
source characteristic polynomial and no real eigenvalue. This stronger version
also includes the zero space, whose characteristic polynomial is one. -/
def real_even_counterexample : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
    Even (Module.finrank ℝ V) →
      ∃ T : Module.End ℝ V,
        Specs.D05.M08.Charpoly.charpoly_value T =
          ((X : Polynomial ℝ) ^ 2 + 1) ^ (Module.finrank ℝ V / 2) ∧
        ∀ μ : ℝ, ¬ T.HasEigenvalue μ

/-- The exact boundary for a universal real eigenvalue-existence assertion. -/
def real_universal_iff_odd : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
    (∀ T : Module.End ℝ V, ∃ μ : ℝ, T.HasEigenvalue μ) ↔
      Odd (Module.finrank ℝ V)

/-- The complex assertion requires a nonzero space. -/
def complex_exists_iff_nonzero : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V),
    (∃ μ : ℂ, T.HasEigenvalue μ) ↔ 0 < Module.finrank ℂ V

/-- Degree divisibility for the original polynomial evaluation and its inherited
kernel subspace. Irreducibility already implies positive degree over a field;
no monicity or nonzero-kernel hypothesis is imposed. -/
def degree_dvd_kernel : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) (p : Polynomial K),
    Irreducible p →
      p.natDegree ∣ Module.finrank K
        (LinearMap.ker (Specs.D05.M08.Evaluation.evaluation_value K V T p))

/-- Negative discriminant forces this particular real kernel to have even
dimension, including when the ambient space or the kernel is zero. -/
def quadratic_kernel_even : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : Module.End ℝ V) (b c : ℝ), b ^ 2 < 4 * c →
      Even (Module.finrank ℝ (LinearMap.ker (T ^ 2 + b • T + c • 1)))

end Specs.D05.M09.Existence
