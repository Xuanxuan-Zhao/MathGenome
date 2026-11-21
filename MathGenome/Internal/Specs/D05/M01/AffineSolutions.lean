import MathGenome.Internal.Specs.D05.M01.System
import MathGenome.Internal.Specs.D05.M03.Kernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Independent statements for paper.tex:767–768, K05.01.affine_solutions.
The solution predicate is the upstream column-matrix equation. The kernel is
the canonical submodule of `Matrix.mulVecLin A`. A translate is its image under
`z ↦ x₀ + z`; no choice of a solution or decomposition is assumed implicitly.
All sizes are natural numbers, including zero. Subspace assertions mean equality
with the carrier of a `Submodule` with the inherited operations.
-/
namespace D05.M01.AffineSolutionsSpec

open scoped Matrix
open D05.M01.SystemSpec

universe u

/-- Subtracting a particular solution gives the homogeneous equation. -/
def solution_iff_sub_zero : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x₀ x : Fin n → K),
    IsSolutionValue A b x₀ →
      (IsSolutionValue A b x ↔ A *ᵥ (x - x₀) = 0)

/-- The same equivalence using the canonical kernel subspace. -/
def solution_iff_sub_mem_kernel : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x₀ x : Fin n → K),
    IsSolutionValue A b x₀ →
      (IsSolutionValue A b x ↔ x - x₀ ∈ LinearMap.ker A.mulVecLin)

/-- Equality of the entire solution set with the translate of the kernel. -/
def solutions_eq_translate_kernel : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K) (x₀ : Fin n → K),
    IsSolutionValue A b x₀ →
      {x | IsSolutionValue A b x} =
        (fun z => x₀ + z) '' (LinearMap.ker A.mulVecLin : Set (Fin n → K))

/-- The alternative to having a particular solution is the empty set. -/
def solutions_eq_empty_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    {x | IsSolutionValue A b x} = ∅ ↔ ¬ ∃ x, IsSolutionValue A b x

/-- In the homogeneous case the solution set is exactly the kernel carrier. -/
def homogeneous_solutions_eq_kernel : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K),
    {x | IsSolutionValue A 0 x} = (LinearMap.ker A.mulVecLin : Set (Fin n → K))

/-- A solution set contains zero exactly when its right-hand side is zero. -/
def zero_mem_solutions_iff : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    (0 : Fin n → K) ∈ {x | IsSolutionValue A b x} ↔ b = 0

/-- A nonempty solution set is a subspace precisely when it contains zero. -/
def solutions_subspace_iff_contains_zero : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    (∃ x, IsSolutionValue A b x) →
      ((∃ S : Submodule K (Fin n → K), (S : Set (Fin n → K)) =
          {x | IsSolutionValue A b x}) ↔
        (0 : Fin n → K) ∈ {x | IsSolutionValue A b x})

/-- Equivalently, exactly the homogeneous systems have a subspace as solution set.
This also excludes the empty solution set, since a subspace contains zero. -/
def solutions_subspace_iff_rhs_zero : Prop :=
  ∀ {K : Type u} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (b : Fin m → K),
    (∃ S : Submodule K (Fin n → K), (S : Set (Fin n → K)) =
      {x | IsSolutionValue A b x}) ↔ b = 0

end D05.M01.AffineSolutionsSpec
