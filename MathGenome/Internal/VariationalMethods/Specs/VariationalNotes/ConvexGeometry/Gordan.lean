import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Basic.Real.Basic

/-! Independent specifications of `paper.tex`, Theorem `thm:gordan` and the
subspace-of-directions applicability statement immediately following it.
Strict inequalities are coordinatewise; empty row and column types are allowed.
-/
namespace VariationalNotes.ConvexGeometry.Specs

open Matrix

universe w u v

/-- Exactly one of the strict matrix system and its nonnegative transpose-kernel
certificate holds. No nonemptiness assumption is imposed on the index types. -/
def gordan_alternative : Prop :=
  ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n] (B : Matrix m n ℝ),
    ((∃ d : n → ℝ, ∀ i, (B *ᵥ d) i < 0) ∨
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧ Bᵀ *ᵥ μ = 0)) ∧
    ¬ ((∃ d : n → ℝ, ∀ i, (B *ᵥ d) i < 0) ∧
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧ Bᵀ *ᵥ μ = 0))

/-- The same alternative for a linear map into a finite coordinate space. -/
def gordan_linearMap : Prop :=
  ∀ {E : Type w} [AddCommGroup E] [Module ℝ E]
    {m : Type u} [Fintype m] (T : E →ₗ[ℝ] (m → ℝ)),
    ((∃ d : E, ∀ i, T d i < 0) ∨
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧
        ∀ d : E, ∑ i, μ i * T d i = 0)) ∧
    ¬ ((∃ d : E, ∀ i, T d i < 0) ∧
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧
        ∀ d : E, ∑ i, μ i * T d i = 0))

/-- Coordinates on any finite-dimensional subspace, with no dimension hypothesis
on the ambient space. The displayed matrix represents the restriction of T,
and the alternative quantifies over directions in S. -/
def gordan_subspace : Prop :=
  ∀ {E : Type w} [AddCommGroup E] [Module ℝ E]
    (S : Submodule ℝ E) [FiniteDimensional ℝ S]
    {m : Type u} [Fintype m] (T : E →ₗ[ℝ] (m → ℝ)),
    let b := Module.finBasis ℝ S
    let B : Matrix m (Fin (Module.finrank ℝ S)) ℝ := fun i j => T (b j) i
    (∀ d : S, B *ᵥ (fun j => b.repr d j) = T d) ∧
    (((∃ d : S, ∀ i, T d i < 0) ∨
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧
        ∀ d : S, ∑ i, μ i * T d i = 0)) ∧
    ¬ ((∃ d : S, ∀ i, T d i < 0) ∧
      (∃ μ : m → ℝ, (∀ i, 0 ≤ μ i) ∧ μ ≠ 0 ∧
        ∀ d : S, ∑ i, μ i * T d i = 0)))

end VariationalNotes.ConvexGeometry.Specs
