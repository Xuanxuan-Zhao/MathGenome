import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Basic.Real.Basic

noncomputable section

namespace VariationalNotes.Ch05

open Matrix

/-- The objective in the equality-constrained quadratic program. -/
def quadraticObjective {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (c x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ (Q *ᵥ x)) / 2 + c ⬝ᵥ x

/-- The two rows of the displayed block system, with the sign convention
`Qx + Aᵀν = -c`, `Ax = b`. -/
def IsKKTSolution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (z : (Fin n → ℝ) × (Fin m → ℝ)) : Prop :=
  Q *ᵥ z.1 + Aᵀ *ᵥ z.2 = -c ∧ A *ᵥ z.1 = b

/-- Feasibility, global minimality, and uniqueness among global minimizers. -/
def IsUniqueGlobalMinimizer {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (c x : Fin n → ℝ) : Prop :=
  A *ᵥ x = b ∧
  (∀ y, A *ᵥ y = b → quadraticObjective Q c x ≤ quadraticObjective Q c y) ∧
  (∀ y, A *ᵥ y = b → quadraticObjective Q c y ≤ quadraticObjective Q c x → y = x)

end VariationalNotes.Ch05

namespace Specs.VariationalNotes.Ch05

open Matrix
open _root_.VariationalNotes.Ch05

/-- Proposition `prop:reduced-hessian`. Row independence is the full row rank
condition. No nonemptiness of either coordinate index type is assumed. -/
def ReducedHessianStatement : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ),
    LinearIndependent ℝ (fun i => fun j => A i j) → Q.IsSymm →
    (∀ u : Fin n → ℝ, A *ᵥ u = 0 → u ≠ 0 → 0 < u ⬝ᵥ (Q *ᵥ u)) →
    ∀ (b : Fin m → ℝ) (c : Fin n → ℝ),
      (∃! z, IsKKTSolution A Q b c z) ∧
      ∀ z, IsKKTSolution A Q b c z → IsUniqueGlobalMinimizer A Q b c z.1

end Specs.VariationalNotes.Ch05
