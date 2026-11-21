import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Algebraic.Basic

/-! Independent statements of K07.23.frobenius, paper.tex:7476–7538.
`Algebra ℝ D` specifies the central real scalar embedding. A division ring
is associative and nonzero; commutativity and finite dimension are not
hypotheses of the algebraic classification. -/

universe u
namespace Specs.D07.Ch23.Frobenius

/-- The three actual real algebras, indexed by their distinct real dimensions.
Each alternative contains an algebra equivalence, not just a vector-space
equivalence or a multiplication table. -/
def ModelEquivalence (D : Type u) [DivisionRing D] [Algebra ℝ D] (n : ℕ) : Prop :=
  (n = 1 ∧ Nonempty (ℝ ≃ₐ[ℝ] D)) ∨
  (n = 2 ∧ Nonempty (ℂ ≃ₐ[ℝ] D)) ∨
  (n = 4 ∧ Nonempty (Quaternion ℝ ≃ₐ[ℝ] D))

def Existence : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) →
    Nonempty (ℝ ≃ₐ[ℝ] D) ∨ Nonempty (ℂ ≃ₐ[ℝ] D) ∨
      Nonempty (Quaternion ℝ ≃ₐ[ℝ] D)

/-- Exactly one of the three models occurs. Uniqueness is of the model,
not of the choice of an algebra equivalence. -/
def Classification : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) → ∃! n : ℕ, ModelEquivalence D n

def PairwiseNonisomorphic : Prop :=
  ¬ Nonempty (ℝ ≃ₐ[ℝ] ℂ) ∧
  ¬ Nonempty (ℝ ≃ₐ[ℝ] Quaternion ℝ) ∧
  ¬ Nonempty (ℂ ≃ₐ[ℝ] Quaternion ℝ)

/-- Algebraicity alone implies finite dimension in this setting. -/
def AlgebraicFiniteDimensional : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) →
    FiniteDimensional ℝ D ∧
      (Module.finrank ℝ D = 1 ∨ Module.finrank ℝ D = 2 ∨ Module.finrank ℝ D = 4)

def FiniteDimensionalClassification : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D],
    ∃! n : ℕ, ModelEquivalence D n

end Specs.D07.Ch23.Frobenius
