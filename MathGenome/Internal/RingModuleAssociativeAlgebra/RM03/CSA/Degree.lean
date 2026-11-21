import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Tensor
import Mathlib.Data.Nat.Sqrt
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.SimpleModule.IsAlgClosed

/-! Degree and splitting over an algebraic closure for central simple algebras. -/

namespace RM03.CSA

universe u v w

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

/-- The degree of a central simple algebra, given by its dimension's natural square root. -/
noncomputable def degree (k : Type u) [Field k] (A : Type v) [Ring A] [Algebra k A] : ℕ :=
  Nat.sqrt (Module.finrank k A)

private theorem finrank_eq_sq_of_baseChange_matrix
    {L : Type w} [Field L] [Algebra k L] {n : ℕ} (hA : IsCentralSimple k A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Module.finrank k A = n ^ 2 := by
  rw [← finrank_baseChange (L := L) hA, e.toLinearEquiv.finrank_eq, Module.finrank_matrix]
  simp [pow_two]

/-- The size of any matrix presentation over a splitting field is the degree. -/
theorem degree_eq_matrix_size
    {L : Type w} [Field L] [Algebra k L] {n : ℕ} (hA : IsCentralSimple k A)
    (e : BaseChange k L A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    degree k A = n := by
  rw [degree, finrank_eq_sq_of_baseChange_matrix hA e, Nat.sqrt_eq']

private theorem exists_matrix_algebraicClosure (hA : IsCentralSimple k A) :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (BaseChange k (AlgebraicClosure k) A ≃ₐ[AlgebraicClosure k]
        Matrix (Fin n) (Fin n) (AlgebraicClosure k)) := by
  have hC := isCentralSimple_baseChange (L := AlgebraicClosure k) hA
  let : IsSimpleRing (BaseChange k (AlgebraicClosure k) A) := hC.1
  let : FiniteDimensional (AlgebraicClosure k) (BaseChange k (AlgebraicClosure k) A) := hC.2.2
  obtain ⟨n, hn, he⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure k)
      (BaseChange k (AlgebraicClosure k) A)
  exact ⟨n, Nat.pos_of_ne_zero hn.out, he⟩

/-- Scalar extension to the algebraic closure gives a matrix algebra of size `degree k A`. -/
theorem algEquiv_matrix_algebraicClosure (hA : IsCentralSimple k A) :
    Nonempty (BaseChange k (AlgebraicClosure k) A ≃ₐ[AlgebraicClosure k]
      Matrix (Fin (degree k A)) (Fin (degree k A)) (AlgebraicClosure k)) := by
  obtain ⟨n, _, ⟨e⟩⟩ := exists_matrix_algebraicClosure hA
  rw [degree_eq_matrix_size hA e]
  exact ⟨e⟩

theorem degree_pos (hA : IsCentralSimple k A) : 0 < degree k A := by
  obtain ⟨n, hn, ⟨e⟩⟩ := exists_matrix_algebraicClosure hA
  rwa [degree_eq_matrix_size hA e]

theorem finrank_eq_degree_sq (hA : IsCentralSimple k A) :
    Module.finrank k A = (degree k A) ^ 2 := by
  obtain ⟨e⟩ := algEquiv_matrix_algebraicClosure hA
  exact finrank_eq_sq_of_baseChange_matrix hA e

/-- The degree is the unique positive integer whose square equals the dimension. -/
theorem degree_eq_iff (hA : IsCentralSimple k A) {n : ℕ} :
    degree k A = n ↔ 0 < n ∧ Module.finrank k A = n ^ 2 := by
  constructor
  · rintro rfl
    exact ⟨degree_pos hA, finrank_eq_degree_sq hA⟩
  · rintro ⟨_, hn⟩
    rw [degree, hn, Nat.sqrt_eq']

/-- The degree and algebraic-closure assertions applied to a central division algebra. -/
theorem centralDivision_degree {D : Type v} [DivisionRing D] [Algebra k D]
    (hD : IsCentralDivision k D) :
    0 < degree k D ∧ Module.finrank k D = (degree k D) ^ 2 ∧
      Nonempty (BaseChange k (AlgebraicClosure k) D ≃ₐ[AlgebraicClosure k]
        Matrix (Fin (degree k D)) (Fin (degree k D)) (AlgebraicClosure k)) := by
  have h := isCentralSimple_of_isCentralDivision k D hD
  exact ⟨degree_pos h, finrank_eq_degree_sq h, algEquiv_matrix_algebraicClosure h⟩

/-- In a matrix presentation over a central division algebra, the degrees multiply. -/
theorem degree_matrix_division {D : Type w} [DivisionRing D] [Algebra k D] {r : ℕ}
    (hA : IsCentralSimple k A) (hD : IsCentralDivision k D) (hr : 0 < r)
    (e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) :
    degree k A = r * degree k D := by
  have h := isCentralSimple_of_isCentralDivision k D hD
  refine (degree_eq_iff hA).2 ⟨Nat.mul_pos hr (degree_pos h), ?_⟩
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, finrank_eq_degree_sq h, mul_pow]
  simp [pow_two]

end RM03.CSA
