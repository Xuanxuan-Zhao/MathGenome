import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.MatrixCorner
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Morita.FullEquivalence

/-! The explicit full-corner equivalence for square matrices over a unital ring. -/

universe u v

namespace RM03.Morita

open CategoryTheory

variable (R : Type u) [Ring R] {n : ℕ} (hn : 0 < n)

theorem matrix_unit_sum :
    let j : Fin n := ⟨0, hn⟩
    (∑ i, Matrix.single i j (1 : R) * (matrixIdempotent R hn).val * Matrix.single j i 1) = 1 := by
  let j : Fin n := ⟨0, hn⟩
  change (∑ i, Matrix.single i j (1 : R) * Matrix.single j j 1 * Matrix.single j i 1) = 1
  simp only [Matrix.single_mul_single_same, one_mul, Matrix.sum_single_one]

theorem matrixIdempotent_isFull : IsFull (matrixIdempotent R hn) :=
  (full_iff_sum (matrixIdempotent R hn)).2
    ⟨n, fun i => Matrix.single i ⟨0, hn⟩ 1, fun i => Matrix.single ⟨0, hn⟩ i 1,
      matrix_unit_sum R hn⟩

theorem matrix_corner_full : MatrixCornerSpec.fullType.{u} :=
  fun R _ _ hn => ⟨matrixIdempotent_isFull R hn, matrix_unit_sum R hn⟩

private theorem corner_eq_single (a : Corner (matrixIdempotent R hn)) :
    let j : Fin n := ⟨0, hn⟩
    Matrix.single j j (a.val j j) = a.val := by
  let j : Fin n := ⟨0, hn⟩
  change Matrix.single j j (a.val j j) = a.val
  calc
    _ = Matrix.single j j (1 : R) * a.val * Matrix.single j j 1 := by
      rw [Matrix.single_mul_mul_single, one_mul, mul_one]
    _ = a.val := by
      change (matrixIdempotent R hn).val * a.val * (matrixIdempotent R hn).val = a.val
      rw [a.property.1, a.property.2]

/-- Evaluation at the first diagonal entry, with inverse supported at that entry. -/
def matrixCornerRingEquiv : Corner (matrixIdempotent R hn) ≃+* R :=
  let j : Fin n := ⟨0, hn⟩
  { toFun := fun a => a.val j j
    invFun := fun r => ⟨Matrix.single j j r, by
      constructor
      · change Matrix.single j j (1 : R) * Matrix.single j j r = Matrix.single j j r
        rw [Matrix.single_mul_single_same, one_mul]
      · change Matrix.single j j r * Matrix.single j j (1 : R) = Matrix.single j j r
        rw [Matrix.single_mul_single_same, mul_one]⟩
    left_inv := fun a => Subtype.ext (corner_eq_single R hn a)
    right_inv := Matrix.single_apply_same j j
    map_add' := fun _ _ => rfl
    map_mul' := by
      intro a b
      change (a.val * b.val) j j = a.val j j * b.val j j
      conv_lhs => rw [← corner_eq_single R hn a]
      exact Matrix.single_mul_apply_same (a.val j j) j j j b.val }

/-- The full matrix corner followed by transport to right modules over the coefficient ring. -/
noncomputable def matrixCornerEquivalence :
    ModuleCat.{max u v} (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ ≌ ModuleCat.{max u v} Rᵐᵒᵖ :=
  (fullCornerEquivalence (matrixIdempotent R hn) (matrixIdempotent_isFull R hn)).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (matrixCornerRingEquiv R hn).symm.op)

theorem matrix_corner_equivalence : MatrixCornerSpec.equivalenceType.{u,v} := by
  intro R _ n hn
  exact ⟨matrixCornerRingEquiv R hn, fun _ => rfl, fun _ => rfl,
    matrixCornerEquivalence R hn, rfl, rfl⟩

end RM03.Morita
