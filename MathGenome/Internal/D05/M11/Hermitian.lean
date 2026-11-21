import MathGenome.Internal.Specs.D05.M11.Hermitian
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.Tactic.Ring

/-! K05.11.hermitian: first-slot-linear forms and their coordinate conventions. -/
noncomputable section

namespace D05.M11.Hermitian

open Module Matrix
open scoped BigOperators

abbrev sesquilinearForm (K V : Type*) [RCLike K] [AddCommGroup V] [Module K V] :=
  V →ₗ[K] V →ₗ⋆[K] K

def isHermitian {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V]
    (B : sesquilinearForm K V) : Prop := ∀ x y, B y x = star (B x y)

def formMatrix {K V : Type*} [RCLike K] [AddCommGroup V] [Module K V] {n : ℕ}
    (e : Basis (Fin n) K V) (B : sesquilinearForm K V) : Matrix (Fin n) (Fin n) K :=
  fun i j => B (e i) (e j)

theorem sesquilinear_iff_axioms : Specs.D05.M11.Hermitian.sesquilinear_iff_axioms := by
  intro K V _ _ _ b
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x x' y
      simpa only [hB] using B.map_add₂ x x' y
    · intro a x y
      simpa only [hB, smul_eq_mul] using B.map_smul₂ a x y
    · intro x y y'
      simpa only [hB] using (B x).map_add y y'
    · intro a x y
      simpa only [hB, smul_eq_mul, starRingEnd_apply] using (B x).map_smulₛₗ a y
  · rintro ⟨ha, hs, hb, ht⟩
    exact ⟨LinearMap.mk₂'ₛₗ (RingHom.id K) (starRingEnd K) b ha hs hb ht, fun _ _ => rfl⟩

theorem finite_expansion : Specs.D05.M11.Hermitian.finite_expansion := by
  intro K V I J _ _ _ B s t a b x y
  rw [B.map_sum₂]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [B.map_smul₂]
  simp only [map_sum, LinearMap.map_smulₛₗ, starRingEnd_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem matrix_formula : Specs.D05.M11.Hermitian.matrix_formula := by
  intro K V _ _ _ n e B x y
  have hm : LinearMap.toMatrix₂ e e B =
      Specs.D05.M11.Hermitian.formMatrix_value e B := by
    ext i j
    simp [Specs.D05.M11.Hermitian.formMatrix_value]
  simpa only [hm, Function.comp_def, RingHom.id_apply, starRingEnd_apply] using
    apply_eq_dotProduct_toMatrix₂_mulVec e e B x y

theorem hermitian_iff_matrix : Specs.D05.M11.Hermitian.hermitian_iff_matrix := by
  intro K V _ _ _ n e B
  have h : Specs.D05.M11.Hermitian.isHermitian_value B ↔ B.flip.IsSymm := by
    constructor
    · intro h
      exact ⟨fun x y => (h y x).symm⟩
    · intro h x y
      exact (h.eq y x).symm
  rw [h, LinearMap.isSymm_iff_isHermitian_toMatrix e]
  have hm : LinearMap.toMatrix₂ e e B.flip =
      (Specs.D05.M11.Hermitian.formMatrix_value e B)ᵀ := by
    ext i j
    simp [Specs.D05.M11.Hermitian.formMatrix_value]
  rw [hm, Matrix.isHermitian_transpose_iff]

theorem hermitian_matrix_equation : Specs.D05.M11.Hermitian.hermitian_matrix_equation := by
  intro K _ n H
  exact eq_comm

theorem diagonal_real : Specs.D05.M11.Hermitian.diagonal_real := by
  intro K V _ _ _ B h v
  exact RCLike.conj_eq_iff_real.mp (h v v).symm

theorem change_basis : Specs.D05.M11.Hermitian.change_basis := by
  intro K V _ _ _ n e f B
  ext i j
  change B (f i) (f j) = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [matrix_formula e B (f i) (f j)]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul,
    Specs.D05.M11.Hermitian.formMatrix_value,
    Specs.D05.M04.ChangeBasis.changeMatrix_value,
    Specs.D05.M04.MatrixOfMap.matrixOfMap_value,
    LinearMap.toMatrix_apply, LinearMap.id_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  ring

theorem quadratic_transpose_bridge : Specs.D05.M11.Hermitian.quadratic_transpose_bridge := by
  intro K _ n H x
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

theorem quadratic_matrix_expression : Specs.D05.M11.Hermitian.quadratic_matrix_expression := by
  intro K V _ _ _ n e B v
  rw [matrix_formula e B v v]
  exact quadratic_transpose_bridge _ _

theorem transpose_hermitian : Specs.D05.M11.Hermitian.transpose_hermitian := by
  intro K _ n H
  exact Matrix.isHermitian_transpose_iff

end D05.M11.Hermitian
