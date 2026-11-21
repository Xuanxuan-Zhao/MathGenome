import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The faithful complex two-dimensional representation of `Q₈`. -/

namespace D07.Ch01.DihedralQuaternionModelsQuaternionMatrices

open Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices

theorem matrix_identities :
    Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.MatrixIdentities := by
  dsimp [Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.MatrixIdentities]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | (ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [I, J, K, E, pow_two, Matrix.mul_apply, Fin.sum_univ_two])
    | (intro h
       have h01 := congrArg (fun A : Mat => A 0 1) h
       norm_num [I, J, Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] at h01)

theorem eight_distinct :
    Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.EightDistinct := by
  intro a b h
  have hentries := congrArg (fun A : Mat => (A 0 0, A 0 1)) h
  fin_cases a <;> fin_cases b <;>
    first | rfl | norm_num [matrixList, E, I, J, K, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff, Prod.mk.injEq] at hentries

theorem modelMatrix_one : modelMatrix 1 = 1 := rfl

set_option maxHeartbeats 2000000 in
theorem modelMatrix_mul (a b : QuaternionGroup 2) :
    modelMatrix (a * b) = modelMatrix a * modelMatrix b := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa_mul_xa] <;>
    simp only [modelMatrix, sub_eq_add_neg, ZMod.val_add, ZMod.neg_val',
      ZMod.val_natCast] <;>
    fin_cases a <;> fin_cases b <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [E, I, J, K, Matrix.mul_apply, Fin.sum_univ_two, ZMod.val]

theorem modelMatrix_injective : Function.Injective modelMatrix := by
  intro a b h
  have hentries := congrArg (fun A : Mat => (A 0 0, A 0 1)) h
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;>
    first | rfl | norm_num [modelMatrix, ZMod.val, E, I, J, K, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff, Prod.mk.injEq] at hentries

theorem modelMatrix_mem_eight (q : QuaternionGroup 2) :
    modelMatrix q ∈ eightMatrices := by
  rcases q with t | t <;> fin_cases t <;>
    simp [modelMatrix, ZMod.val, eightMatrices]

theorem mem_eight_iff (A : Mat) :
    A ∈ eightMatrices ↔ ∃ q : QuaternionGroup 2, modelMatrix q = A := by
  constructor
  · intro h
    simp only [eightMatrices, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.a 0, rfl⟩
    · exact ⟨.a 2, rfl⟩
    · exact ⟨.a 1, rfl⟩
    · exact ⟨.a 3, rfl⟩
    · exact ⟨.xa 0, rfl⟩
    · exact ⟨.xa 2, rfl⟩
    · exact ⟨.xa 3, rfl⟩
    · exact ⟨.xa 1, rfl⟩
  · rintro ⟨q, rfl⟩
    exact modelMatrix_mem_eight q

theorem matrix_closure :
    Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.MatrixClosure := by
  refine ⟨by simp [eightMatrices], ?_, ?_⟩
  · intro A hA B hB
    obtain ⟨a, rfl⟩ := (mem_eight_iff A).1 hA
    obtain ⟨b, rfl⟩ := (mem_eight_iff B).1 hB
    rw [← modelMatrix_mul]
    exact modelMatrix_mem_eight _
  · intro A hA
    obtain ⟨a, rfl⟩ := (mem_eight_iff A).1 hA
    refine ⟨modelMatrix a⁻¹, modelMatrix_mem_eight _, ?_, ?_⟩
    · rw [← modelMatrix_mul, mul_inv_cancel, modelMatrix_one, E]
    · rw [← modelMatrix_mul, inv_mul_cancel, modelMatrix_one, E]

/-- Every displayed matrix is a unit, using the inverse supplied by `Q₈`. -/
def matrixRepresentation : QuaternionGroup 2 →* MatrixGroup where
  toFun q :=
    { val := modelMatrix q
      inv := modelMatrix q⁻¹
      val_inv := by rw [← modelMatrix_mul, mul_inv_cancel, modelMatrix_one]
      inv_val := by rw [← modelMatrix_mul, inv_mul_cancel, modelMatrix_one] }
  map_one' := Units.ext modelMatrix_one
  map_mul' a b := Units.ext (modelMatrix_mul a b)

theorem matrixRepresentation_injective : Function.Injective matrixRepresentation := by
  intro a b h
  exact modelMatrix_injective (congrArg (fun g : MatrixGroup => (g : Mat)) h)

theorem quaternion_matrix_model :
    Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.QuaternionMatrixModel := by
  let H : Subgroup MatrixGroup := matrixRepresentation.range
  let e : QuaternionGroup 2 ≃* H := MonoidHom.ofInjective matrixRepresentation_injective
  have he (q : QuaternionGroup 2) : (((e q : H) : MatrixGroup) : Mat) = modelMatrix q :=
    rfl
  refine ⟨H, ?_, ?_, ?_, e, he⟩
  · intro g
    constructor
    · rintro ⟨q, rfl⟩
      exact modelMatrix_mem_eight q
    · intro hg
      obtain ⟨q, hq⟩ := (mem_eight_iff (g : Mat)).1 hg
      exact ⟨q, Units.ext hq⟩
  · rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  · refine ⟨e (.a 1), e (.xa 0), ?_⟩
    intro h
    have hab : (QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0 ≠ .xa 0 * .a 1 := by
      decide
    apply hab
    apply e.injective
    simpa only [map_mul] using h

end D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
