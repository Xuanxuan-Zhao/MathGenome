import MathGenome.Internal.Specs.D07.Ch08.FieldIdealsMatrixRingSimplicity
import MathGenome.Internal.D07.Ch08.MatrixRing
import MathGenome.Internal.D07.Ch08.UnitInIdeal

/-! Matrix-unit extraction and simplicity of the matrix ring over a field. -/

universe u

namespace D07.Ch08.FieldIdealsMatrixRingSimplicity

open Specs.D07.Ch08.FieldIdealsMatrixRingSimplicity
open scoped BigOperators

theorem matrixUnitExtraction : MatrixUnitExtraction.{u} := by
  intro F _ n A i j k l
  simp [Matrix.smul_single]

theorem matrixUnitsInNonzeroIdeal : MatrixUnitsInNonzeroIdeal.{u} := by
  intro F _ n I A i j hA hij k l
  have hentry : Matrix.single k l (A i j) ∈ I := by
    simpa using I.mul_mem_right _ (Matrix.single j l 1)
      (I.mul_mem_left (Matrix.single k i 1) A hA)
  have hscaled := I.mul_mem_left (Matrix.single k k (A i j)⁻¹) _ hentry
  simpa [hij] using hscaled

theorem simplicity : Simplicity.{u} := by
  intro F _ n _ I
  classical
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hnonzero : ∃ A : Matrix (Fin n) (Fin n) F, A ∈ I ∧ A ≠ 0 := by
    by_contra h
    apply hI
    apply TwoSidedIdeal.ext
    intro A
    simp only [TwoSidedIdeal.mem_bot]
    constructor
    · intro hA
      by_contra hne
      exact h ⟨A, hA, hne⟩
    · rintro rfl
      exact I.zero_mem
  obtain ⟨A, hA, hne⟩ := hnonzero
  have hentry : ∃ i j, A i j ≠ 0 := by
    by_contra h
    apply hne
    ext i j
    by_contra hij
    exact h ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hentry
  have hunit : ∀ k l : Fin n, Matrix.single k l (1 : F) ∈ I :=
    matrixUnitsInNonzeroIdeal F n I A i j hA hij
  have hone : (1 : Matrix (Fin n) (Fin n) F) ∈ I := by
    rw [← Matrix.sum_single_one]
    exact sum_mem fun k _ => hunit k k
  have htop : I.asIdeal = ⊤ :=
    (D07.Ch08.UnitInIdeal.leftIdealTopIffOne _ I.asIdeal).mpr hone
  apply TwoSidedIdeal.ext
  intro B
  change B ∈ I.asIdeal ↔ B ∈ (⊤ : TwoSidedIdeal _)
  rw [htop]
  simp

theorem hasZeroDivisors : HasZeroDivisors.{u} := by
  intro F _ n hn
  exact D07.Ch08.MatrixRing.hasZeroDivisors F n hn

theorem notDivisionRing : NotDivisionRing.{u} := by
  intro F _ n hn hall
  obtain ⟨A, B, hA, hB, hAB⟩ := hasZeroDivisors F n hn
  obtain ⟨a, rfl⟩ := hall A hA
  apply hB
  calc
    B = (↑(a⁻¹) : Matrix (Fin n) (Fin n) F) * (↑a * B) := by simp
    _ = 0 := by rw [hAB, mul_zero]

end D07.Ch08.FieldIdealsMatrixRingSimplicity
