import MathGenome.Internal.Specs.D05.M11.ComplexClassification
import MathGenome.Internal.D05.M11.DiagonalCongruence
import MathGenome.Internal.D05.M11.Nondegenerate
import MathGenome.Internal.D05.Foundations.ComplexRoots
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Classification of complex symmetric bilinear forms, including degenerate forms. -/
namespace D05.M11.ComplexClassification

open Module Matrix
open Specs.D05.M11.Nondegenerate

/-- The rescaling coefficient is the inverse of a square root, with a unit
coefficient retained on a zero direction. There is no conjugation in this identity. -/
theorem exists_normalizing_unit (d : ℂ) :
    ∃ a : ℂˣ, (a : ℂ) * (a : ℂ) * d = if d = 0 then 0 else 1 := by
  classical
  by_cases hd : d = 0
  · exact ⟨1, by simp [hd]⟩
  obtain ⟨c, hc⟩ := D05.Foundations.ComplexRoots.complexRoot d 2 (by decide)
  have hc0 : c ≠ 0 := by
    intro h
    simp [h] at hc
    exact hd hc.symm
  refine ⟨(Units.mk0 c hc0)⁻¹, ?_⟩
  simp only [Units.val_inv_eq_inv_val, Units.val_mk0, ite_eq_right hd]
  rw [← hc]
  field_simp

/-- Orthogonal basis with every diagonal entry zero or one. -/
theorem exists_normalized_basis {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (B : LinearMap.BilinForm ℂ V) (hB : B.IsSymm) :
    ∃ b : Basis (Fin (finrank ℂ V)) ℂ V,
      (∀ i j, i ≠ j → B (b i) (b j) = 0) ∧
      (∀ i, B (b i) (b i) = 0 ∨ B (b i) (b i) = 1) := by
  classical
  obtain ⟨b, hO, _⟩ := DiagonalCongruence.orthogonal_basis_radical
    (show (2 : ℂ) ≠ 0 by norm_num) B hB
  choose a ha using fun i => exists_normalizing_unit (B (b i) (b i))
  refine ⟨b.unitsSMul a, ?_, ?_⟩
  · intro i j hij
    simp [Basis.unitsSMul_apply, hO i j hij]
  · intro i
    have h := ha i
    have he : B ((b.unitsSMul a) i) ((b.unitsSMul a) i) =
        if B (b i) (b i) = 0 then 0 else 1 := by
      simpa [Basis.unitsSMul_apply, LinearMap.map_smul₂, Units.smul_def, smul_eq_mul, mul_assoc] using h
    rw [he]
    split_ifs <;> simp

/-- Reordering the normalized basis yields the two asserted blocks. -/
theorem normal_form : Specs.D05.M11.ComplexClassification.normal_form := by
  intro V _ _ _ B hB
  classical
  obtain ⟨b, hO, hD⟩ := exists_normalized_basis B hB
  let d := fun i => B (b i) (b i)
  have hM : B.toMatrix b = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [d]
    · simp [hij, hO i j hij]
  have hs : Fintype.card {i // d i ≠ 0} = rank_value B := by
    rw [Nondegenerate.rank_eq_matrix_rank b B]
    rw [FormMatrix.matrix_eq_toMatrix]
    rw [hM, rank_diagonal]
  let ep : {i // d i ≠ 0} ≃ Fin (rank_value B) := Fintype.equivFinOfCardEq hs
  have hz : Fintype.card {i // ¬ d i ≠ 0} = finrank ℂ V - rank_value B := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hs]
  let ez : {i // ¬ d i ≠ 0} ≃ Fin (finrank ℂ V - rank_value B) :=
    Fintype.equivFinOfCardEq hz
  let e : Fin (finrank ℂ V) ≃
      Fin (rank_value B) ⊕ Fin (finrank ℂ V - rank_value B) :=
    (Equiv.sumCompl (fun i => d i ≠ 0)).symm.trans (ep.sumCongr ez)
  refine ⟨b.reindex e, ?_⟩
  have hinl (i : Fin (rank_value B)) :
      d (e.symm (Sum.inl i)) ≠ 0 := by
    change d (ep.symm i).val ≠ 0
    exact (ep.symm i).property
  have hinr (i : Fin (finrank ℂ V - rank_value B)) :
      d (e.symm (Sum.inr i)) = 0 := by
    change d (ez.symm i).val = 0
    exact not_ne_iff.mp (ez.symm i).property
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.reindex_apply]
  by_cases hij : i = j
  · subst j
    cases i with
    | inl i =>
      have hi := (hD (e.symm (.inl i))).resolve_left (hinl i)
      simpa using hi
    | inr i => simpa using hinr i
  · rw [hO _ _ (fun h => hij (e.symm.injective h))]
    cases i <;> cases j <;> simp_all

/-- Invertibility on both sides preserves rank; the left factor is the transpose. -/
theorem rank_congruence : Specs.D05.M11.ComplexClassification.rank_congruence := by
  intro n A P hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  rw [Matrix.rank_mul_eq_left_of_isUnit_det P (Pᵀ * A) hd]
  exact Matrix.rank_mul_eq_right_of_isUnit_det Pᵀ A (by simpa using hd)

/-- Congruence of symmetric complex forms is classified by rank. -/
theorem congruent_iff_rank : Specs.D05.M11.ComplexClassification.congruent_iff_rank := by
  intro V _ _ _ B C hB hC
  classical
  constructor
  · rintro ⟨e, he⟩
    let b := Module.finBasis ℂ V
    rw [Nondegenerate.rank_eq_matrix_rank b B,
      Nondegenerate.rank_eq_matrix_rank (b.map e) C]
    congr 1
    ext i j
    exact (he (b i) (b j)).symm
  · intro hr
    obtain ⟨b, hb⟩ := normal_form B hB
    have hC' : ∃ c : Basis (Fin (rank_value B) ⊕
        Fin (finrank ℂ V - rank_value B)) ℂ V,
        C.toMatrix c = Matrix.fromBlocks 1 0 0 0 := by
      rw [hr]
      exact normal_form C hC
    obtain ⟨c, hc⟩ := hC'
    let e := b.equiv c (Equiv.refl _)
    refine ⟨e, ?_⟩
    have hf : C.comp e.toLinearMap e.toLinearMap = B := by
      apply LinearMap.BilinForm.ext_basis b
      intro i j
      change C (e (b i)) (e (b j)) = B (b i) (b j)
      simp only [e, Basis.equiv_apply, Equiv.refl_apply]
      have hm := congrArg (fun M => M i j) (hc.trans hb.symm)
      simpa only [LinearMap.BilinForm.toMatrix_apply] using hm
    intro x y
    exact congrArg (fun F : LinearMap.BilinForm ℂ V => F x y) hf

/-- Rank of the bilinear form associated to a coordinate matrix. -/
theorem rank_toBilin' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    rank_value A.toBilin' = A.rank := by
  rw [Nondegenerate.rank_eq_matrix_rank (Pi.basisFun ℂ (Fin n)) A.toBilin']
  congr 1
  ext i j
  simp [Specs.D05.M11.FormMatrix.formMatrix_value, Pi.basisFun_apply]

/-- Matrix version of the classification, with an invertible congruence witness. -/
theorem matrix_congruent_iff_rank :
    Specs.D05.M11.ComplexClassification.matrix_congruent_iff_rank := by
  intro n A C hA hC
  classical
  constructor
  · rintro ⟨P, hP, he⟩
    rw [← he, rank_congruence A P hP]
  · intro hr
    have hAb : A.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
    have hCb : C.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hC
    have hrb : rank_value C.toBilin' = rank_value A.toBilin' := by
      simpa only [rank_toBilin'] using hr.symm
    obtain ⟨e, he⟩ := (congruent_iff_rank C.toBilin' A.toBilin' hCb hAb).mpr hrb
    refine ⟨e.toLinearMap.toMatrix', ?_, ?_⟩
    · apply LinearMap.isUnit_toMatrix'_iff.mpr
      exact (Module.End.isUnit_iff _).mpr e.bijective
    · have hf : A.toBilin'.comp e.toLinearMap e.toLinearMap = C.toBilin' := by
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        exact he x y
      have hm := congrArg LinearMap.BilinForm.toMatrix' hf
      simpa only [LinearMap.BilinForm.toMatrix'_comp,
        LinearMap.BilinForm.toMatrix'_toBilin'] using hm

end D05.M11.ComplexClassification
