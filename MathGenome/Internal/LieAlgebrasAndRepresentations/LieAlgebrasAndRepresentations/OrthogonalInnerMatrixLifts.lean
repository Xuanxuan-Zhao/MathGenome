import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section

namespace LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts

open Matrix LieAlgebra
open Specs.LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
open Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition (Aut inner)

open private inner_module_intertwiner from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.AutomorphismDecomposition

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

private theorem exists_other_index (hcard : 2 < Fintype.card ι) {i j : ι} (hij : i ≠ j) :
    ∃ k, k ≠ i ∧ k ≠ j := by
  by_contra! h
  have hs : (Finset.univ : Finset ι) ⊆ {i, j} := by
    intro k _
    by_cases hk : k = i
    · simp [hk]
    · simp [h k hk]
  have hh := Finset.card_le_card hs
  simp [hij] at hh
  omega

private def elementarySkew (i j : ι) : so ι :=
  ⟨Matrix.single i j 1 - Matrix.single j i 1, by
    rw [Orthogonal.mem_so, Matrix.transpose_sub, Matrix.transpose_single,
      Matrix.transpose_single, neg_sub]⟩

/-- Test the centralizer on the elementary coordinate-plane skew matrices. -/
theorem commuting_with_skew_is_scalar : commuting_with_skew_is_scalar_type.{u} := by
  intro ι _ _ hcard B hcomm
  have hOff (i j : ι) (hij : i ≠ j) : B i j = 0 := by
    obtain ⟨k, hki, hkj⟩ := exists_other_index hcard hij
    have h := congrArg (fun C : Matrix ι ι ℂ => C i k) (hcomm (elementarySkew j k))
    change (B * (Matrix.single j k (1 : ℂ) - Matrix.single k j (1 : ℂ))) i k =
      ((Matrix.single j k (1 : ℂ) - Matrix.single k j (1 : ℂ)) * B) i k at h
    simpa [mul_sub, sub_mul, hkj, hki.symm, hij] using h
  have hDiag (i j : ι) : B i i = B j j := by
    by_cases hij : i = j
    · simp [hij]
    · have h := congrArg (fun C : Matrix ι ι ℂ => C i j) (hcomm (elementarySkew i j))
      change (B * (Matrix.single i j (1 : ℂ) - Matrix.single j i (1 : ℂ))) i j =
        ((Matrix.single i j (1 : ℂ) - Matrix.single j i (1 : ℂ)) * B) i j at h
      simpa [mul_sub, sub_mul, hij, Ne.symm hij] using h
  obtain ⟨i, _, _, _⟩ := Fintype.two_lt_card_iff.mp hcard
  refine ⟨B i i, ?_⟩
  ext a b
  by_cases h : a = b
  · subst b
    simpa using hDiag a i
  · simp [hOff a b h, Matrix.one_apply_ne h]

private theorem orthogonal_transpose {R : Type*} [CommRing R] {A : Matrix ι ι R}
    (hA : IsOrthogonal A) : IsOrthogonal Aᵀ := by
  change Aᵀᵀ * Aᵀ = 1
  rw [transpose_transpose]
  exact mul_eq_one_comm.mp hA

private theorem orthogonal_mul {R : Type*} [CommRing R] {A B : Matrix ι ι R}
    (hA : IsOrthogonal A) (hB : IsOrthogonal B) : IsOrthogonal (A * B) := by
  change (A * B)ᵀ * (A * B) = 1
  rw [transpose_mul]
  calc
    _ = Bᵀ * (Aᵀ * A) * B := by noncomm_ring
    _ = 1 := by rw [show Aᵀ * A = 1 from hA, mul_one]; exact hB

private theorem orthogonalAction_mul {A B : Matrix ι ι ℂ}
    (hA : IsOrthogonal A) (hB : IsOrthogonal B) :
    orthogonalAction A hA * orthogonalAction B hB =
      orthogonalAction (A * B) (orthogonal_mul hA hB) := by
  apply Subtype.ext
  ext X : 1
  apply Subtype.ext
  change A * (B * X.val * Bᵀ) * Aᵀ = (A * B) * X.val * (A * B)ᵀ
  rw [transpose_mul]
  noncomm_ring

theorem complex_representative_mul : complex_representative_mul_type.{u} := by
  rintro ι _ _ _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  exact ⟨A * B, orthogonal_mul hA hB, orthogonalAction_mul hA hB⟩

theorem real_representative_mul : real_representative_mul_type.{u} := by
  rintro ι _ _ _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have h := orthogonalAction_mul (complex_orthogonal hA) (complex_orthogonal hB)
  refine ⟨A * B, orthogonal_mul hA hB, h.trans ?_⟩
  have hAB : complexMatrix A * complexMatrix B = complexMatrix (A * B) :=
    (map_mul Complex.ofRealHom.mapMatrix A B).symm
  apply Subtype.ext
  ext X : 1
  apply Subtype.ext
  simp only [orthogonalAction_apply, hAB]

/-- Apply the inner intertwiner to the standard column-vector module. -/
private theorem inner_matrix_intertwiner (g : Aut (so ι)) (hg : g ∈ inner (so ι)) :
    ∃ U V : Matrix ι ι ℂ, U * V = 1 ∧
      ∀ X : so ι, U * X.val = (g.val X).val * U := by
  let ρ : so ι →ₗ⁅ℂ⁆ Module.End ℂ (ι → ℂ) :=
    Matrix.toLinAlgEquiv'.toAlgHom.toLieHom.comp (Orthogonal.so ι ℂ).incl
  let : LieRingModule (so ι) (ι → ℂ) := LieRingModule.compLieHom _ ρ
  let : LieModule ℂ (so ι) (ι → ℂ) := LieModule.compLieHom _ ρ
  obtain ⟨e, he⟩ := inner_module_intertwiner (V := ι → ℂ) g.val hg
  let U := LinearMap.toMatrixAlgEquiv' e.toLinearMap
  let V := LinearMap.toMatrixAlgEquiv' e.symm.toLinearMap
  refine ⟨U, V, ?_, ?_⟩
  · have hInv : e.toLinearMap * e.symm.toLinearMap = 1 :=
      LinearMap.ext e.apply_symm_apply
    rw [← map_mul, hInv, map_one]
  · intro X
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_mul, map_mul, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
    exact LinearMap.ext (he X)

theorem inner_has_complex_representative : inner_has_complex_representative_type.{u} := by
  intro ι _ _ hcard g hg
  obtain ⟨U, V, hUV, hU⟩ := inner_matrix_intertwiner g hg
  -- Transposing the intertwining equation shows that the Gram matrix centralizes so.
  have hUt (X : so ι) : X.val * Uᵀ = Uᵀ * (g.val X).val := by
    have h := congrArg Matrix.transpose (hU X)
    rw [transpose_mul, transpose_mul, (Orthogonal.mem_so _ _ _).1 X.property,
      (Orthogonal.mem_so _ _ _).1 (g.val X).property, neg_mul, mul_neg] at h
    exact neg_injective h
  have hGram (X : so ι) : (Uᵀ * U) * X.val = X.val * (Uᵀ * U) := by
    rw [mul_assoc, hU, ← mul_assoc, ← hUt, mul_assoc]
  obtain ⟨c, hc⟩ := commuting_with_skew_is_scalar hcard _ hGram
  obtain ⟨i, _, _, _⟩ := Fintype.two_lt_card_iff.mp hcard
  have hc₀ : c ≠ 0 := by
    intro hz
    have hzero : Uᵀ * U = 0 := by simp [hc, hz]
    have hzero' : Uᵀ = 0 := by
      calc
        Uᵀ = Uᵀ * (U * V) := by rw [hUV, mul_one]
        _ = (Uᵀ * U) * V := (mul_assoc ..).symm
        _ = 0 := by rw [hzero, zero_mul]
    have hzeroU : U = 0 := by simpa using congrArg Matrix.transpose hzero'
    have hOne : (1 : ℂ) = 0 := by
      simpa [hzeroU] using congrArg (fun M : Matrix ι ι ℂ => M i i) hUV.symm
    exact one_ne_zero hOne
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by decide)
  have hs₀ : s ≠ 0 := by
    intro hz
    exact hc₀ (by simpa [hz] using hs.symm)
  let A := s⁻¹ • U
  have hA : IsOrthogonal A := by
    change (s⁻¹ • U)ᵀ * (s⁻¹ • U) = 1
    rw [transpose_smul, smul_mul_smul_comm, hc, smul_smul, ← hs]
    have hscale : s⁻¹ * s⁻¹ * s ^ 2 = 1 := by field_simp
    rw [hscale, one_smul]
  refine ⟨A, hA, ?_⟩
  apply Subtype.ext
  ext X : 1
  apply Subtype.ext
  change (g.val X).val = A * X.val * Aᵀ
  have hintertwines : A * X.val = (g.val X).val * A := by
    dsimp [A]
    rw [smul_mul_assoc, mul_smul_comm, hU]
  rw [hintertwines, mul_assoc, mul_eq_one_comm.mp hA, mul_one]

private theorem conjMatrix_mul (A B : Matrix ι ι ℂ) :
    conjMatrix (A * B) = conjMatrix A * conjMatrix B :=
  map_mul Complex.conjAe.toRingEquiv.mapMatrix A B

private theorem conjMatrix_orthogonal {A : Matrix ι ι ℂ}
    (hA : IsOrthogonal A) : IsOrthogonal (conjMatrix A) := by
  change (conjMatrix A)ᵀ * conjMatrix A = 1
  rw [← conjMatrix_transpose, ← conjMatrix_mul, show Aᵀ * A = 1 from hA]
  exact map_one Complex.conjAe.toRingEquiv.mapMatrix

private theorem coefficientConjugation_involutive :
    Function.Involutive (coefficientConjugation (ι := ι)) :=
  fun X => Subtype.ext (Matrix.ext fun i j => star_star (X.val i j))

private theorem complex_orthogonal_eq_conj (hcard : 2 < Fintype.card ι)
    (A : Matrix ι ι ℂ) (hA : IsOrthogonal A)
    (hcomm : CommutesWithConjugation (orthogonalAction A hA)) :
    conjMatrix A = A := by
  let C := conjMatrix A
  have hC : IsOrthogonal C := conjMatrix_orthogonal hA
  have hActions (X : so ι) : C * X.val * Cᵀ = A * X.val * Aᵀ := by
    have h := congrArg Subtype.val (hcomm (coefficientConjugation X))
    change conjMatrix (A * (coefficientConjugation X).val * Aᵀ) =
      A * (coefficientConjugation (coefficientConjugation X)).val * Aᵀ at h
    rw [coefficientConjugation_involutive X, conjMatrix_mul, conjMatrix_mul,
      conjMatrix_transpose] at h
    change C * (coefficientConjugation (coefficientConjugation X)).val * Cᵀ =
      A * X.val * Aᵀ at h
    rwa [coefficientConjugation_involutive X] at h
  let D := Aᵀ * C
  have hD : IsOrthogonal D := orthogonal_mul (orthogonal_transpose hA) hC
  have hDcomm (X : so ι) : D * X.val = X.val * D := by
    calc
      D * X.val = Aᵀ * (C * X.val * Cᵀ) * C := by
        calc
          _ = Aᵀ * (C * X.val) * (Cᵀ * C) := by
            rw [show Cᵀ * C = 1 from hC, mul_one, ← mul_assoc]
          _ = _ := by noncomm_ring
      _ = Aᵀ * (A * X.val * Aᵀ) * C := by rw [hActions]
      _ = (Aᵀ * A) * (X.val * D) := by dsimp [D]; noncomm_ring
      _ = X.val * D := by rw [show Aᵀ * A = 1 from hA, one_mul]
  obtain ⟨c, hc⟩ := commuting_with_skew_is_scalar hcard D hDcomm
  obtain ⟨i, _, _, _⟩ := Fintype.two_lt_card_iff.mp hcard
  have hsquare : c * c = 1 := by
    change Dᵀ * D = 1 at hD
    rw [hc, transpose_smul, transpose_one, smul_mul_smul_comm, one_mul] at hD
    simpa using congrArg (fun M : Matrix ι ι ℂ => M i i) hD
  have hfactor : (c - 1) * (c + 1) = 0 := by linear_combination hsquare
  have hnonneg : 0 ≤ (D i i).re := by
    change 0 ≤ ((Aᵀ * conjMatrix A) i i).re
    rw [Matrix.mul_apply, Complex.re_sum]
    apply Finset.sum_nonneg
    intro j _
    rw [transpose_apply, conjMatrix_apply]
    change 0 ≤ (A j i * (starRingEnd ℂ) (A j i)).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have hcone : c = 1 := by
    rcases mul_eq_zero.mp hfactor with h | h
    · exact sub_eq_zero.mp h
    · have hneg : c = -1 := eq_neg_of_add_eq_zero_left h
      rw [hc, hneg] at hnonneg
      simp at hnonneg
      linarith
  have hDone : D = 1 := by simp [hc, hcone]
  calc
    C = (A * Aᵀ) * C := by rw [mul_eq_one_comm.mp hA, one_mul]
    _ = A * D := mul_assoc ..
    _ = A := by rw [hDone, mul_one]

theorem complex_has_real_representative : complex_has_real_representative_type.{u} := by
  rintro ι _ _ hcard g ⟨A, hA, rfl⟩ hcomm
  have hreal := complex_orthogonal_eq_conj hcard A hA hcomm
  let B : Matrix ι ι ℝ := A.map Complex.re
  have hBA : complexMatrix B = A := by
    ext i j
    apply Complex.conj_eq_iff_re.mp
    exact congrArg (fun M : Matrix ι ι ℂ => M i j) hreal
  have hB : IsOrthogonal B := by
    change Bᵀ * B = 1
    apply (Matrix.map_injective Complex.ofReal_injective :
      Function.Injective (complexMatrix (ι := ι)))
    change complexMatrix (Bᵀ * B) = complexMatrix 1
    rw [show complexMatrix (Bᵀ * B) = complexMatrix Bᵀ * complexMatrix B from
      map_mul Complex.ofRealHom.mapMatrix Bᵀ B, complexMatrix_transpose, hBA]
    exact hA.trans (map_one Complex.ofRealHom.mapMatrix).symm
  refine ⟨B, hB, ?_⟩
  apply Subtype.ext
  ext X : 1
  apply Subtype.ext
  simp only [orthogonalAction_apply, hBA]

theorem real_representative_of_inner_difference : real_representative_of_inner_difference_type.{u} := by
  intro ι _ _ hcard g h hInner hRep hComm
  apply complex_has_real_representative hcard g _ hComm
  simpa using complex_representative_mul
    (inner_has_complex_representative hcard _ hInner) hRep

end LieAlgebrasAndRepresentations.OrthogonalInnerMatrixLifts
