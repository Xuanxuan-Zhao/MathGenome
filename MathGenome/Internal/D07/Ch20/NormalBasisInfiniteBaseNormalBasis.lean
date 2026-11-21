import MathGenome.Internal.Specs.D07.Ch20.NormalBasisInfiniteBaseNormalBasis
import MathGenome.Internal.D07.Ch14.IndependentEmbeddings
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

universe u v w
noncomputable section

namespace D07.Ch20.NormalBasisInfiniteBaseNormalBasis

open MvPolynomial
open scoped Classical Matrix
open Specs.D07.Ch20.NormalBasisInfiniteBaseNormalBasis

/-- The identity-supported assignment turns the group matrix into the
permutation matrix for inversion. This works for a noncommutative group. -/
theorem group_determinant_nonzero (G : Type w) [Group G] [Fintype G] [DecidableEq G]
    (L : Type v) [Field L] : groupDeterminant G L ≠ 0 := by
  let y : G → L := fun g => if g = 1 then 1 else 0
  have hm : (Matrix.of fun σ τ : G => y (σ * τ)) =
      (1 : Matrix G G L).submatrix (Equiv.inv G) id := by
    ext σ τ
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.inv_apply, id_eq,
      Matrix.one_apply, y]
    simp only [mul_eq_one_iff_inv_eq]
  have hdet : (Matrix.of fun σ τ : G => y (σ * τ)).det ≠ 0 := by
    rw [hm, Matrix.det_permute, Matrix.det_one, mul_one]
    exact (Units.isUnit _).map (Int.castRingHom L) |>.ne_zero
  intro hz
  apply hdet
  have he := congrArg (eval y) hz
  simpa only [groupDeterminant, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map, Matrix.of_apply, eval_X, map_zero] using he

/-- Restricting distinct embeddings to a basis preserves their independence:
a relation on the basis extends K-linearly to all of L. -/
theorem embedding_matrix_nonsingular : EmbeddingMatrixNonsingular.{u, v} := by
  intro K L _ _ _ _ _ b
  classical
  have hσ : LinearIndependent L (fun σ : L ≃ₐ[K] L => (σ : L → L)) := by
    apply Ch14.IndependentEmbeddings.embeddings_linearIndependent L L _
      (fun σ : L ≃ₐ[K] L => σ.toRingHom)
    intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  have hrows : LinearIndependent L (embeddingMatrix b).row := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    apply Fintype.linearIndependent_iff.mp hσ c
    ext x
    let f : L →ₗ[K] L := ∑ σ : L ≃ₐ[K] L, c σ • σ.toLinearMap
    have hf : f = 0 := by
      apply b.ext
      intro j
      simpa [f, embeddingMatrix, Matrix.row, LinearMap.sum_apply,
        LinearMap.smul_apply] using congrFun hc j
    have hx := congrArg (fun f : L →ₗ[K] L => f x) hf
    simpa [f, LinearMap.sum_apply, LinearMap.smul_apply] using hx
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hrows)).ne_zero

/-- The infinite evaluation box is the image of K inside L; coefficients
are allowed to be arbitrary elements of L. -/
theorem polynomial_nonvanishing : PolynomialNonvanishing.{u, v, w} := by
  intro K L _ _ _ _ ι p hp
  classical
  by_contra! h
  apply hp
  refine MvPolynomial.funext_set (fun _ : ι => Set.range (algebraMap K L))
    (fun _ => Set.infinite_range_of_injective (algebraMap K L).injective) ?_
  intro x hx
  obtain ⟨x, rfl⟩ := Set.range_piMap _ ▸ hx
  change eval (algebraMap K L ∘ x) p = eval (algebraMap K L ∘ x) 0
  simpa only [map_zero] using h x

/-- Composition corresponds to matrix multiplication (in substitution order). -/
theorem coordinate_substitution_comp {L : Type v} [Field L]
    {ι : Type w} [Fintype ι] (A B : Matrix ι ι L) :
    (coordinateSubstitution B).comp (coordinateSubstitution A) =
      coordinateSubstitution (A * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, coordinateSubstitution, aeval_X]
  simp only [map_sum, map_mul, aeval_C, aeval_X]
  change (∑ j, C (A i j) * (∑ k, C (B j k) * X k)) =
    ∑ k, C ((A * B) i k) * X k
  simp only [Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
    ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]

@[simp]
theorem coordinate_substitution_one {L : Type v} [Field L]
    {ι : Type w} [Fintype ι] [DecidableEq ι] :
    coordinateSubstitution (1 : Matrix ι ι L) = AlgHom.id L (MvPolynomial ι L) := by
  ext i
  simp [coordinateSubstitution, Matrix.one_apply]

/-- A nonsingular matrix defines a change of polynomial variables whose inverse
is substitution by the inverse matrix. -/
def linearSubstitutionEquiv {L : Type v} [Field L]
    {ι : Type w} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L) (hA : A.det ≠ 0) :
    MvPolynomial ι L ≃ₐ[L] MvPolynomial ι L :=
  AlgEquiv.ofAlgHom (coordinateSubstitution A) (coordinateSubstitution A⁻¹)
    (by rw [coordinate_substitution_comp, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
        coordinate_substitution_one])
    (by rw [coordinate_substitution_comp, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
        coordinate_substitution_one])

theorem embedding_substitution_invertible : EmbeddingSubstitutionInvertible.{u, v} := by
  intro K L _ _ _ _ _ b
  classical
  exact ⟨linearSubstitutionEquiv (embeddingMatrix b) (embedding_matrix_nonsingular K L b),
    fun _ => rfl⟩

theorem substituted_determinant_nonzero : SubstitutedDeterminantNonzero.{u, v} := by
  intro K L _ _ _ _ _ b
  classical
  obtain ⟨e, he⟩ := embedding_substitution_invertible K L b
  rw [← he]
  exact e.injective.ne (group_determinant_nonzero (L ≃ₐ[K] L) L) |>.trans_eq (map_zero e)

/-- Evaluating the substituted determinant gives exactly the source's matrix
of conjugates of the element with the selected K-coordinates. -/
theorem evaluated_group_determinant {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (b : Module.Basis (L ≃ₐ[K] L) K L) (x : (L ≃ₐ[K] L) → K) :
    eval (algebraMap K L ∘ x)
      (coordinateSubstitution (embeddingMatrix b) (groupDeterminant (L ≃ₐ[K] L) L)) =
    (Matrix.of fun σ τ : L ≃ₐ[K] L => (σ * τ) (∑ j, x j • b j)).det := by
  classical
  change (eval (algebraMap K L ∘ x))
    ((coordinateSubstitution (embeddingMatrix b)).toRingHom
      (Matrix.det (Matrix.of fun σ τ : L ≃ₐ[K] L => X (σ * τ)))) = _
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext σ τ
  simp [Matrix.map, coordinateSubstitution, embeddingMatrix, map_sum,
    Algebra.smul_def, mul_comm]

theorem normal_basis_from_coordinates : NormalBasisFromCoordinates.{u, v} := by
  intro K L _ _ _ _ _ _ b
  classical
  obtain ⟨x, hx⟩ := polynomial_nonvanishing K L (L ≃ₐ[K] L) _
    (substituted_determinant_nonzero K L b)
  refine ⟨x, hx, ?_⟩
  let a : L := ∑ j, x j • b j
  let M : Matrix (L ≃ₐ[K] L) (L ≃ₐ[K] L) L := Matrix.of fun σ τ => (σ * τ) a
  have hdet : M.det ≠ 0 := by
    simpa only [evaluated_group_determinant] using hx
  have hi : LinearIndependent K (fun τ : L ≃ₐ[K] L => τ a) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hkill : M *ᵥ (fun τ => algebraMap K L (c τ)) = 0 := by
      ext σ
      have h := congrArg (fun z : L => σ z) hc
      simpa [M, Matrix.mulVec, dotProduct, map_sum, Algebra.smul_def, mul_comm] using h
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hdet hkill
    intro τ
    apply (algebraMap K L).injective
    simpa using congrFun hz τ
  let B := basisOfLinearIndependentOfCardEqFinrank hi
    (Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L))
  exact ⟨B, fun σ => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hi _) σ⟩

theorem normal_basis_exists : NormalBasisExists.{u, v} := by
  intro K L _ _ _ _ _ _
  classical
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L :=
    Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank K L)
  let b : Module.Basis (L ≃ₐ[K] L) K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨x, _, B, hB⟩ := normal_basis_from_coordinates K L b
  exact ⟨∑ j, x j • b j, B, hB⟩

end D07.Ch20.NormalBasisInfiniteBaseNormalBasis
