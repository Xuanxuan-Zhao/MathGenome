import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.OperatorNorm
import MathGenome.Internal.D05.M14.Frobenius

noncomputable section
open scoped BigOperators ENNReal DirectSum
namespace NumAnalysis206.MatrixData

abbrev Mat : Specs.NumAnalysis206.MatrixData.Mat_type :=
  @NumAnalysis206.MatrixDefinitions.Mat

abbrev Vec : Specs.NumAnalysis206.MatrixData.Vec_type :=
  @NumAnalysis206.MatrixDefinitions.Vec

abbrev IsPermutation : Specs.NumAnalysis206.MatrixData.IsPermutation_type :=
  @NumAnalysis206.MatrixDefinitions.IsPermutation

abbrev IsLowerTriangular : Specs.NumAnalysis206.MatrixData.IsLowerTriangular_type :=
  @NumAnalysis206.MatrixDefinitions.IsLowerTriangular

abbrev IsUpperTriangular : Specs.NumAnalysis206.MatrixData.IsUpperTriangular_type :=
  @NumAnalysis206.MatrixDefinitions.IsUpperTriangular

abbrev IsUnitLowerTriangular : Specs.NumAnalysis206.MatrixData.IsUnitLowerTriangular_type :=
  @NumAnalysis206.MatrixDefinitions.IsUnitLowerTriangular

abbrev IsRowEchelon : Specs.NumAnalysis206.MatrixData.IsRowEchelon_type :=
  @NumAnalysis206.MatrixDefinitions.IsRowEchelon

abbrev adjoint : Specs.NumAnalysis206.MatrixData.adjoint_type :=
  @NumAnalysis206.MatrixDefinitions.adjoint

abbrev entrywiseAbs : Specs.NumAnalysis206.MatrixData.entrywiseAbs_type :=
  @NumAnalysis206.MatrixDefinitions.entrywiseAbs

abbrev EntrywiseLE : Specs.NumAnalysis206.MatrixData.EntrywiseLE_type :=
  @NumAnalysis206.MatrixDefinitions.EntrywiseLE

abbrev operatorNorm : Specs.NumAnalysis206.MatrixData.operatorNorm_type :=
  @NumAnalysis206.MatrixDefinitions.operatorNorm

abbrev frobeniusNorm : Specs.NumAnalysis206.MatrixData.frobeniusNorm_type :=
  @NumAnalysis206.MatrixDefinitions.frobeniusNorm

abbrev columns : Specs.NumAnalysis206.MatrixData.columns_type :=
  @Specs.NumAnalysis206.MatrixData.columns_value

abbrev FullColumnRank : Specs.NumAnalysis206.MatrixData.FullColumnRank_type :=
  @NumAnalysis206.MatrixDefinitions.FullColumnRank

abbrev ReducedQR : Specs.NumAnalysis206.MatrixData.ReducedQR_type :=
  @NumAnalysis206.MatrixDefinitions.ReducedQR

abbrev PositiveRealDiagonal : Specs.NumAnalysis206.MatrixData.PositiveRealDiagonal_type :=
  @NumAnalysis206.MatrixDefinitions.PositiveRealDiagonal

abbrev NonnegativeRealDiagonal : Specs.NumAnalysis206.MatrixData.NonnegativeRealDiagonal_type :=
  @NumAnalysis206.MatrixDefinitions.NonnegativeRealDiagonal

abbrev SemidefiniteCholeskyNormalization : Specs.NumAnalysis206.MatrixData.SemidefiniteCholeskyNormalization_type :=
  @NumAnalysis206.MatrixDefinitions.SemidefiniteCholeskyNormalization

abbrev singularValue : Specs.NumAnalysis206.MatrixData.singularValue_type :=
  @NumAnalysis206.MatrixDefinitions.singularValue

abbrev rank : Specs.NumAnalysis206.MatrixData.rank_type :=
  @NumAnalysis206.MatrixDefinitions.rank

abbrev pseudoinverse : Specs.NumAnalysis206.MatrixData.pseudoinverse_type :=
  @NumAnalysis206.MatrixDefinitions.pseudoinverse

abbrev svdTruncation : Specs.NumAnalysis206.MatrixData.svdTruncation_type :=
  @NumAnalysis206.MatrixDefinitions.svdTruncation

abbrev eigenvalue : Specs.NumAnalysis206.MatrixData.eigenvalue_type :=
  @NumAnalysis206.MatrixDefinitions.eigenvalue

abbrev eigenbasis : Specs.NumAnalysis206.MatrixData.eigenbasis_type :=
  @NumAnalysis206.MatrixDefinitions.eigenbasis

abbrev rayleigh : Specs.NumAnalysis206.MatrixData.rayleigh_type :=
  @NumAnalysis206.MatrixDefinitions.rayleigh

abbrev spectralSubspace : Specs.NumAnalysis206.MatrixData.spectralSubspace_type :=
  @NumAnalysis206.MatrixDefinitions.spectralSubspace

abbrev spectralProjection : Specs.NumAnalysis206.MatrixData.spectralProjection_type :=
  @NumAnalysis206.MatrixDefinitions.spectralProjection

abbrev hermitianDilation : Specs.NumAnalysis206.MatrixData.hermitianDilation_type :=
  @NumAnalysis206.MatrixDefinitions.hermitianDilation

abbrev IsDiagonalizable : Specs.NumAnalysis206.MatrixData.IsDiagonalizable_type :=
  @NumAnalysis206.MatrixDefinitions.IsDiagonalizable

abbrev eigenspaceDecomposition : Specs.NumAnalysis206.MatrixData.eigenspaceDecomposition_type :=
  @NumAnalysis206.MatrixDefinitions.eigenspaceDecomposition

abbrev spectralComponent : Specs.NumAnalysis206.MatrixData.spectralComponent_type :=
  @NumAnalysis206.MatrixDefinitions.spectralComponent

abbrev subordinateNorm : Specs.NumAnalysis206.MatrixData.subordinateNorm_type :=
  @NumAnalysis206.MatrixDefinitions.subordinateNorm

abbrev lpVectorNorm : Specs.NumAnalysis206.MatrixData.lpVectorNorm_type :=
  @NumAnalysis206.MatrixDefinitions.lpVectorNorm

abbrev lpOperatorNorm : Specs.NumAnalysis206.MatrixData.lpOperatorNorm_type :=
  @NumAnalysis206.MatrixDefinitions.lpOperatorNorm


theorem toEuclidean_apply : Specs.NumAnalysis206.MatrixData.toEuclidean_apply := by
  intro K _ m n A x i
  rfl

theorem toEuclidean_mul : Specs.NumAnalysis206.MatrixData.toEuclidean_mul := by
  intro K _ m n l A B
  exact Matrix.toLpLin_mul 2 2 2 A B

theorem toEuclidean_adjoint : Specs.NumAnalysis206.MatrixData.toEuclidean_adjoint := by
  intro K _ m n A
  exact A.toEuclideanLin_conjTranspose_eq_adjoint

theorem rank_eq_matrix_rank : Specs.NumAnalysis206.MatrixData.rank_eq_matrix_rank := by
  intro K _ m n A
  exact (A.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun (Fin m) K).toBasis
    (EuclideanSpace.basisFun (Fin n) K).toBasis).symm

theorem columns_eq_apply_basis : Specs.NumAnalysis206.MatrixData.columns_eq_apply_basis := by
  intro K _ m n A j
  ext i
  simp [NumAnalysis206.MatrixDefinitions.columns, D05.QrCholesky.columns,
    Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply]

theorem fullColumnRank_iff_injective : Specs.NumAnalysis206.MatrixData.fullColumnRank_iff_injective := by
  intro K _ m n A
  have hc : NumAnalysis206.MatrixDefinitions.columns A =
      A.toEuclideanLin ∘ (EuclideanSpace.basisFun (Fin n) K) :=
    funext (columns_eq_apply_basis A)
  change LinearIndependent K (NumAnalysis206.MatrixDefinitions.columns A) ↔ _
  rw [hc]
  constructor
  · intro h
    exact LinearMap.injective_of_linearIndependent
      (EuclideanSpace.basisFun (Fin n) K).toBasis.span_eq h
  · intro h
    exact (EuclideanSpace.basisFun (Fin n) K).toBasis.linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr h)

theorem operatorNorm_eq_D05 : Specs.NumAnalysis206.MatrixData.operatorNorm_eq_D05 := by
  intro K _ m n A
  exact (D05.M14.OperatorNorm.eq_continuous_opNorm A.toEuclideanLin).symm

theorem frobeniusNorm_sq_columns : Specs.NumAnalysis206.MatrixData.frobeniusNorm_sq_columns := by
  intro K _ m n A
  unfold NumAnalysis206.MatrixDefinitions.frobeniusNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (EuclideanSpace.norm_sq_eq (NumAnalysis206.MatrixDefinitions.columns A j)).symm

theorem frobeniusNorm_eq_D05 : Specs.NumAnalysis206.MatrixData.frobeniusNorm_eq_D05 := by
  intro K _ m n A
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (D05.M14.Frobenius.nonneg A.toEuclideanLin)).mp
  calc
    _ = ∑ j, ‖NumAnalysis206.MatrixDefinitions.columns A j‖ ^ 2 := frobeniusNorm_sq_columns A
    _ = ∑ j, ‖A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) K j)‖ ^ 2 :=
      Finset.sum_congr rfl (fun j _ => congrArg (fun v => ‖v‖ ^ 2) (columns_eq_apply_basis A j))
    _ = _ := (D05.M14.Frobenius.squared_basis_sum A.toEuclideanLin
      (EuclideanSpace.basisFun (Fin n) K)).symm

theorem frobeniusNorm_sq_basis : Specs.NumAnalysis206.MatrixData.frobeniusNorm_sq_basis := by
  intro K _ m n ι _ A b
  rw [frobeniusNorm_eq_D05 A]
  exact D05.M14.Frobenius.squared_basis_sum A.toEuclideanLin b

theorem singularValue_nonneg : Specs.NumAnalysis206.MatrixData.singularValue_nonneg := by
  intro K _ m n A i
  exact A.toEuclideanLin.singularValues_nonneg (i - 1)

theorem singularValue_antitone : Specs.NumAnalysis206.MatrixData.singularValue_antitone := by
  intro K _ m n A i j hij
  exact A.toEuclideanLin.singularValues_antitone (Nat.sub_le_sub_right hij 1)

theorem singularValue_pos_iff : Specs.NumAnalysis206.MatrixData.singularValue_pos_iff := by
  intro K _ m n A i hi
  change 0 < A.toEuclideanLin.singularValues (i - 1) ↔ _
  rw [A.toEuclideanLin.singularValues_pos_iff_lt_finrank_range]
  change i - 1 < rank A ↔ i ≤ rank A
  omega

theorem singularValue_zero_of_rank_lt : Specs.NumAnalysis206.MatrixData.singularValue_zero_of_rank_lt := by
  intro K _ m n A i hi
  apply A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr
  change NumAnalysis206.MatrixDefinitions.rank A ≤ i - 1
  change NumAnalysis206.MatrixDefinitions.rank A < i at hi
  omega

theorem singularValue_zero_of_domain_lt : Specs.NumAnalysis206.MatrixData.singularValue_zero_of_domain_lt := by
  intro K _ m n A i hi
  apply A.toEuclideanLin.singularValues_of_finrank_le
  rw [finrank_euclideanSpace_fin]
  omega

theorem eigenvalue_monotone : Specs.NumAnalysis206.MatrixData.eigenvalue_monotone := by
  intro K _ n A hA i j hij
  exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues_antitone
    (finrank_euclideanSpace_fin (𝕜 := K)) (Fin.rev_le_rev.mpr hij)

theorem eigenbasis_action : Specs.NumAnalysis206.MatrixData.eigenbasis_action := by
  intro K _ n A hA i
  simpa only [NumAnalysis206.MatrixDefinitions.eigenbasis,
    NumAnalysis206.MatrixDefinitions.eigenvalue, OrthonormalBasis.reindex_apply,
    Fin.revPerm_symm, Fin.revPerm_apply] using
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
      (finrank_euclideanSpace_fin (𝕜 := K)) i.rev

theorem pseudoinverse_transport : Specs.NumAnalysis206.MatrixData.pseudoinverse_transport := by
  intro K _ m n A
  exact Matrix.toEuclideanLin.apply_symm_apply _

theorem svdTruncation_transport : Specs.NumAnalysis206.MatrixData.svdTruncation_transport := by
  intro K _ m n A d k
  exact Matrix.toEuclideanLin.apply_symm_apply _

theorem hermitianDilation_isHermitian : Specs.NumAnalysis206.MatrixData.hermitianDilation_isHermitian := by
  intro K _ m n A
  simp [NumAnalysis206.MatrixDefinitions.hermitianDilation, Matrix.isHermitian_fromBlocks_iff]

theorem spectralComponent_mem : Specs.NumAnalysis206.MatrixData.spectralComponent_mem := by
  intro K V _ _ _ T hT μ x
  classical
  exact ((DirectSum.component K K (fun ν : K => T.eigenspace ν) μ)
    (eigenspaceDecomposition T hT x)).property

theorem eigenspaceDecomposition_recompose : Specs.NumAnalysis206.MatrixData.eigenspaceDecomposition_recompose := by
  intro K V _ _ _ T hT x
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun μ : K => T.eigenspace μ))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.eigenspaces_iSupIndep hT)).apply_symm_apply x



theorem upperTriangular_iff : Specs.NumAnalysis206.MatrixData.upperTriangular_iff := by
  intro K _ n A
  rfl

theorem lowerTriangular_iff : Specs.NumAnalysis206.MatrixData.lowerTriangular_iff := by
  intro K _ n A
  rfl

theorem operatorNorm_apply_le : Specs.NumAnalysis206.MatrixData.operatorNorm_apply_le := by
  intro K _ m n A x
  exact A.toEuclideanLin.toContinuousLinearMap.le_opNorm x

theorem operatorNorm_mul_le : Specs.NumAnalysis206.MatrixData.operatorNorm_mul_le := by
  intro K _ m n l A B
  rw [operatorNorm_eq_D05, operatorNorm_eq_D05, operatorNorm_eq_D05, toEuclidean_mul]
  exact D05.M14.OperatorNorm.comp_le _ _

theorem operatorNorm_adjoint : Specs.NumAnalysis206.MatrixData.operatorNorm_adjoint := by
  intro K _ m n A
  rw [operatorNorm_eq_D05, operatorNorm_eq_D05, toEuclidean_adjoint]
  exact D05.M14.OperatorNorm.adjoint_eq _

theorem spectralProjection_characterization : Specs.NumAnalysis206.MatrixData.spectralProjection_characterization := by
  intro K _ n A hA s x
  exact ⟨(spectralSubspace A s).starProjection_apply_mem x,
    (spectralSubspace A s).sub_starProjection_mem_orthogonal x⟩

theorem diagonalizable_iff_eigenbasis : Specs.NumAnalysis206.MatrixData.diagonalizable_iff_eigenbasis := by
  intro K V _ _ _ T
  classical
  constructor
  · intro hT
    let h := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.eigenspaces_iSupIndep hT
    let b := h.collectedBasis (fun μ : K => Module.Free.chooseBasis K (T.eigenspace μ))
    exact ⟨_, b, (fun i => i.1), fun i =>
      Module.End.mem_eigenspace_iff.mp (h.collectedBasis_mem _ i)⟩
  · rintro ⟨ι, b, μ, hb⟩
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (μ i) (Module.End.mem_eigenspace_iff.mpr (hb i))

end NumAnalysis206.MatrixData
