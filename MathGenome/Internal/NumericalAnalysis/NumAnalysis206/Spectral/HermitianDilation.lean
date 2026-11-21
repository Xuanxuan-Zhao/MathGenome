import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.HermitianDilation
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section
open scoped BigOperators
open Polynomial
namespace NumAnalysis206.HermitianDilation
open MatrixData HermitianDilationDefinitions

theorem isHermitian : Specs.NumAnalysis206.HermitianDilation.isHermitian := by
  exact MatrixData.hermitianDilation_isHermitian

theorem frobenius_sq_matrix {K ι κ : Type*} [RCLike K] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (M : Matrix ι κ K) :
    D05.frobeniusNorm M.toEuclideanLin ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [D05.M14.Frobenius.squared_basis_sum _ (EuclideanSpace.basisFun _ K)]
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, EuclideanSpace.basisFun_apply]

theorem frobenius_difference_sq :
    Specs.NumAnalysis206.HermitianDilation.frobenius_difference_sq := by
  intro K _ m n A B
  rw [frobenius_sq_matrix]
  change (∑ i, ∑ j, ‖(MatrixDefinitions.hermitianDilation A -
    MatrixDefinitions.hermitianDilation B) i j‖ ^ 2) =
      2 * (Real.sqrt (∑ i, ∑ j, ‖(A - B) i j‖ ^ 2)) ^ 2
  rw [Real.sq_sqrt (by positivity)]
  simp only [Fintype.sum_sum_type, Matrix.sub_apply,
    MatrixDefinitions.hermitianDilation, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add, add_zero,
    Matrix.conjTranspose_apply, ← star_sub, norm_star]
  rw [Finset.sum_comm (f := fun i : Fin n => fun j : Fin m => ‖A j i - B j i‖ ^ 2)]
  ring

/-- A division-free block determinant calculation. -/
theorem charpoly_offDiagonal {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K) :
    (Matrix.fromBlocks 0 A B 0).charpoly * X ^ n =
      X ^ m * (B * A).charpoly.comp (X ^ 2) := by
  classical
  let M := Matrix.charmatrix (Matrix.fromBlocks 0 A B 0)
  let N := Matrix.fromBlocks (Matrix.scalar (Fin m) (X : K[X])) (A.map C)
    0 (Matrix.scalar (Fin n) (X : K[X]))
  have hMN : M * N = Matrix.fromBlocks (Matrix.scalar (Fin m) (X ^ 2 : K[X])) 0
      (-(B.map C * Matrix.scalar (Fin m) X))
      (Matrix.scalar (Fin n) (X ^ 2) - (B * A).map C) := by
    dsimp [M, N]
    rw [Matrix.charmatrix_fromBlocks]
    simp only [Matrix.charmatrix_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero, add_zero,
      Matrix.neg_mul, Matrix.map_mul]
    congr 1
    · ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, pow_two]
    · ext i j : 1
      simp only [Matrix.scalar_apply, Matrix.add_apply, Matrix.neg_apply,
        Matrix.zero_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    · have hs : Matrix.scalar (Fin n) (X : K[X]) * Matrix.diagonal (fun _ => X) =
          Matrix.scalar (Fin n) (X ^ 2) := by
        ext i j : 1
        simp [Matrix.scalar_apply, Matrix.diagonal_apply, pow_two]
      rw [hs, Matrix.scalar_apply, sub_eq_add_neg, add_comm]
  have hcomp : (B * A).charpoly.comp (X ^ 2) =
      (Matrix.scalar (Fin n) (X ^ 2 : K[X]) - (B * A).map C).det := by
    change Polynomial.compRingHom (X ^ 2) (Matrix.charmatrix (B * A)).det = _
    rw [RingHom.map_det]
    congr 1
    ext i j : 1
    by_cases h : i = j <;> simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply, Polynomial.coe_compRingHom, Polynomial.sub_comp,
      Polynomial.zero_comp, Polynomial.X_comp, Polynomial.C_comp, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.diagonal_apply, h, ite_true, ite_false]
  have hd := congrArg Matrix.det hMN
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂] at hd
  simp only [N, Matrix.det_fromBlocks_zero₂₁, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul] at hd
  rw [← Matrix.scalar_apply, ← hcomp] at hd
  change (Matrix.fromBlocks 0 A B 0).charpoly * (X ^ m * X ^ n) =
    X ^ (2 * m) * (B * A).charpoly.comp (X ^ 2) at hd
  apply mul_left_cancel₀ (pow_ne_zero m (X_ne_zero (R := K)))
  calc
    X ^ m * ((Matrix.fromBlocks 0 A B 0).charpoly * X ^ n) =
        (Matrix.fromBlocks 0 A B 0).charpoly * (X ^ m * X ^ n) := by ring
    _ = _ := hd
    _ = X ^ m * (X ^ m * (B * A).charpoly.comp (X ^ 2)) := by
      rw [show 2 * m = m + m by omega, pow_add]
      ring

theorem gram_charpoly {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n) :
    (A.conjTranspose * A).charpoly =
      ∏ i : Fin n, (X - C ((A.toEuclideanLin.singularValues i : K) ^ 2)) := by
  have ht : (A.conjTranspose * A).toEuclideanLin =
      A.toEuclideanLin.adjoint.comp A.toEuclideanLin := by
    rw [Matrix.toLpLin_mul 2 2 2, A.toEuclideanLin_conjTranspose_eq_adjoint]
  calc
    _ = ((A.conjTranspose * A).toEuclideanLin).charpoly := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]
    _ = _ := by
      rw [ht, A.toEuclideanLin.isSymmetric_adjoint_comp_self.charpoly_eq
        (finrank_euclideanSpace_fin (𝕜 := K))]
      apply Finset.prod_congr rfl
      intro i _
      rw [← A.toEuclideanLin.sq_singularValues_fin (finrank_euclideanSpace_fin (𝕜 := K))]
      simp only [map_pow]

theorem gram_charpoly_comp {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n) :
    (A.conjTranspose * A).charpoly.comp (X ^ 2) =
      ∏ i ∈ Finset.range n,
        ((X - C (-A.toEuclideanLin.singularValues i : K)) *
          (X - C (A.toEuclideanLin.singularValues i : K))) := by
  rw [gram_charpoly, Polynomial.prod_comp]
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    Polynomial.pow_comp, map_neg, map_pow]
  ring

theorem singularValues_zero_of_min_le {K : Type*} [RCLike K] {m n : ℕ}
    (A : Mat K m n) (i : ℕ) (hi : min m n ≤ i) : A.toEuclideanLin.singularValues i = 0 := by
  apply A.toEuclideanLin.singularValues_eq_zero_iff_le_finrank_range.mpr
  apply le_trans _ hi
  apply le_min
  · simpa using (Submodule.finrank_le A.toEuclideanLin.range)
  · simpa using A.toEuclideanLin.finrank_range_le

theorem charpoly_factorization {K : Type*} [RCLike K] {m n : ℕ} (A : Mat K m n) :
    (hermitianDilation A).charpoly =
      X ^ ((m - min m n) + (n - min m n)) *
        ∏ i : Fin (min m n),
          ((X - C (-A.toEuclideanLin.singularValues i : K)) *
            (X - C (A.toEuclideanLin.singularValues i : K))) := by
  classical
  let q := min m n
  let f : ℕ → K[X] := fun i =>
    (X - C (-A.toEuclideanLin.singularValues i : K)) *
      (X - C (A.toEuclideanLin.singularValues i : K))
  have hn : q + (n - q) = n := Nat.add_sub_of_le (min_le_right m n)
  have hp : (A.conjTranspose * A).charpoly.comp (X ^ 2) =
      (∏ i ∈ Finset.range q, f i) * X ^ (2 * (n - q)) := by
    rw [gram_charpoly_comp]
    change (∏ i ∈ Finset.range n, f i) = _
    have hs := Finset.prod_range_add f q (n - q)
    rw [hn] at hs
    rw [hs]
    congr 1
    have hf : ∀ i ∈ Finset.range (n - q), f (q + i) = (X : K[X]) ^ 2 := by
      intro i _
      dsimp [f]
      rw [singularValues_zero_of_min_le A (q + i) (by dsimp [q]; omega)]
      simp [pow_two]
    rw [Finset.prod_congr rfl hf]
    simp [← pow_mul, Nat.mul_comm]
  have h := charpoly_offDiagonal A A.conjTranspose
  rw [hp] at h
  change (hermitianDilation A).charpoly * X ^ n = _ at h
  rw [← Fin.prod_univ_eq_prod_range] at h
  apply mul_right_cancel₀ (pow_ne_zero n (X_ne_zero (R := K)))
  calc
    (hermitianDilation A).charpoly * X ^ n = _ := h
    _ = (X ^ m * X ^ (2 * (n - q))) * (∏ i : Fin q, f i.val) := by ring
    _ = X ^ (m + 2 * (n - q)) * (∏ i : Fin q, f i.val) := by rw [← pow_add]
    _ = X ^ (((m - q) + (n - q)) + n) * (∏ i : Fin q, f i.val) := by
      congr 2
      dsimp [q]
      have := min_le_left m n
      have := min_le_right m n
      omega
    _ = _ := by rw [pow_add]; ring

theorem roots_prod_linear {K ι : Type*} [Field K] [Fintype ι] (a : ι → K) :
    (∏ i, (X - C (a i))).roots = Finset.univ.val.map a := by
  classical
  rw [Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero (a i)))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]

theorem signedSingularValues_sorted {K : Type*} [RCLike K] {m n : ℕ}
    (A : Mat K m n) : (signedSingularValues A).Pairwise (· ≤ ·) := by
  let q := min m n
  let negs := List.ofFn (fun i : Fin q => -singularValue A (i.val + 1))
  let poss := List.ofFn (fun i : Fin q => singularValue A (i.val + 1))
  have hneg : negs.Pairwise (· ≤ ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact neg_le_neg (singularValue_antitone A (by omega))
  have hpos : poss.reverse.Pairwise (· ≤ ·) := by
    rw [List.pairwise_reverse]
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact singularValue_antitone A (by omega)
  have hn : ∀ x ∈ negs, x ≤ 0 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact neg_nonpos.mpr (singularValue_nonneg A _)
  have hp : ∀ x ∈ poss.reverse, 0 ≤ x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
    exact singularValue_nonneg A _
  change (negs ++ List.replicate _ 0 ++ poss.reverse).Pairwise (· ≤ ·)
  apply List.pairwise_append.mpr
  refine ⟨?_, hpos, ?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨hneg, ?_, ?_⟩
    · simp
    · intro x hx y hy
      have hy0 : y = 0 := List.eq_of_mem_replicate hy
      simpa [hy0] using hn x hx
  · intro x hx y hy
    rcases List.mem_append.mp hx with hx | hx
    · exact (hn x hx).trans (hp y hy)
    · have hx0 : x = 0 := List.eq_of_mem_replicate hx
      simpa [hx0] using hp y hy

theorem roots_eq_signedSingularValues {K : Type*} [RCLike K] {m n : ℕ}
    (A : Mat K m n) :
    (hermitianDilation A).charpoly.roots.map RCLike.re =
      (signedSingularValues A : Multiset ℝ) := by
  classical
  have hneg : (∏ i : Fin (min m n), (X - C (-A.toEuclideanLin.singularValues i : K))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  have hpos : (∏ i : Fin (min m n), (X - C (A.toEuclideanLin.singularValues i : K))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)
  rw [charpoly_factorization, Finset.prod_mul_distrib,
    Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (mul_ne_zero hneg hpos)),
    Polynomial.roots_mul (mul_ne_zero hneg hpos), roots_prod_linear, roots_prod_linear,
    Polynomial.roots_X_pow]
  simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton,
    Multiset.map_map, Function.comp_def, RCLike.ofReal_re, map_neg, RCLike.zero_re]
  simp only [signedSingularValues, ← Multiset.coe_add, Multiset.coe_reverse,
    MatrixDefinitions.singularValue, Nat.add_sub_cancel]
  rw [Fin.univ_val_map, Fin.univ_val_map]
  simp only [Multiset.coe_replicate, Multiset.nsmul_singleton]
  ac_rfl

theorem eigenvalue_list : Specs.NumAnalysis206.HermitianDilation.eigenvalue_list := by
  intro K _ m n A
  rw [roots_eq_signedSingularValues, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simpa only [decide_eq_true_eq] using signedSingularValues_sorted A

theorem canonical_eigenvalue_list :
    Specs.NumAnalysis206.HermitianDilation.canonical_eigenvalue_list := by
  intro K _ m n A hA
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hd : Module.finrank K (EuclideanSpace K (Fin m ⊕ Fin n)) = m + n := by simp
  let e := hT.eigenvalues hd
  have hc : (hermitianDilation A).toEuclideanLin.charpoly =
      (hermitianDilation A).charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]
  have hr : (hermitianDilation A).charpoly.roots.map RCLike.re =
      (List.ofFn e : Multiset ℝ) := by
    rw [← hc, hT.roots_charpoly_eq_eigenvalues hd]
    simp only [Multiset.map_map, Function.comp_def, RCLike.ofReal_re]
    rw [Fin.univ_val_map]
  have hrev : (List.ofFn (fun i => e i.rev) : Multiset ℝ) = List.ofFn e := by
    apply Multiset.coe_eq_coe.mpr
    simpa only [Function.comp_def, Fin.revPerm_apply] using Fin.revPerm.ofFn_comp_perm e
  have hs : (List.ofFn (fun i => e i.rev)).Pairwise (· ≤ ·) := by
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact hT.eigenvalues_antitone hd (Fin.rev_le_rev.mpr (le_of_lt hij))
  have he : ((hermitianDilation A).charpoly.roots.map RCLike.re).sort (· ≤ ·) =
      List.ofFn (fun i => e i.rev) := by
    rw [hr, ← hrev, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [decide_eq_true_eq] using hs
  exact he.symm.trans (eigenvalue_list A)

end NumAnalysis206.HermitianDilation
