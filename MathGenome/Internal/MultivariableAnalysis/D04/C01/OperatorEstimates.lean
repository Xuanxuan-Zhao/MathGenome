import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.OperatorEstimates
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Multilinear.Basis

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04

private def linearContinuous {n m : ℕ} (A : E n →ₗ[ℝ] E m) : E n →L[ℝ] E m :=
  LinearMap.toContinuousLinearMap A

private theorem linear_norm_bridge {n m : ℕ} (A : E n →ₗ[ℝ] E m) :
    linearOperatorNorm A = ‖linearContinuous A‖ :=
  linearOperatorNorm_eq_standard (linearContinuous A)

theorem linear_continuous {n m : ℕ} (A : E n →ₗ[ℝ] E m) : Continuous A :=
  A.continuous_of_finiteDimensional

theorem linear_norm_finite {n m : ℕ} (A : E n →ₗ[ℝ] E m) :
    BddAbove ((fun v => ‖A v‖) '' {v | ‖v‖ ≤ 1}) ∧ 0 ≤ linearOperatorNorm A := by
  refine ⟨⟨‖linearContinuous A‖, ?_⟩, ?_⟩
  · rintro r ⟨v, hv, rfl⟩
    exact (linearContinuous A).unit_le_opNorm v hv
  · rw [linear_norm_bridge]; exact norm_nonneg _

theorem linear_apply_bound {n m : ℕ} (A : E n →ₗ[ℝ] E m) (v : E n) :
    ‖A v‖ ≤ linearOperatorNorm A * ‖v‖ := by
  rw [linear_norm_bridge]
  exact (linearContinuous A).le_opNorm v

theorem linear_comp_bound {n m p : ℕ} (A : E n →ₗ[ℝ] E m) (B : E m →ₗ[ℝ] E p) :
    linearOperatorNorm (B.comp A) ≤ linearOperatorNorm B * linearOperatorNorm A := by
  simp only [linear_norm_bridge]
  exact ContinuousLinearMap.opNorm_comp_le (linearContinuous B) (linearContinuous A)

private theorem multilinear_expansion {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) (v : Fin k → E n) :
    T v = ∑ j : Fin k → Fin n, (∏ i, v i (j i)) • T (fun i => standardBasis n (j i)) := by
  have hv (i : Fin k) : v i = ∑ j : Fin n, v i j • standardBasis n j := by
    simpa [standardBasis, EuclideanSpace.basisFun_repr] using
      ((standardBasis n).sum_repr (v i)).symm
  conv_lhs => rw [show v = (fun i => ∑ j : Fin n, v i j • standardBasis n j) from funext hv]
  rw [T.map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact T.map_smul_univ _ _

theorem multilinear_continuous {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) : Continuous T := by
  have he : (fun v => T v) =
      (fun v => ∑ j : Fin k → Fin n, (∏ i, v i (j i)) • T (fun i => standardBasis n (j i))) :=
    funext (multilinear_expansion T)
  rw [show (T : (Fin k → E n) → E m) = _ from he]
  apply continuous_finsetSum
  intro j _
  have hc : Continuous (fun v : Fin k → E n => ∏ i, v i (j i)) := by
    exact continuous_finsetProd _ (fun i _ =>
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) (j i)).comp (continuous_apply i))
  exact hc.smul continuous_const

private def multilinearContinuous {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) (E m) :=
  ⟨T, multilinear_continuous T⟩

private theorem multilinear_norm_bridge {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :
    multilinearOperatorNorm T = ‖multilinearContinuous T‖ :=
  multilinearOperatorNorm_eq_standard (multilinearContinuous T)

theorem multilinear_norm_finite {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :
    BddAbove ((fun v => ‖T v‖) '' {v | ∀ i, ‖v i‖ ≤ 1}) ∧
      0 ≤ multilinearOperatorNorm T := by
  refine ⟨⟨‖multilinearContinuous T‖, ?_⟩, ?_⟩
  · rintro r ⟨v, hv, rfl⟩
    exact (multilinearContinuous T).unit_le_opNorm
      ((pi_norm_le_iff_of_nonneg zero_le_one).mpr hv)
  · rw [multilinear_norm_bridge]; exact norm_nonneg _

theorem multilinear_apply_bound {n m k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) (v : Fin k → E n) :
    ‖T v‖ ≤ multilinearOperatorNorm T * ∏ i, ‖v i‖ := by
  rw [multilinear_norm_bridge]
  exact (multilinearContinuous T).le_opNorm v


private def linearCoefficients (n m : ℕ) :
    (E n →L[ℝ] E m) →ₗ[ℝ] (Fin m × Fin n → ℝ) where
  toFun A ij := A (standardBasis n ij.2) ij.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem linearCoefficients_injective (n m : ℕ) :
    Function.Injective (linearCoefficients n m) := by
  intro A B h
  apply ContinuousLinearMap.coe_injective
  have he : A.toLinearMap = B.toLinearMap := (standardBasis n).ext fun j => by
    ext i
    exact congrFun h (i, j)
  exact he

theorem linear_operator_tendsto {ι : Type*} {n m : ℕ} (l : Filter ι)
    (f : ι → E n →ₗ[ℝ] E m) (A : E n →ₗ[ℝ] E m) :
    Tendsto (fun x => linearOperatorNorm (f x - A)) l (𝓝 0) ↔
      ∀ i j, Tendsto (fun x => matrixOfLinearMap (f x) i j) l
        (𝓝 (matrixOfLinearMap A i j)) := by
  simp_rw [linear_norm_bridge]
  change Tendsto (fun x => ‖linearContinuous (f x) - linearContinuous A‖) l (𝓝 0) ↔ _
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  let c := linearCoefficients n m
  let : FiniteDimensional ℝ (E n →L[ℝ] E m) :=
    FiniteDimensional.of_injective c (linearCoefficients_injective n m)
  rw [(LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (linearCoefficients_injective n m))).tendsto_nhds_iff]
  rw [tendsto_pi_nhds]
  simp only [Function.comp_apply, linearCoefficients,
    matrixOfLinearMap_apply, Prod.forall]
  rfl

private def multilinearCoefficients (n m k : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) (E m) →ₗ[ℝ]
      ((Fin k → Fin n) × Fin m → ℝ) where
  toFun T ji := T (fun r => standardBasis n (ji.1 r)) ji.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem multilinearCoefficients_injective (n m k : ℕ) :
    Function.Injective (multilinearCoefficients n m k) := by
  intro T U h
  have he : T.toMultilinearMap = U.toMultilinearMap :=
    Module.Basis.ext_multilinear (fun _ => standardBasis n) fun j => by
      ext i
      exact congrFun h (j, i)
  apply ContinuousMultilinearMap.ext
  intro v
  exact DFunLike.congr_fun he v

theorem multilinear_operator_tendsto {ι : Type*} {n m k : ℕ} (l : Filter ι)
    (f : ι → MultilinearMap ℝ (fun _ : Fin k => E n) (E m))
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :
    Tendsto (fun x => multilinearOperatorNorm (f x - T)) l (𝓝 0) ↔
      ∀ (j : Fin k → Fin n) (i : Fin m),
        Tendsto (fun x => f x (fun r => standardBasis n (j r)) i) l
          (𝓝 (T (fun r => standardBasis n (j r)) i)) := by
  simp_rw [multilinear_norm_bridge]
  change Tendsto (fun x => ‖multilinearContinuous (f x) - multilinearContinuous T‖)
    l (𝓝 0) ↔ _
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  let c := multilinearCoefficients n m k
  let : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :=
    FiniteDimensional.of_injective c (multilinearCoefficients_injective n m k)
  rw [(LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (multilinearCoefficients_injective n m k))).tendsto_nhds_iff]
  rw [tendsto_pi_nhds]
  simp only [Function.comp_apply, multilinearCoefficients,
    Prod.forall]
  rfl

theorem linear_operator_continuous {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (f : X → E n →ₗ[ℝ] E m) :
    (∀ a, Tendsto (fun x => linearOperatorNorm (f x - f a)) (𝓝 a) (𝓝 0)) ↔
      ∀ i j, Continuous (fun x => matrixOfLinearMap (f x) i j) := by
  simp_rw [linear_operator_tendsto, continuous_iff_continuousAt, ContinuousAt]
  exact forall_comm.trans (forall_congr' fun _ => forall_comm)

theorem multilinear_operator_continuous {X : Type*} [TopologicalSpace X] {n m k : ℕ}
    (f : X → MultilinearMap ℝ (fun _ : Fin k => E n) (E m)) :
    (∀ a, Tendsto (fun x => multilinearOperatorNorm (f x - f a)) (𝓝 a) (𝓝 0)) ↔
      ∀ (j : Fin k → Fin n) (i : Fin m),
        Continuous (fun x => f x (fun r => standardBasis n (j r)) i) := by
  simp_rw [multilinear_operator_tendsto, continuous_iff_continuousAt, ContinuousAt]
  exact forall_comm.trans (forall_congr' fun _ => forall_comm)


theorem matrix_entry_bound {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) :
    |M i j| ≤ linearOperatorNorm (matrixLinearEquiv m n M) := by
  have hn : ‖standardBasis n j‖ = 1 := by
    simp [standardBasis]
  calc
    |M i j| = ‖matrixLinearEquiv m n M (standardBasis n j) i‖ := by
      rw [matrix_column, Real.norm_eq_abs]
    _ ≤ ‖matrixLinearEquiv m n M (standardBasis n j)‖ := PiLp.norm_apply_le _ _
    _ ≤ linearOperatorNorm (matrixLinearEquiv m n M) * ‖standardBasis n j‖ :=
      linear_apply_bound _ _
    _ = linearOperatorNorm (matrixLinearEquiv m n M) := by rw [hn, mul_one]

theorem matrix_max_le_operator {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖ ≤
      linearOperatorNorm (matrixLinearEquiv m n M) := by
  apply (pi_norm_le_iff_of_nonneg (linear_norm_finite _).2).mpr
  intro ij
  exact matrix_entry_bound M ij.1 ij.2

theorem matrix_operator_le_frobenius {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    linearOperatorNorm (matrixLinearEquiv m n M) ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) := by
  rw [linear_norm_bridge]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ ∑ i, ∑ j, M i j ^ 2 from
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  change ‖matrixLinearEquiv m n M v‖ ^ 2 ≤ _
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    (∑ i, (matrixLinearEquiv m n M v i) ^ 2) ≤
        ∑ i, (∑ j, M i j ^ 2) * (∑ j, v j ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrix_apply]
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (M i) (fun j => v j)
    _ = (∑ i, ∑ j, M i j ^ 2) * ‖v‖ ^ 2 := by
      rw [← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq]

theorem matrix_frobenius_le_max {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤
      Real.sqrt ((m : ℝ) * (n : ℝ)) * ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖ := by
  let C := ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖
  have hC : 0 ≤ C := norm_nonneg _
  calc
    Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤ Real.sqrt (∑ _i : Fin m, ∑ _j : Fin n, C ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hb : |M i j| ≤ C := norm_le_pi_norm (fun ij : Fin m × Fin n => M ij.1 ij.2) (i,j)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr hb
    _ = Real.sqrt ((m : ℝ) * (n : ℝ) * C ^ 2) := by congr 1; simp; ring
    _ = Real.sqrt ((m : ℝ) * (n : ℝ)) * C := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC]


/-- The maximum here is the ordinary finite maximum of absolute entries.
The empty maximum is zero, so the stronger statement includes empty matrices. -/
theorem matrix_operator_bounds {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖ ≤
        linearOperatorNorm (matrixLinearEquiv m n M) ∧
      linearOperatorNorm (matrixLinearEquiv m n M) ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) ∧
      Real.sqrt (∑ i, ∑ j, M i j ^ 2) ≤
        Real.sqrt ((m : ℝ) * (n : ℝ)) * ‖fun ij : Fin m × Fin n => M ij.1 ij.2‖ :=
  ⟨matrix_max_le_operator M, matrix_operator_le_frobenius M, matrix_frobenius_le_max M⟩

theorem linear_operator_zero_dimensions {n m : ℕ} (A : E n →ₗ[ℝ] E m)
    (h : n = 0 ∨ m = 0) : linearOperatorNorm A = 0 := by
  rcases h with rfl | rfl
  · exact linearOperatorNorm_from_zero A
  · rw [linearMap_to_zero A, linear_norm_bridge]
    exact norm_zero

theorem multilinear_operator_zero_codomain {n k : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin k => E n) (E 0)) :
    multilinearOperatorNorm T = 0 := by
  have he : T = 0 := by ext v i; exact Fin.elim0 i
  rw [he, multilinear_norm_bridge]
  exact norm_zero

theorem multilinear_operator_zero_domain {m k : ℕ} (hk : 0 < k)
    (T : MultilinearMap ℝ (fun _ : Fin k => E 0) (E m)) :
    multilinearOperatorNorm T = 0 :=
  multilinearOperatorNorm_from_zero hk T

/-- An order-zero tensor still has its value as coefficients, even when n = 0. -/
theorem multilinear_order_zero_equality {n m : ℕ}
    (T : MultilinearMap ℝ (fun _ : Fin 0 => E n) (E m)) (v : Fin 0 → E n) :
    ‖T v‖ = multilinearOperatorNorm T * ∏ i, ‖v i‖ := by
  rw [multilinearOperatorNorm_order_zero]
  have hv : v = (fun i => Fin.elim0 i) := Subsingleton.elim _ _
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, hv]

end D04
