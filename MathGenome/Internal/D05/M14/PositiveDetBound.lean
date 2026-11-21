import MathGenome.Internal.Specs.D05.M14.PositiveDetBound
import MathGenome.Internal.D05.M14.PositiveRoot
import MathGenome.Internal.D05.M05.Hadamard
import MathGenome.Internal.D05.M05.DetProduct

noncomputable section
open scoped BigOperators

namespace D05.M14.PositiveDetBound

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V] {n : ℕ}

/-- The coordinate columns are actual Euclidean vectors, with the same norms. -/
theorem coordinate_column_matrix (S : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V) :
    D05.M05.Hadamard.columnMatrix (fun i => e.repr (S (e i))) =
      S.toMatrix e.toBasis e.toBasis := by
  ext i j
  simp [D05.M05.Hadamard.columnMatrix, LinearMap.toMatrix_apply]

/-- Determinant of a Gram operator, including singular maps and empty matrices. -/
theorem det_adjoint_mul (S : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V) :
    LinearMap.det ((LinearMap.adjoint S) * S) = (‖LinearMap.det S‖ ^ 2 : ℝ) := by
  rw [← LinearMap.det_toMatrix e.toBasis,
    LinearMap.toMatrix_mul e.toBasis, LinearMap.toMatrix_adjoint e e,
    Matrix.det_mul, Matrix.det_conjTranspose, LinearMap.det_toMatrix]
  simpa only [RCLike.ofReal_pow, RCLike.star_def] using (RCLike.conj_mul (LinearMap.det S))

/-- Pulling the first-slot inner product through the positive square root. -/
theorem root_gram (T S : V →ₗ[F] V) (hS : D05.positiveSemidefinite S)
    (hsq : S ^ 2 = T) (x y : V) :
    D05.firstInner (F := F) (S x) (S y) = D05.firstInner (F := F) (T x) y := by
  have hself : S = LinearMap.adjoint S := hS.1
  change inner F (S y) (S x) = inner F y (T x)
  rw [← LinearMap.adjoint_inner_right, ← hself]
  congr 1
  exact congrArg (fun R : Module.End F V => R x) hsq

/-- Norm squares equal the source's diagonal values. -/
theorem root_diagonal (T S : V →ₗ[F] V) (hS : D05.positiveSemidefinite S)
    (hsq : S ^ 2 = T) (x : V) :
    D05.firstInner (F := F) (T x) x = (‖S x‖ ^ 2 : ℝ) := by
  rw [← root_gram T S hS hsq x x]
  simpa only [D05.firstInner, RCLike.ofReal_pow] using
    (inner_self_eq_norm_sq_to_K (𝕜 := F) (S x))

theorem root_det (T S : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V)
    (hS : D05.positiveSemidefinite S) (hsq : S ^ 2 = T) :
    LinearMap.det T = (‖LinearMap.det S‖ ^ 2 : ℝ) := by
  have hT : (LinearMap.adjoint S) * S = T := by
    rw [← hS.1, ← pow_two, hsq]
  rw [← hT]
  exact det_adjoint_mul S e

theorem real_values : Specs.D05.M14.PositiveDetBound.real_values := by
  intro F V _ _ _ _ n T e hT
  obtain ⟨S, hS, hsq⟩ := D05.M14.PositiveRoot.exists_positive_root T hT
  rw [root_det T S e hS hsq, RCLike.ofReal_re]
  refine ⟨rfl, sq_nonneg _, fun i => ?_⟩
  rw [root_diagonal T S hS hsq, RCLike.ofReal_re]

/-- Hadamard on the actual coordinates of S in the given basis. -/
theorem root_hadamard (S : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V) :
    ‖LinearMap.det S‖ ≤ ∏ i, ‖S (e i)‖ := by
  have hh := D05.M05.Hadamard.inequality (fun i => e.repr (S (e i)))
  rw [coordinate_column_matrix, D05.M05.DetDefinition.matrix_det_bridge,
    LinearMap.det_toMatrix] at hh
  simpa only [e.repr.norm_map] using hh

theorem inequality : Specs.D05.M14.PositiveDetBound.inequality := by
  intro F V _ _ _ _ n T e hT
  obtain ⟨S, hS, hsq⟩ := D05.M14.PositiveRoot.exists_positive_root T hT
  rw [root_det T S e hS hsq, RCLike.ofReal_re]
  simp_rw [root_diagonal T S hS hsq, RCLike.ofReal_re]
  rw [Finset.prod_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg _))).mpr
    (root_hadamard S e)

open scoped ComplexOrder in
/-- The displayed scalar inequality, with the real order on real values. -/
theorem scalar_inequality : Specs.D05.M14.PositiveDetBound.scalar_inequality := by
  intro F V _ _ _ _ n T e hT
  obtain ⟨hd, _, he⟩ := real_values T e hT
  calc
    LinearMap.det T = (RCLike.re (LinearMap.det T) : F) := hd.symm
    _ ≤ ((∏ i, RCLike.re (D05.firstInner (F := F) (T (e i)) (e i)) : ℝ) : F) :=
      RCLike.ofReal_le_ofReal.mpr (inequality T e hT)
    _ = ∏ i, D05.firstInner (F := F) (T (e i)) (e i) := by
      rw [RCLike.ofReal_prod]
      exact Finset.prod_congr rfl (fun i _ => he i)

/-- Vanishing off the diagonal is exactly the eigenbasis condition. -/
theorem off_diagonal_iff_eigenbasis (T : V →ₗ[F] V)
    (e : OrthonormalBasis (Fin n) F V) :
    (∀ i j, i ≠ j → D05.firstInner (F := F) (T (e i)) (e j) = 0) ↔
      ∀ i, ∃ μ : F, T (e i) = μ • e i := by
  classical
  constructor
  · intro h i
    refine ⟨e.repr (T (e i)) i, ?_⟩
    conv_lhs => rw [← e.sum_repr (T (e i))]
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hz : e.repr (T (e i)) j = 0 := by
        rw [e.repr_apply_apply]
        exact h i j (Ne.symm hji)
      rw [hz, zero_smul]
    · simp
  · intro h i j hij
    obtain ⟨μ, hμ⟩ := h i
    rw [hμ]
    change inner F (e j) (μ • e i) = 0
    rw [inner_smul_right, e.inner_eq_zero (Ne.symm hij), mul_zero]

/-- Equality of the two squared products is equality in Hadamard. -/
theorem root_equality_iff (T S : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V)
    (hS : D05.positiveSemidefinite S) (hsq : S ^ 2 = T)
    (hne : ∀ i, S (e i) ≠ 0) :
    (RCLike.re (LinearMap.det T) =
      ∏ i, RCLike.re (D05.firstInner (F := F) (T (e i)) (e i))) ↔
      ∀ i, ∃ μ : F, T (e i) = μ • e i := by
  have heq : (RCLike.re (LinearMap.det T) =
      ∏ i, RCLike.re (D05.firstInner (F := F) (T (e i)) (e i))) ↔
      ‖LinearMap.det S‖ = ∏ i, ‖S (e i)‖ := by
    rw [root_det T S e hS hsq, RCLike.ofReal_re]
    simp_rw [root_diagonal T S hS hsq, RCLike.ofReal_re]
    rw [Finset.prod_pow]
    exact sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  have hh := D05.M05.Hadamard.equality_nonzero (fun i => e.repr (S (e i)))
    (fun i hz => hne i (e.repr.injective (hz.trans (e.repr.map_zero.symm))))
  have hh' : (‖LinearMap.det S‖ = ∏ i, ‖S (e i)‖) ↔
      D05.orthogonalFamily (F := F) (fun i => S (e i)) := by
    rw [coordinate_column_matrix, D05.M05.DetDefinition.matrix_det_bridge,
      LinearMap.det_toMatrix] at hh
    simpa only [e.repr.norm_map, D05.orthogonalFamily,
      D05.firstInner, e.repr.inner_map_map] using hh
  rw [heq, hh']
  change (∀ i j, i ≠ j → D05.firstInner (F := F) (S (e i)) (S (e j)) = 0) ↔ _
  simp_rw [root_gram T S hS hsq]
  exact off_diagonal_iff_eigenbasis T e

theorem equality_iff_eigenbasis :
    Specs.D05.M14.PositiveDetBound.equality_iff_eigenbasis := by
  intro F V _ _ _ _ n T e hT
  have hp := D05.M14.Positive.positiveDefinite_implies_semidefinite T hT
  obtain ⟨S, hS, hsq⟩ := D05.M14.PositiveRoot.exists_positive_root T hp
  apply root_equality_iff T S e hS hsq
  intro i hz
  have hd := hT.2 (e i) (e.toBasis.ne_zero i)
  simp [root_diagonal T S hS hsq, hz] at hd

theorem scalar_equality_iff_eigenbasis :
    Specs.D05.M14.PositiveDetBound.scalar_equality_iff_eigenbasis := by
  intro F V _ _ _ _ n T e hT
  have hp := D05.M14.Positive.positiveDefinite_implies_semidefinite T hT
  obtain ⟨hd, _, he⟩ := real_values T e hp
  have hr : LinearMap.det T = ∏ i, D05.firstInner (F := F) (T (e i)) (e i) ↔
      RCLike.re (LinearMap.det T) =
        ∏ i, RCLike.re (D05.firstInner (F := F) (T (e i)) (e i)) := by
    have hprod : ((∏ i, RCLike.re (D05.firstInner (F := F) (T (e i)) (e i)) : ℝ) : F) =
        ∏ i, D05.firstInner (F := F) (T (e i)) (e i) := by
      rw [RCLike.ofReal_prod]
      exact Finset.prod_congr rfl (fun i _ => he i)
    constructor
    · intro h
      exact RCLike.ofReal_injective (hd.trans (h.trans hprod.symm))
    · intro h
      exact hd.symm.trans ((congrArg (fun r : ℝ => (r : F)) h).trans hprod)
  rw [hr]
  exact equality_iff_eigenbasis T e hT

theorem empty_case : Specs.D05.M14.PositiveDetBound.empty_case := by
  intro F V _ _ _ _ T e
  constructor
  · rw [← LinearMap.det_toMatrix e.toBasis]
    exact Matrix.det_isEmpty
  · simp

end D05.M14.PositiveDetBound
