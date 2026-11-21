import MathGenome.Internal.Specs.D05.M14.EigenvalueFrobeniusBound
import MathGenome.Internal.D05.M08.Charpoly
import MathGenome.Internal.D05.M13.Normal
import MathGenome.Internal.D05.M13.Schur
import MathGenome.Internal.D05.M13.ComplexSpectral
import MathGenome.Internal.D05.M14.Frobenius

noncomputable section
namespace D05.M14.EigenvalueFrobeniusBound
open scoped BigOperators
open Polynomial

/-- The root multiset of a triangular matrix is its diagonal, with repetition. -/
theorem roots_upper_triangular {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsUpperTriangular) :
    B.charpoly.roots = Finset.univ.val.map (fun i => B i i) := by
  rw [Matrix.charpoly_of_isUpperTriangular B hB,
    Polynomial.roots_prod _ _ (Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _))]
  simp only [roots_X_sub_C, Multiset.bind_singleton]

/-- Consequently summing any function of the roots sums that function on the diagonal. -/
theorem sum_roots_upper_triangular {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.IsUpperTriangular) :
    (B.charpoly.roots.map (fun z : ℂ => ‖z‖ ^ 2)).sum = ∑ i, ‖B i i‖ ^ 2 := by
  rw [roots_upper_triangular B hB, Multiset.map_map]
  rfl

/-- Discarding off-diagonal squared norms can only decrease the sum. -/
theorem diagonal_sum_le {I : Type*} [Fintype I] (B : Matrix I I ℂ) :
    (∑ i, ‖B i i‖ ^ 2) ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  classical
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (fun j _ => sq_nonneg ‖B i j‖) (Finset.mem_univ i)

/-- Equality in the discarded-term inequality annihilates each off-diagonal entry. -/
theorem off_diagonal_zero {I : Type*} [Fintype I] (B : Matrix I I ℂ)
    (h : (∑ i, ‖B i i‖ ^ 2) = ∑ i, ∑ j, ‖B i j‖ ^ 2) :
    ∀ i j, i ≠ j → B i j = 0 := by
  classical
  have hi (i : I) : ‖B i i‖ ^ 2 = ∑ j, ‖B i j‖ ^ 2 :=
    (Finset.sum_eq_sum_iff_of_le (fun i _ =>
      Finset.single_le_sum (fun j _ => sq_nonneg ‖B i j‖) (Finset.mem_univ i))).mp h i
        (Finset.mem_univ i)
  intro i j hij
  have hr : (∑ k ∈ Finset.univ.erase i, ‖B i k‖ ^ 2) = 0 := by
    have hh := Finset.sum_erase_add Finset.univ (fun k => ‖B i k‖ ^ 2)
      (Finset.mem_univ i)
    linarith [hi i]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖B i k‖)).mp hr
    j (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)
  simpa using hz


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The coordinate equation of an eigenbasis is exactly a diagonal matrix. -/
theorem matrix_eq_diagonal {n : ℕ} (T : Module.End ℂ V)
    (e : OrthonormalBasis (Fin n) ℂ V) (μ : Fin n → ℂ)
    (hμ : ∀ j, T (e j) = μ j • e j) :
    LinearMap.toMatrix e.toBasis e.toBasis T = Matrix.diagonal μ := by
  classical
  ext i j
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    hμ, inner_smul_right]
  rw [orthonormal_iff_ite.mp e.orthonormal]
  by_cases h : i = j <;> simp [Matrix.diagonal, h]

/-- Vanishing off-diagonal coordinates makes each basis vector an eigenvector. -/
theorem eigenvectors_of_off_diagonal {n : ℕ} (T : Module.End ℂ V)
    (e : OrthonormalBasis (Fin n) ℂ V)
    (h : ∀ i j, i ≠ j → LinearMap.toMatrix e.toBasis e.toBasis T i j = 0) :
    ∀ j, T (e j) = LinearMap.toMatrix e.toBasis e.toBasis T j j • e j := by
  classical
  intro j
  apply e.toBasis.repr.injective
  ext i
  change e.toBasis.repr (T (e.toBasis j)) i = _
  rw [← LinearMap.toMatrix_apply e.toBasis e.toBasis T i j]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  change LinearMap.toMatrix e.toBasis e.toBasis T i j =
    LinearMap.toMatrix e.toBasis e.toBasis T j j * e.toBasis.repr (e.toBasis j) i
  rw [e.toBasis.repr_self]
  by_cases hij : i = j
  · subst i; simp
  · simp [hij, h i j hij]

variable [FiniteDimensional ℂ V]

/-- The upstream spectral criterion applies to any finite orthonormal eigenbasis. -/
theorem normal_of_eigenbasis {n : ℕ} (T : Module.End ℂ V)
    (e : OrthonormalBasis (Fin n) ℂ V) (μ : Fin n → ℂ)
    (hμ : ∀ j, T (e j) = μ j • e j) : D05.normalOperator T := by
  have hn : Module.finrank ℂ V = n := by
    simpa using Module.finrank_eq_card_basis e.toBasis
  subst n
  exact D05.M13.ComplexSpectral.orthonormal_eigenbasis_normal T e.toBasis
    ((D05.M12.Orthonormal.orthonormal_iff_mathlib _).mpr e.orthonormal) ⟨μ, hμ⟩

/-- A version with explicit coordinate instances, bridged by the entry formula. -/
theorem frobenius_matrix {n : ℕ} (T : Module.End ℂ V)
    (e : OrthonormalBasis (Fin n) ℂ V) :
    D05.frobeniusNorm T ^ 2 =
      ∑ i, ∑ j, ‖LinearMap.toMatrix e.toBasis e.toBasis T i j‖ ^ 2 := by
  simpa only [LinearMap.toMatrix_apply] using D05.M14.Frobenius.matrix_formula T e e

theorem operator_bound : Specs.D05.M14.EigenvalueFrobeniusBound.operator_bound := by
  intro V _ _ _ T
  classical
  obtain ⟨n, e, he⟩ := D05.M13.Schur.schur T
  rw [← LinearMap.charpoly_toMatrix T e.toBasis, sum_roots_upper_triangular _ he,
    frobenius_matrix T e]
  exact diagonal_sum_le (LinearMap.toMatrix e.toBasis e.toBasis T)

theorem operator_equality_iff :
    Specs.D05.M14.EigenvalueFrobeniusBound.operator_equality_iff := by
  intro V _ _ _ T
  classical
  constructor
  · intro heq
    obtain ⟨n, e, he⟩ := D05.M13.Schur.schur T
    rw [← LinearMap.charpoly_toMatrix T e.toBasis, sum_roots_upper_triangular _ he,
      frobenius_matrix T e] at heq
    exact normal_of_eigenbasis T e _
      (eigenvectors_of_off_diagonal T e (off_diagonal_zero _ heq))
  · intro hn
    obtain ⟨e, μ, hμ⟩ := D05.M13.ComplexSpectral.exists_orthonormalBasis T hn
    have hB := matrix_eq_diagonal T e μ hμ
    rw [← LinearMap.charpoly_toMatrix T e.toBasis, hB,
      sum_roots_upper_triangular _ (Matrix.blockTriangular_diagonal μ),
      D05.M14.Frobenius.squared_basis_sum T e]
    simp [hμ, norm_smul, e.orthonormal.norm_eq_one]

/-- The usual matrix and its action on standard Euclidean space have the same charpoly. -/
theorem charpoly_euclidean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A.toEuclideanLin.charpoly = A.charpoly := by
  exact Matrix.charpoly_toLin A (EuclideanSpace.basisFun (Fin n) ℂ).toBasis

/-- The canonical Frobenius norm specializes to the entrywise squared norm. -/
theorem frobenius_euclidean {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    D05.frobeniusNorm A.toEuclideanLin ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [frobenius_matrix A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) ℂ)]
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis A.toEuclideanLin = A :=
    LinearMap.toMatrix_toLin _ _ A
  rw [hm]

theorem normal_euclidean_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    D05.normalOperator A.toEuclideanLin ↔ A * A.conjTranspose = A.conjTranspose * A := by
  unfold D05.normalOperator
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  constructor
  · intro h
    apply Matrix.toEuclideanLin.injective
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h
  · intro h
    have hh := congrArg Matrix.toEuclideanLin h
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using hh

theorem matrix_bound : Specs.D05.M14.EigenvalueFrobeniusBound.matrix_bound := by
  intro n A
  simpa only [charpoly_euclidean, frobenius_euclidean] using operator_bound A.toEuclideanLin

theorem matrix_equality_iff : Specs.D05.M14.EigenvalueFrobeniusBound.matrix_equality_iff := by
  intro n A
  simpa only [charpoly_euclidean, frobenius_euclidean, normal_euclidean_iff] using
    operator_equality_iff A.toEuclideanLin

theorem listed_eigenvalues : Specs.D05.M14.EigenvalueFrobeniusBound.listed_eigenvalues := by
  intro n A μ hμ
  have hs : (A.charpoly.roots.map (fun z : ℂ => ‖z‖ ^ 2)).sum = ∑ i, ‖μ i‖ ^ 2 := by
    rw [← hμ]
    simp only [Multiset.map_coe, Multiset.sum_coe]
    rw [← List.ofFn_comp', List.sum_ofFn]
  exact ⟨hs ▸ matrix_bound A, hs ▸ matrix_equality_iff A⟩

theorem exists_list_of_card (n : ℕ) (s : Multiset ℂ) (h : s.card = n) :
    ∃ μ : Fin n → ℂ, (List.ofFn μ : Multiset ℂ) = s := by
  rcases s with ⟨l⟩
  change l.length = n at h
  subst n
  exact ⟨l.get, congrArg (fun l : List ℂ => (l : Multiset ℂ)) (List.ofFn_get l)⟩

theorem exists_eigenvalue_list : Specs.D05.M14.EigenvalueFrobeniusBound.exists_eigenvalue_list := by
  intro n A
  apply exists_list_of_card n A.charpoly.roots
  rw [← (D05.Foundations.Fta.splits A.charpoly).natDegree_eq_card_roots,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end D05.M14.EigenvalueFrobeniusBound
