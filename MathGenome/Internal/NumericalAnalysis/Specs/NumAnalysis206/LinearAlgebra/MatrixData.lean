import MathGenome.Internal.Specs.D05.M14.QrCholesky.Qr
import MathGenome.Internal.Specs.D05.M14.Frobenius
import MathGenome.Internal.Specs.D05.M14.Pseudoinverse
import MathGenome.Internal.Specs.D05.M14.LowRank.Truncation
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.DirectSum.Decomposition

/-! Canonical objects for P206, chapters 4–5. Dimensions are natural numbers,
including zero. Algebraic elimination predicates impose no analytic scalar
structure. Analytic matrices act on `EuclideanSpace`, not on the sup-norm Pi space.
Singular indices in the manuscript start at one; Hermitian indices below are
`Fin n`, in increasing order. No numerical execution or error certificate is
part of these definitions. -/
noncomputable section
open scoped BigOperators ENNReal DirectSum

namespace NumAnalysis206.MatrixDefinitions

abbrev Mat (K : Type*) (m n : ℕ) := Matrix (Fin m) (Fin n) K
abbrev Vec (K : Type*) [RCLike K] (n : ℕ) := EuclideanSpace K (Fin n)

/-- A permutation matrix over any field, with row i selecting coordinate p i. -/
def IsPermutation {K : Type*} [Field K] {n : ℕ} (P : Mat K n n) : Prop :=
  ∃ p : Equiv.Perm (Fin n), P = fun i j => if j = p i then 1 else 0

def IsLowerTriangular {K : Type*} [Zero K] {m n : ℕ} (A : Mat K m n) : Prop :=
  ∀ i j, i.val < j.val → A i j = 0

def IsUpperTriangular {K : Type*} [Zero K] {m n : ℕ} (A : Mat K m n) : Prop :=
  ∀ i j, j.val < i.val → A i j = 0

def IsUnitLowerTriangular {K : Type*} [Zero K] [One K] {n : ℕ}
    (A : Mat K n n) : Prop := IsLowerTriangular A ∧ ∀ i, A i i = 1

/-- Nonzero rows precede zero rows, and their first nonzero columns strictly
increase. This allows skipped columns and imposes no normalization of pivots. -/
def IsRowEchelon {K : Type*} [Zero K] {m n : ℕ} (A : Mat K m n) : Prop :=
  ∃ (r : ℕ) (hr : r ≤ m) (p : Fin r → Fin n),
    StrictMono p ∧
    (∀ i, A (Fin.castLE hr i) (p i) ≠ 0 ∧
      ∀ j, j < p i → A (Fin.castLE hr i) j = 0) ∧
    ∀ i, r ≤ i.val → ∀ j, A i j = 0

section Analytic
variable {K : Type*} [RCLike K] {m n : ℕ}

def adjoint (A : Mat K m n) : Mat K n m := A.conjTranspose

def entrywiseAbs (A : Mat K m n) : Mat ℝ m n := fun i j => ‖A i j‖

/-- Inequalities are entrywise; any product of the absolute-value matrices is
ordinary real matrix multiplication. -/
def EntrywiseLE (A B : Mat ℝ m n) : Prop := ∀ i j, A i j ≤ B i j

abbrev toEuclidean (A : Mat K m n) := A.toEuclideanLin

def operatorNorm (A : Mat K m n) : ℝ := ‖A.toEuclideanLin.toContinuousLinearMap‖

def frobeniusNorm (A : Mat K m n) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

abbrev columns (A : Mat K m n) := D05.QrCholesky.columns A
abbrev FullColumnRank (A : Mat K m n) : Prop := D05.QrCholesky.FullColumnRank A
abbrev ReducedQR (A Q : Mat K m n) (R : Mat K n n) : Prop :=
  D05.QrCholesky.ReducedQR A Q R

def PositiveRealDiagonal (A : Mat K n n) : Prop :=
  ∀ i, ∃ r : ℝ, 0 < r ∧ A i i = (r : K)

def NonnegativeRealDiagonal (A : Mat K n n) : Prop :=
  ∀ i, ∃ r : ℝ, 0 ≤ r ∧ A i i = (r : K)

/-- The row normalization required in W25, in addition to triangularity. -/
def SemidefiniteCholeskyNormalization (R : Mat K n n) : Prop :=
  IsUpperTriangular R ∧ NonnegativeRealDiagonal R ∧
    ∀ i, R i i = 0 → ∀ j, R i j = 0

/-- For i > 0 this is sigma_i. The unused index zero is assigned sigma_1. -/
def singularValue (A : Mat K m n) (i : ℕ) : ℝ :=
  A.toEuclideanLin.singularValues (i - 1)

def rank (A : Mat K m n) : ℕ := Module.finrank K A.toEuclideanLin.range

/-- The canonical Moore–Penrose map, transported back to a matrix. Its SVD
positive-term formula is a theorem, not an assumed part of this definition. -/
def pseudoinverse (A : Mat K m n) : Mat K n m :=
  Matrix.toEuclideanLin.symm (D05.pseudoinverse A.toEuclideanLin)

/-- Any full SVD may be used; the retained block has length min(k, rank A). -/
def svdTruncation (A : Mat K m n) (d : D05.SingularValueDecomposition A.toEuclideanLin)
    (k : ℕ) : Mat K m n :=
  Matrix.toEuclideanLin.symm (D05.svdTruncation A.toEuclideanLin d k)

/-- Eigenvalues of a Hermitian matrix in the source's increasing order. -/
def eigenvalue (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n) : ℝ :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
    (finrank_euclideanSpace_fin (𝕜 := K)) i.rev

def eigenbasis (A : Mat K n n) (hA : A.IsHermitian) :
    OrthonormalBasis (Fin n) K (Vec K n) :=
  ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := K))).reindex Fin.revPerm

/-- The real Rayleigh value, including on non-unit vectors. -/
def rayleigh (A : Mat K n n) (x : Vec K n) : ℝ :=
  RCLike.re (inner K x (A.toEuclideanLin x))

/-- Select eigenvalues, not particular basis indices: repeated eigenvalues
contribute their complete eigenspaces. -/
def spectralSubspace (A : Mat K n n) (s : Set ℝ) : Submodule K (Vec K n) :=
  ⨆ μ : s, Module.End.eigenspace A.toEuclideanLin (μ.val : K)

def spectralProjection (A : Mat K n n) (_hA : A.IsHermitian) (s : Set ℝ) :
    Vec K n →L[K] Vec K n :=
  (spectralSubspace A s).starProjection

/-- Hermitian dilation on the left-plus-right coordinate space (W43). -/
def hermitianDilation (A : Mat K m n) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) K :=
  Matrix.fromBlocks 0 A A.conjTranspose 0
end Analytic

/-- Algebraic diagonalizability over the specified field: the full eigenspaces
span the space. Independence of distinct eigenspaces gives the internal direct sum. -/
def IsDiagonalizable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) : Prop := (⨆ μ : K, T.eigenspace μ) = ⊤

/-- Canonical algebraic eigenspace decomposition, without choosing individual
vectors inside a repeated eigenspace. -/
def eigenspaceDecomposition {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (hT : IsDiagonalizable T) :
    V ≃ₗ[K] ⨁ μ : K, T.eigenspace μ := by
  classical
  exact (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun μ : K => T.eigenspace μ))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      T.eigenspaces_iSupIndep hT)).symm

def spectralComponent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (hT : IsDiagonalizable T) (μ : K) : V →ₗ[K] V := by
  classical
  exact (T.eigenspace μ).subtype.comp
    ((DirectSum.component K K (fun ν : K => T.eigenspace ν) μ).comp
      (eigenspaceDecomposition T hT).toLinearMap)

/-- The actual subordinate norm for an arbitrary normed finite-dimensional
coordinate space. Choosing another vector norm means choosing that space's
normed structure and coordinate basis. -/
def subordinateNorm {K E F : Type*} [RCLike K]
    [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
    [NormedAddCommGroup F] [NormedSpace K F]
    {m n : ℕ} (b : Module.Basis (Fin n) K E) (c : Module.Basis (Fin m) K F)
    (A : Mat K m n) : ℝ :=
  ‖(Matrix.toLin b c A).toContinuousLinearMap‖

/-- Finite ell_p vector norms, including p = infinity. -/
def lpVectorNorm {K : Type*} [RCLike K] {n : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (x : Fin n → K) : ℝ :=
  letI : Fact (1 ≤ p) := ⟨hp⟩
  ‖WithLp.toLp p x‖

def lpOperatorNorm {K : Type*} [RCLike K] {m n : ℕ}
    (p : ℝ≥0∞) (hp : 1 ≤ p) (A : Mat K m n) : ℝ :=
  letI : Fact (1 ≤ p) := ⟨hp⟩
  ‖(Matrix.toLpLin p p A).toContinuousLinearMap‖

end NumAnalysis206.MatrixDefinitions

namespace Specs.NumAnalysis206.MatrixData
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open _root_.NumAnalysis206.MatrixDefinitions
universe u v w

def Mat_type := (K : Type u) → ℕ → ℕ → Type u
def Mat_value : Mat_type := @_root_.NumAnalysis206.MatrixDefinitions.Mat

def Vec_type := (K : Type u) → [RCLike K] → ℕ → Type u
def Vec_value : Vec_type := @_root_.NumAnalysis206.MatrixDefinitions.Vec

def IsPermutation_type := ∀ {K : Type u} [Field K] {n : ℕ} (P : Mat K n n), Prop
def IsPermutation_value : IsPermutation_type := @_root_.NumAnalysis206.MatrixDefinitions.IsPermutation

def IsLowerTriangular_type := ∀ {K : Type u} [Zero K] {m n : ℕ} (A : Mat K m n), Prop
def IsLowerTriangular_value : IsLowerTriangular_type := @_root_.NumAnalysis206.MatrixDefinitions.IsLowerTriangular

def IsUpperTriangular_type := ∀ {K : Type u} [Zero K] {m n : ℕ} (A : Mat K m n), Prop
def IsUpperTriangular_value : IsUpperTriangular_type := @_root_.NumAnalysis206.MatrixDefinitions.IsUpperTriangular

def IsUnitLowerTriangular_type := ∀ {K : Type u} [Zero K] [One K] {n : ℕ} (A : Mat K n n), Prop
def IsUnitLowerTriangular_value : IsUnitLowerTriangular_type := @_root_.NumAnalysis206.MatrixDefinitions.IsUnitLowerTriangular

def IsRowEchelon_type := ∀ {K : Type u} [Zero K] {m n : ℕ} (A : Mat K m n), Prop
def IsRowEchelon_value : IsRowEchelon_type := @_root_.NumAnalysis206.MatrixDefinitions.IsRowEchelon

def adjoint_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Mat K n m
def adjoint_value : adjoint_type := @_root_.NumAnalysis206.MatrixDefinitions.adjoint

def entrywiseAbs_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Mat ℝ m n
def entrywiseAbs_value : entrywiseAbs_type := @_root_.NumAnalysis206.MatrixDefinitions.entrywiseAbs

def EntrywiseLE_type := ∀ {m n : ℕ} (A B : Mat ℝ m n), Prop
def EntrywiseLE_value : EntrywiseLE_type := @_root_.NumAnalysis206.MatrixDefinitions.EntrywiseLE

def operatorNorm_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), ℝ
def operatorNorm_value : operatorNorm_type := @_root_.NumAnalysis206.MatrixDefinitions.operatorNorm

def frobeniusNorm_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), ℝ
def frobeniusNorm_value : frobeniusNorm_type := @_root_.NumAnalysis206.MatrixDefinitions.frobeniusNorm

def columns_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Fin n → Vec K m
def columns_value : columns_type := fun {K} _ {m n} => @_root_.NumAnalysis206.MatrixDefinitions.columns K m n

def FullColumnRank_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Prop
def FullColumnRank_value : FullColumnRank_type := @_root_.NumAnalysis206.MatrixDefinitions.FullColumnRank

def ReducedQR_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A Q : Mat K m n) (R : Mat K n n), Prop
def ReducedQR_value : ReducedQR_type := @_root_.NumAnalysis206.MatrixDefinitions.ReducedQR

def PositiveRealDiagonal_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n), Prop
def PositiveRealDiagonal_value : PositiveRealDiagonal_type := @_root_.NumAnalysis206.MatrixDefinitions.PositiveRealDiagonal

def NonnegativeRealDiagonal_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n), Prop
def NonnegativeRealDiagonal_value : NonnegativeRealDiagonal_type := @_root_.NumAnalysis206.MatrixDefinitions.NonnegativeRealDiagonal

def SemidefiniteCholeskyNormalization_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (R : Mat K n n), Prop
def SemidefiniteCholeskyNormalization_value : SemidefiniteCholeskyNormalization_type := @_root_.NumAnalysis206.MatrixDefinitions.SemidefiniteCholeskyNormalization

def singularValue_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (i : ℕ), ℝ
def singularValue_value : singularValue_type := @_root_.NumAnalysis206.MatrixDefinitions.singularValue

def rank_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), ℕ
def rank_value : rank_type := @_root_.NumAnalysis206.MatrixDefinitions.rank

def pseudoinverse_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Mat K n m
def pseudoinverse_value : pseudoinverse_type := @_root_.NumAnalysis206.MatrixDefinitions.pseudoinverse

def svdTruncation_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (d : D05.SingularValueDecomposition A.toEuclideanLin) (k : ℕ), Mat K m n
def svdTruncation_value : svdTruncation_type := @_root_.NumAnalysis206.MatrixDefinitions.svdTruncation

def eigenvalue_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n), ℝ
def eigenvalue_value : eigenvalue_type := @_root_.NumAnalysis206.MatrixDefinitions.eigenvalue

def eigenbasis_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian), OrthonormalBasis (Fin n) K (Vec K n)
def eigenbasis_value : eigenbasis_type := @_root_.NumAnalysis206.MatrixDefinitions.eigenbasis

def rayleigh_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (x : Vec K n), ℝ
def rayleigh_value : rayleigh_type := @_root_.NumAnalysis206.MatrixDefinitions.rayleigh

def spectralSubspace_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (s : Set ℝ), Submodule K (Vec K n)
def spectralSubspace_value : spectralSubspace_type := @_root_.NumAnalysis206.MatrixDefinitions.spectralSubspace

def spectralProjection_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian) (s : Set ℝ), Vec K n →L[K] Vec K n
def spectralProjection_value : spectralProjection_type := @_root_.NumAnalysis206.MatrixDefinitions.spectralProjection

def hermitianDilation_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) K
def hermitianDilation_value : hermitianDilation_type := @_root_.NumAnalysis206.MatrixDefinitions.hermitianDilation

def IsDiagonalizable_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) , Prop
def IsDiagonalizable_value : IsDiagonalizable_type := @_root_.NumAnalysis206.MatrixDefinitions.IsDiagonalizable

def eigenspaceDecomposition_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (hT : IsDiagonalizable T), V ≃ₗ[K] ⨁ μ : K, T.eigenspace μ
def eigenspaceDecomposition_value : eigenspaceDecomposition_type := @_root_.NumAnalysis206.MatrixDefinitions.eigenspaceDecomposition

def spectralComponent_type := ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (hT : IsDiagonalizable T) (μ : K), V →ₗ[K] V
def spectralComponent_value : spectralComponent_type := @_root_.NumAnalysis206.MatrixDefinitions.spectralComponent

def subordinateNorm_type := ∀ {K : Type u} {E : Type v} {F : Type w} [RCLike K]
    [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
    [NormedAddCommGroup F] [NormedSpace K F] {m n : ℕ}
    (b : Module.Basis (Fin n) K E) (c : Module.Basis (Fin m) K F) (A : Mat K m n), ℝ
def subordinateNorm_value : subordinateNorm_type := @_root_.NumAnalysis206.MatrixDefinitions.subordinateNorm

def lpVectorNorm_type := ∀ {K : Type u} [RCLike K] {n : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (x : Fin n → K), ℝ
def lpVectorNorm_value : lpVectorNorm_type := @_root_.NumAnalysis206.MatrixDefinitions.lpVectorNorm

def lpOperatorNorm_type := ∀ {K : Type u} [RCLike K] {m n : ℕ} (p : ℝ≥0∞) (hp : 1 ≤ p) (A : Mat K m n), ℝ
def lpOperatorNorm_value : lpOperatorNorm_type := @_root_.NumAnalysis206.MatrixDefinitions.lpOperatorNorm

end Specs.NumAnalysis206.MatrixData

namespace Specs.NumAnalysis206.MatrixData
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open _root_.NumAnalysis206.MatrixDefinitions
universe u v

def toEuclidean_apply : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (x : Vec K n) (i : Fin m),
  A.toEuclideanLin x i = ∑ j, A i j * x j

def toEuclidean_mul : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} {l : ℕ} (A : Mat K m n) (B : Mat K n l),
  (A * B).toEuclideanLin = A.toEuclideanLin.comp B.toEuclideanLin

def toEuclidean_adjoint : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
  (adjoint A).toEuclideanLin = LinearMap.adjoint A.toEuclideanLin

def rank_eq_matrix_rank : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), rank A = A.rank

def columns_eq_apply_basis : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (j : Fin n),
  columns A j = A.toEuclideanLin (EuclideanSpace.basisFun (Fin n) K j)

def fullColumnRank_iff_injective : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
  FullColumnRank A ↔ Function.Injective A.toEuclideanLin

def operatorNorm_eq_D05 : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), operatorNorm A = D05.operatorNorm A.toEuclideanLin

def frobeniusNorm_sq_columns : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
  frobeniusNorm A ^ 2 = ∑ j, ‖columns A j‖ ^ 2

def frobeniusNorm_eq_D05 : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), frobeniusNorm A = D05.frobeniusNorm A.toEuclideanLin

def frobeniusNorm_sq_basis : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} {ι : Type v} [Fintype ι] (A : Mat K m n)
    (b : OrthonormalBasis ι K (Vec K n)),
  frobeniusNorm A ^ 2 = ∑ j, ‖A.toEuclideanLin (b j)‖ ^ 2

def singularValue_nonneg : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (i : ℕ), 0 ≤ singularValue A i

def singularValue_antitone : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), Antitone (singularValue A)

def singularValue_pos_iff : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (i : ℕ) (hi : 0 < i),
  0 < singularValue A i ↔ i ≤ rank A

def singularValue_zero_of_rank_lt : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (i : ℕ) (hi : rank A < i),
  singularValue A i = 0

def singularValue_zero_of_domain_lt : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (i : ℕ) (hi : n < i),
  singularValue A i = 0

def eigenvalue_monotone : Prop :=
  ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian), Monotone (eigenvalue A hA)

def eigenbasis_action : Prop :=
  ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian) (i : Fin n),
  A.toEuclideanLin (eigenbasis A hA i) = (eigenvalue A hA i : K) • eigenbasis A hA i

def pseudoinverse_transport : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n),
  (pseudoinverse A).toEuclideanLin = D05.pseudoinverse A.toEuclideanLin

def svdTruncation_transport : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (d : D05.SingularValueDecomposition A.toEuclideanLin) (k : ℕ),
  (svdTruncation A d k).toEuclideanLin = D05.svdTruncation A.toEuclideanLin d k

def hermitianDilation_isHermitian : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), (hermitianDilation A).IsHermitian

def spectralComponent_mem : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (hT : IsDiagonalizable T) (μ : K) (x : V),
  spectralComponent T hT μ x ∈ T.eigenspace μ

def eigenspaceDecomposition_recompose : Prop := by
  classical
  exact ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (hT : IsDiagonalizable T) (x : V),
  DirectSum.coeLinearMap (fun μ : K => T.eigenspace μ) (eigenspaceDecomposition T hT x) = x

end Specs.NumAnalysis206.MatrixData

namespace Specs.NumAnalysis206.MatrixData
set_option linter.checkUnivs false
open _root_.NumAnalysis206.MatrixDefinitions
universe u v

def upperTriangular_iff : Prop :=
  ∀ {K : Type u} [Zero K] {n : ℕ} (A : Mat K n n),
    IsUpperTriangular A ↔ A.IsUpperTriangular

def lowerTriangular_iff : Prop :=
  ∀ {K : Type u} [Zero K] {n : ℕ} (A : Mat K n n),
    IsLowerTriangular A ↔ A.IsLowerTriangular

def operatorNorm_apply_le : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n) (x : Vec K n),
    ‖A.toEuclideanLin x‖ ≤ operatorNorm A * ‖x‖

def operatorNorm_mul_le : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} {l : ℕ} (A : Mat K m n) (B : Mat K n l),
    operatorNorm (A * B) ≤ operatorNorm A * operatorNorm B

def operatorNorm_adjoint : Prop :=
  ∀ {K : Type u} [RCLike K] {m n : ℕ} (A : Mat K m n), operatorNorm (adjoint A) = operatorNorm A

def spectralProjection_characterization : Prop :=
  ∀ {K : Type u} [RCLike K] {n : ℕ} (A : Mat K n n) (hA : A.IsHermitian) (s : Set ℝ) (x : Vec K n),
    spectralProjection A hA s x ∈ spectralSubspace A s ∧
    x - spectralProjection A hA s x ∈ (spectralSubspace A s).orthogonal

def diagonalizable_iff_eigenbasis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) ,
    IsDiagonalizable T ↔
      ∃ (ι : Type (max u v)) (b : Module.Basis ι K V) (μ : ι → K),
        ∀ i, T (b i) = μ i • b i

end Specs.NumAnalysis206.MatrixData
