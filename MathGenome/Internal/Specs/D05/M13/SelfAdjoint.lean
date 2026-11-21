import MathGenome.Internal.Specs.D05.M13.AdjointLaws
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
Independent specifications for K05.13.self_adjoint, paper.tex:2119–2126.
Adjoints are the canonical adjoints already bridged to `D05.firstInner`.
All general statements include the zero space and both real and complex scalars.
The counterexample uses the standard Euclidean inner product on the real plane,
with the displayed column-coordinate matrix, rather than an arbitrary norm on R².
-/

noncomputable section

namespace D05

/-- Self-adjointness in the paper's equality order. -/
def selfAdjoint {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  T = LinearMap.adjoint T

/-- Normality uses composition of endomorphisms. -/
def normalOperator {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) : Prop :=
  T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T

/-- The source's real matrix, with rows and columns in the order 0,1. -/
def planeRotationMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The actual operator represented by the displayed matrix on Euclidean R². -/
def planeRotation : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanLin planeRotationMatrix

end D05

namespace Specs.D05.M13.SelfAdjoint

universe u v w

def selfAdjoint_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → [FiniteDimensional F V] → (V →ₗ[F] V) → Prop

def selfAdjoint_value : selfAdjoint_type.{u, v} :=
  fun T => T = LinearMap.adjoint T

def normalOperator_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → [FiniteDimensional F V] → (V →ₗ[F] V) → Prop

def normalOperator_value : normalOperator_type.{u, v} :=
  fun T => T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T

def planeRotationMatrix_type := Matrix (Fin 2) (Fin 2) ℝ

def planeRotationMatrix_value : planeRotationMatrix_type := !![0, -1; 1, 0]

def planeRotation_type := EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)

def planeRotation_value : planeRotation_type :=
  Matrix.toEuclideanLin _root_.D05.planeRotationMatrix

/-- Bridge to the standard star-algebra predicate; the equality order is reversed. -/
def selfAdjoint_iff_mathlib : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T ↔ IsSelfAdjoint T

/-- Bridge to the inner-product symmetry predicate. -/
def selfAdjoint_iff_isSymmetric : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T ↔ T.IsSymmetric

/-- Bridge from composition to the star-normality predicate on endomorphisms. -/
def normalOperator_iff_mathlib : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T ↔ IsStarNormal T

def selfAdjoint_implies_normal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T → _root_.D05.normalOperator T

/-- This verifies the operator is precisely the matrix in the source. -/
def rotation_matrix : Prop :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis _root_.D05.planeRotation =
      _root_.D05.planeRotationMatrix

def rotation_adjoint : Prop :=
  LinearMap.adjoint _root_.D05.planeRotation = -_root_.D05.planeRotation

def rotation_products : Prop :=
  _root_.D05.planeRotation.comp (LinearMap.adjoint _root_.D05.planeRotation) =
    LinearMap.id ∧
  (LinearMap.adjoint _root_.D05.planeRotation).comp _root_.D05.planeRotation =
    LinearMap.id

def rotation_normal : Prop := _root_.D05.normalOperator _root_.D05.planeRotation

def rotation_not_selfAdjoint : Prop := ¬ _root_.D05.selfAdjoint _root_.D05.planeRotation

/-- The polynomial variable is formal; charpoly is det(X I - J). -/
def rotation_charpoly : Prop :=
  _root_.D05.planeRotationMatrix.charpoly = (Polynomial.X : Polynomial ℝ) ^ 2 + 1

/-- The scalar determinant identity as printed in the paper. -/
def rotation_det_sub : Prop :=
  ∀ t : ℝ, Matrix.det (t • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
    _root_.D05.planeRotationMatrix) = t ^ 2 + 1

def rotation_no_real_root : Prop :=
  ∀ t : ℝ, ¬ Polynomial.IsRoot _root_.D05.planeRotationMatrix.charpoly t

/-- There are no nonzero real eigenvectors, not merely no particular chosen basis. -/
def rotation_no_real_eigenvector : Prop :=
  ∀ (t : ℝ) (v : EuclideanSpace ℝ (Fin 2)),
    _root_.D05.planeRotation v = t • v → v = 0

/-- Arbitrary basis index types are allowed, so every real eigenbasis is excluded. -/
def rotation_no_real_eigenbasis : Prop :=
  ∀ {ι : Type w}, ¬ ∃ b : Module.Basis ι ℝ (EuclideanSpace ℝ (Fin 2)),
    ∀ i, ∃ t : ℝ, _root_.D05.planeRotation (b i) = t • b i

/-- The two failed converses, witnessed by one and the same operator. -/
def real_normal_counterexample : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
    _root_.D05.normalOperator T ∧ ¬ _root_.D05.selfAdjoint T ∧
      ¬ ∃ b : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)),
        ∀ i, ∃ t : ℝ, T (b i) = t • b i

end Specs.D05.M13.SelfAdjoint
