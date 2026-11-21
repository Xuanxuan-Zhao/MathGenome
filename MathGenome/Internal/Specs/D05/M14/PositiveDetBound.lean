import MathGenome.Internal.Specs.D05.M14.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant

/-! K05.14.positive_det_bound, paper.tex:2665–2683.
The inequalities are real inequalities. The real-valuedness statement identifies
both sides with the original scalar determinant and diagonal product, including
over ℂ. The basis is arbitrary and may be empty. Positivity uses the canonical
paper predicate and therefore includes self-adjointness over both ℝ and ℂ. -/

noncomputable section
open scoped BigOperators

namespace Specs.D05.M14.PositiveDetBound

def real_values : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] {n : ℕ}
    (T : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V),
    _root_.D05.positiveSemidefinite T →
      (RCLike.re (LinearMap.det T) : F) = LinearMap.det T ∧
      0 ≤ RCLike.re (LinearMap.det T) ∧
      ∀ i, (RCLike.re (_root_.D05.firstInner (F := F) (T (e i)) (e i)) : F) =
        _root_.D05.firstInner (F := F) (T (e i)) (e i)

def inequality : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] {n : ℕ}
    (T : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V),
    _root_.D05.positiveSemidefinite T →
      RCLike.re (LinearMap.det T) ≤
        ∏ i, RCLike.re (_root_.D05.firstInner (F := F) (T (e i)) (e i))

open scoped ComplexOrder in
/-- The manuscript's displayed inequality in the scalar field; this order
restricts to the ordinary real order on the real-valued sides. -/
def scalar_inequality : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] {n : ℕ}
    (T : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V),
    _root_.D05.positiveSemidefinite T →
      LinearMap.det T ≤ ∏ i, _root_.D05.firstInner (F := F) (T (e i)) (e i)

/-- Equality for a positive definite map is equivalent to every basis vector
being an eigenvector. Nonvanishing of those vectors is part of the basis data. -/
def equality_iff_eigenbasis : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] {n : ℕ}
    (T : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V),
    _root_.D05.positiveDefinite T →
      (RCLike.re (LinearMap.det T) =
        ∏ i, RCLike.re (_root_.D05.firstInner (F := F) (T (e i)) (e i)) ↔
        ∀ i, ∃ μ : F, T (e i) = μ • e i)

/-- The scalar equality in the paper is also recorded explicitly. -/
def scalar_equality_iff_eigenbasis : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] {n : ℕ}
    (T : V →ₗ[F] V) (e : OrthonormalBasis (Fin n) F V),
    _root_.D05.positiveDefinite T →
      (LinearMap.det T = ∏ i, _root_.D05.firstInner (F := F) (T (e i)) (e i) ↔
        ∀ i, ∃ μ : F, T (e i) = μ • e i)

def empty_case : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V]
    (T : V →ₗ[F] V) (e : OrthonormalBasis (Fin 0) F V),
    LinearMap.det T = 1 ∧
      (∏ i, _root_.D05.firstInner (F := F) (T (e i)) (e i)) = 1

end Specs.D05.M14.PositiveDetBound
