import MathGenome.Internal.Specs.D05.M14.Svd
import MathGenome.Internal.Specs.D05.M14.OperatorNorm

/-! Truncation stage of K05.14.low_rank, paper.tex:2569–2586.
Indices are zero based, so `T.singularValues k` is the paper's s_(k+1).
The chosen SVD is arbitrary; there is no assumption of positive rank or dimension.
-/
noncomputable section
open scoped BigOperators

namespace D05
variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- Retain exactly the first min(k, rank T) terms of the SVD. -/
def svdTruncation (T : V →ₗ[F] W) (d : SingularValueDecomposition T) (k : ℕ) :
    V →ₗ[F] W where
  toFun v := ∑ i : Fin (min k (Module.finrank F T.range)),
    ((T.singularValues i : F) * firstInner v
      (d.domainBasis (Fin.castLE T.finrank_range_le
        (Fin.castLE (min_le_right k _) i)))) •
      d.codomainBasis (Fin.castLE (Submodule.finrank_le _)
        (Fin.castLE (min_le_right k _) i))
  map_add' x y := by
    simp [firstInner, inner_add_right, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp [firstInner, inner_smul_right, mul_left_comm, smul_smul, Finset.smul_sum]
end D05

namespace Specs.D05.M14.LowRank.Truncation
universe u v w

def truncation_type :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ), V →ₗ[F] W

def truncation_value : truncation_type := @_root_.D05.svdTruncation

def apply_formula : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ) (v : V),
    _root_.D05.svdTruncation T d k v =
      ∑ i : Fin (min k (Module.finrank F T.range)),
        ((T.singularValues i : F) * _root_.D05.firstInner v
          (d.domainBasis (Fin.castLE T.finrank_range_le
            (Fin.castLE (min_le_right k _) i)))) •
          d.codomainBasis (Fin.castLE (Submodule.finrank_le _)
            (Fin.castLE (min_le_right k _) i))

def rank_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ),
    Module.finrank F (LinearMap.range (_root_.D05.svdTruncation T d k)) ≤ k

def eq_self_of_rank_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ), Module.finrank F T.range ≤ k →
    _root_.D05.svdTruncation T d k = T

def error_norm : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ),
    _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) = T.singularValues k

def error_of_lt_rank : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ), k < Module.finrank F T.range →
    _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) = T.singularValues k

def error_of_rank_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (k : ℕ), Module.finrank F T.range ≤ k →
    _root_.D05.svdTruncation T d k = T ∧
      _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) = 0

def zero_truncation : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T), _root_.D05.svdTruncation T d 0 = 0

def rank_zero : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (hr : Module.finrank F T.range = 0) (k : ℕ),
    _root_.D05.svdTruncation T d k = T ∧
      _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) = 0

def zero_domain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (hV : Module.finrank F V = 0) (k : ℕ),
    _root_.D05.svdTruncation T d k = T ∧
      _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) = 0

def zero_codomain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (hW : Module.finrank F W = 0) (k : ℕ),
    _root_.D05.svdTruncation T d k = T ∧
      _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) = 0

end Specs.D05.M14.LowRank.Truncation
