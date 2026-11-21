import MathGenome.Internal.Specs.D05.M14.LowRank.Truncation

/-! K05.14.low_rank, paper.tex:2569–2586.
The truncation is the shared finite SVD sum, with the paper's first-slot-linear
inner product. `T.singularValues k` denotes s_(k+1); the sequence is zero after
rank(T). No positive-rank, positive-dimension, or uniqueness premise is used.
-/

noncomputable section
namespace Specs.D05.M14.LowRank
universe u v w

/-- Every chosen truncated SVD minimizes error among all rank-at-most-k maps. -/
def optimality : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (d : _root_.D05.SingularValueDecomposition T)
    (k : ℕ) (S : V →ₗ[F] W), Module.finrank F S.range ≤ k →
    _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) ≤
      _root_.D05.operatorNorm (T - S)

/-- The paper's rank bound, optimality, and exact minimum, for the displayed sum. -/
def best_approximation : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (d : _root_.D05.SingularValueDecomposition T) (k : ℕ),
    Module.finrank F (LinearMap.range (_root_.D05.svdTruncation T d k)) ≤ k ∧
    (∀ S : V →ₗ[F] W, Module.finrank F S.range ≤ k →
      _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) ≤
        _root_.D05.operatorNorm (T - S)) ∧
    _root_.D05.operatorNorm (T - _root_.D05.svdTruncation T d k) =
      if k < Module.finrank F T.range then T.singularValues k else 0

/-- The least error is attained, without assuming a supplied SVD. -/
def minimum_error : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (k : ℕ),
    IsLeast {ε : ℝ | ∃ S : V →ₗ[F] W,
      Module.finrank F S.range ≤ k ∧ _root_.D05.operatorNorm (T - S) = ε}
      (if k < Module.finrank F T.range then T.singularValues k else 0)

end Specs.D05.M14.LowRank
