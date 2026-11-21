import MathGenome.Internal.Specs.D05.M14.Svd
import MathGenome.Internal.Specs.D05.M14.OperatorNorm

/-! K05.14.low_rank, paper.tex:2569–2586, lower-bound stage.
Library index `k` is the source's s_(k+1). The subspace below is exactly the
span of the first k+1 domain singular vectors. No positive-dimension or SVD
premise is imposed on the final operator-norm bound. -/
noncomputable section
namespace Specs.D05.M14.LowRank.LowerBound
universe u v w

/-- Every vector in the initial singular subspace has the required expansion bound. -/
def span_norm_lower : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (d : _root_.D05.SingularValueDecomposition T)
    (k : ℕ) (hk : k < Module.finrank F T.range) (x : V),
    x ∈ Submodule.span F (Set.range (fun j : Fin (k + 1) =>
      d.domainBasis (Fin.castLE T.finrank_range_le
        (Fin.castLE (Nat.succ_le_of_lt hk) j)))) →
    T.singularValues k * ‖x‖ ≤ ‖T x‖

/-- Rank-nullity on that subspace supplies a unit kernel vector, including k=0. -/
def unit_kernel_vector : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T S : V →ₗ[F] W) (d : _root_.D05.SingularValueDecomposition T)
    (k : ℕ) (hk : k < Module.finrank F T.range),
    Module.finrank F S.range ≤ k →
    ∃ x : V,
      x ∈ Submodule.span F (Set.range (fun j : Fin (k + 1) =>
        d.domainBasis (Fin.castLE T.finrank_range_le
          (Fin.castLE (Nat.succ_le_of_lt hk) j)))) ∧
      S x = 0 ∧ ‖x‖ = 1 ∧ T.singularValues k ≤ ‖T x‖

/-- The error of every rank-at-most-k map is at least s_(k+1). -/
def lower_bound : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T S : V →ₗ[F] W) (k : ℕ),
    k < Module.finrank F T.range → Module.finrank F S.range ≤ k →
    T.singularValues k ≤ _root_.D05.operatorNorm (T - S)

end Specs.D05.M14.LowRank.LowerBound
