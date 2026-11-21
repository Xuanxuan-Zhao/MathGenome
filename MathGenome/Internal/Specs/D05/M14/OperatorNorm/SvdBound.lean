import MathGenome.Internal.Specs.D05.M14.Svd
import MathGenome.Internal.Specs.D05.M12.FourierParseval

/-! The SVD estimate in K05.14.operator_norm, paper.tex:2547–2567.
`T.singularValues 0` is the first positive singular value when the rank is
positive, and is zero when the rank is zero. All spaces, including zero
spaces, are allowed. The set in the supremum statements uses the closed
unit ball, which contains zero in every dimension.
Theorems about a particular SVD quantify over the shared SVD record; the
supremum statements have no decomposition premise.
-/

noncomputable section
namespace Specs.D05.M14.OperatorNorm.SvdBound
universe u v w
def norm_sq_expansion : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (v : V),
    ‖T v‖ ^ 2 = ∑ i : Fin (Module.finrank F (LinearMap.range T)),
      T.singularValues i ^ 2 * ‖_root_.D05.firstInner (F := F) v (d.domainBasis (Fin.castLE T.finrank_range_le i))‖ ^ 2


def norm_sq_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (v : V),
    ‖T v‖ ^ 2 ≤ T.singularValues 0 ^ 2 * ‖v‖ ^ 2


def norm_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (v : V),
    ‖T v‖ ≤ T.singularValues 0 * ‖v‖


def attains_first : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (d : _root_.D05.SingularValueDecomposition T) (hr : 0 < Module.finrank F (LinearMap.range T)),
    let e := d.domainBasis (Fin.castLE T.finrank_range_le ⟨0, hr⟩)
    ‖e‖ = 1 ∧ ‖T e‖ = T.singularValues 0 ∧
      ‖T e‖ ^ 2 = T.singularValues 0 ^ 2 * ‖e‖ ^ 2


def rank_zero_outputs : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Module.finrank F (LinearMap.range T) = 0 ↔
      T = 0 ∧ ∀ v : V, T v = 0


def unit_ball_bounded : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}).Nonempty ∧ BddAbove ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1})


def unit_ball_isLUB : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    IsLUB ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) (T.singularValues 0)


def unit_ball_supremum : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    sSup ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) = T.singularValues 0 ∧
      (T ≠ 0 → 0 < T.singularValues 0) ∧
      (T = 0 → sSup ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) = 0)


def zero_domain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Module.finrank F V = 0 →
      T = 0 ∧ (∀ v : V, T v = 0) ∧
        IsLUB ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) 0 ∧ sSup ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) = 0

end Specs.D05.M14.OperatorNorm.SvdBound
