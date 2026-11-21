import MathGenome.Internal.Specs.D05.M14.OperatorNorm.SvdBound
import Mathlib.Analysis.Normed.Operator.NNNorm

/-! K05.14.operator_norm, paper.tex:2547–2567.
The definition uses the closed unit ball, including the zero vector in all
dimensions. The natural-number singular-value sequence is zero after rank;
index zero represents the paper's s₁ precisely when T is nonzero.
No decomposition, positive dimension, continuity, or completeness premise is
imposed. Finite-dimensional continuity is used only in the proved library bridge.
-/
noncomputable section
namespace D05
variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [NormedAddCommGroup W]
  [InnerProductSpace F V] [InnerProductSpace F W]
  [FiniteDimensional F V] [FiniteDimensional F W]

/-- The manuscript's closed-unit-ball definition of the operator norm. -/
def operatorNorm (T : V →ₗ[F] W) : ℝ :=
  sSup ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1})
end D05

namespace Specs.D05.M14.OperatorNorm
universe u v w z

def operatorNorm_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {W : Type w} → [RCLike F] →
  [NormedAddCommGroup V] → [NormedAddCommGroup W] →
  [InnerProductSpace F V] → [InnerProductSpace F W] →
  [FiniteDimensional F V] → [FiniteDimensional F W] → (V →ₗ[F] W) → ℝ

def operatorNorm_value : operatorNorm_type.{u,v,w} := fun T =>
  sSup ((fun v => ‖T v‖) '' {v | ‖v‖ ≤ 1})

def definition_eq : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.operatorNorm T = sSup ((fun v => ‖T v‖) '' {v | ‖v‖ ≤ 1})

def unit_ball_supremum : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}).Nonempty ∧
    BddAbove ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) ∧
    IsLUB ((fun v : V => ‖T v‖) '' {v : V | ‖v‖ ≤ 1}) (_root_.D05.operatorNorm T)

def eq_first_singularValue : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.operatorNorm T = T.singularValues 0

def nonzero_attains : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), T ≠ 0 →
    0 < T.singularValues 0 ∧ _root_.D05.operatorNorm T = T.singularValues 0 ∧
    ∃ v : V, ‖v‖ = 1 ∧ ‖T v‖ = _root_.D05.operatorNorm T

def zero_map : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W], _root_.D05.operatorNorm (0 : V →ₗ[F] W) = 0

def zero_domain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), Module.finrank F V = 0 →
    T = 0 ∧ _root_.D05.operatorNorm T = 0

def eq_continuous_opNorm : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.operatorNorm T = ‖T.toContinuousLinearMap‖

def apply_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (v : V),
    ‖T v‖ ≤ _root_.D05.operatorNorm T * ‖v‖

def adjoint_eq : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    _root_.D05.operatorNorm (LinearMap.adjoint T) = _root_.D05.operatorNorm T

def nonneg : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), 0 ≤ _root_.D05.operatorNorm T

def eq_zero_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W), _root_.D05.operatorNorm T = 0 ↔ T = 0

def smul : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (a : F) (T : V →ₗ[F] W),
    _root_.D05.operatorNorm (a • T) = ‖a‖ * _root_.D05.operatorNorm T

def add_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (S T : V →ₗ[F] W),
    _root_.D05.operatorNorm (S + T) ≤ _root_.D05.operatorNorm S + _root_.D05.operatorNorm T

def norm_axioms : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    (∀ T : V →ₗ[F] W, 0 ≤ _root_.D05.operatorNorm T) ∧
    (∀ T : V →ₗ[F] W, _root_.D05.operatorNorm T = 0 ↔ T = 0) ∧
    (∀ (a : F) (T : V →ₗ[F] W),
      _root_.D05.operatorNorm (a • T) = ‖a‖ * _root_.D05.operatorNorm T) ∧
    (∀ S T : V →ₗ[F] W,
      _root_.D05.operatorNorm (S + T) ≤ _root_.D05.operatorNorm S + _root_.D05.operatorNorm T)

/-- Composition is allowed between three different spaces and dimensions. -/
def comp_le : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] {X : Type z} [NormedAddCommGroup X]
    [InnerProductSpace F X] [FiniteDimensional F X]
    (S : W →ₗ[F] X) (T : V →ₗ[F] W),
    _root_.D05.operatorNorm (S.comp T) ≤
      _root_.D05.operatorNorm S * _root_.D05.operatorNorm T

end Specs.D05.M14.OperatorNorm
