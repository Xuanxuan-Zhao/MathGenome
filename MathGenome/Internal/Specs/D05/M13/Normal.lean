import MathGenome.Internal.Specs.D05.M13.SelfAdjoint
import MathGenome.Internal.Specs.D05.M13.Unitary

/-!
Independent specifications for K05.13.normal, paper.tex:2152–2153.
Normality, self-adjointness, the real plane rotation, and unitarity are the
shared upstream objects. The adjoint is the canonical adjoint already bridged
to `D05.firstInner x y = inner F y x`. Every general statement permits zero
spaces and both real and complex scalars. Unitary transport can be between
different spaces; no positive dimension or spectral hypothesis is imposed.
-/

noncomputable section

namespace Specs.D05.M13.Normal

universe u v w

def normalOperator_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → [FiniteDimensional F V] → (V →ₗ[F] V) → Prop

/-- Reuse the shared predicate, whose value is precisely TT† = T†T. -/
def normalOperator_value : normalOperator_type.{u, v} :=
  fun T => _root_.D05.normalOperator T

def normal_iff_adjoint_commutes : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T ↔
      T.comp (LinearMap.adjoint T) = (LinearMap.adjoint T).comp T

def normal_iff_mathlib : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T ↔ IsStarNormal T

def selfAdjoint_products : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T →
      T.comp (LinearMap.adjoint T) = T.comp T ∧
        (LinearMap.adjoint T).comp T = T.comp T

def selfAdjoint_normal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint T → _root_.D05.normalOperator T

def unitary_products : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (U : V →ₗ[F] V),
    _root_.D05.IsUnitaryMap U →
      U.comp (LinearMap.adjoint U) = LinearMap.id ∧
        (LinearMap.adjoint U).comp U = LinearMap.id

def unitary_normal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (U : V →ₗ[F] V),
    _root_.D05.IsUnitaryMap U → _root_.D05.normalOperator U

/-- The very same real rotation J, not an unspecified existential example. -/
def rotation_counterexample : Prop :=
  _root_.D05.normalOperator _root_.D05.planeRotation ∧
    ¬ _root_.D05.selfAdjoint _root_.D05.planeRotation

/-- U is bundled with its inverse; the hypothesis is still the shared
surjective-isometry predicate, rather than an assumed adjoint formula. -/
def adjoint_unitary_conjugate : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (U : V ≃ₗ[F] W), _root_.D05.IsUnitaryMap U.toLinearMap →
  ∀ T : V →ₗ[F] V,
    LinearMap.adjoint ((U.toLinearMap.comp T).comp U.symm.toLinearMap) =
      (U.toLinearMap.comp (LinearMap.adjoint T)).comp U.symm.toLinearMap

/-- Invariance in both directions, with the actual inverse of U. -/
def unitary_conjugate_normal_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (U : V ≃ₗ[F] W), _root_.D05.IsUnitaryMap U.toLinearMap →
  ∀ T : V →ₗ[F] V,
    _root_.D05.normalOperator ((U.toLinearMap.comp T).comp U.symm.toLinearMap) ↔
      _root_.D05.normalOperator T

/-- Unbundled version: unitarity alone supplies the inverse U†. -/
def unitary_transport_normal_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (U : V →ₗ[F] W), _root_.D05.IsUnitaryMap U →
  ∀ T : V →ₗ[F] V,
    _root_.D05.normalOperator ((U.comp T).comp (LinearMap.adjoint U)) ↔
      _root_.D05.normalOperator T

end Specs.D05.M13.Normal
