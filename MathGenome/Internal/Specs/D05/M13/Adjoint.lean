import MathGenome.Internal.Specs.D05.M03.LinearMap
import MathGenome.Internal.Specs.D05.M12.Riesz
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Independent specifications for K05.13.adjoint, paper.tex:2077–2086.
The shared `D05.firstInner u v = inner F v u` is linear in its first slot.
The adjoint is an ordinary bundled linear map, over the same real or complex
field, between arbitrary finite-dimensional domain and codomain. No nonzero
or equal-dimension assumption, continuity premise, or completeness premise is added.
-/

noncomputable section

namespace Specs.D05.M13.Adjoint

universe u v w

/-- Type of the adjoint operation on finite-dimensional inner-product spaces. -/
def adjoint_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {W : Type w} → [RCLike F] →
    [NormedAddCommGroup V] → [NormedAddCommGroup W] →
    [InnerProductSpace F V] → [InnerProductSpace F W] →
    [FiniteDimensional F V] → [FiniteDimensional F W] →
    (V →ₗ[F] W) → (W →ₗ[F] V)

/-- Reuse Mathlib's canonical adjoint; the identity below checks the convention. -/
def adjoint_value : adjoint_type.{u, v, w} := fun T => _root_.LinearMap.adjoint T

/-- The defining identity, with precisely the paper's order of arguments. -/
def adjoint_identity : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ (T : V →ₗ[F] W) (v : V) (w : W),
    _root_.D05.firstInner (F := F) (T v) w =
      _root_.D05.firstInner (F := F) v (_root_.LinearMap.adjoint T w)

/-- Every map obeying the defining identity is the canonical adjoint. -/
def adjoint_unique : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ (T : V →ₗ[F] W) (S : W →ₗ[F] V),
    (∀ (v : V) (w : W), _root_.D05.firstInner (F := F) (T v) w =
      _root_.D05.firstInner (F := F) v (S w)) → S = _root_.LinearMap.adjoint T

/-- Full existence and uniqueness of a linear map satisfying the identity. -/
def exists_unique_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ T : V →ₗ[F] W, ∃! S : W →ₗ[F] V,
    ∀ (v : V) (w : W), _root_.D05.firstInner (F := F) (T v) w =
      _root_.D05.firstInner (F := F) v (S w)

/-- Linearity in the vector to which the adjoint is applied. -/
def adjoint_linear : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ (T : V →ₗ[F] W) (a b : F) (w₁ w₂ : W),
    _root_.LinearMap.adjoint T (a • w₁ + b • w₂) =
      a • _root_.LinearMap.adjoint T w₁ + b • _root_.LinearMap.adjoint T w₂

/-- A zero domain is included, with the unique map into that domain as adjoint. -/
def zero_domain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ [Subsingleton V] (T : V →ₗ[F] W), _root_.LinearMap.adjoint T = 0

/-- A zero codomain is included, with the unique map out of it as adjoint. -/
def zero_codomain : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ [Subsingleton W] (T : V →ₗ[F] W), _root_.LinearMap.adjoint T = 0

end Specs.D05.M13.Adjoint
