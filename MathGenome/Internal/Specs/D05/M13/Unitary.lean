import MathGenome.Internal.Specs.D05.M13.AdjointLaws
import MathGenome.Internal.Specs.D05.M12.Parallelogram
import MathGenome.Internal.Specs.D05.M03.EqualDimension
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
Independent specifications for K05.13.unitary, paper.tex:2141–2150.
We retain the shared convention `firstInner x y = inner F y x` and the
canonical `LinearMap.adjoint`. A unitary map is a surjective inner-product
isometry; over the real field this same condition is called orthogonal.
The basic definitions and norm statements work without finite dimension.
Every statement involving adjoints or endomorphism surjectivity retains
finite dimension. No positivity of dimension, equal domain/codomain dimension,
completeness, or extra inverse certificate is assumed.
-/

noncomputable section

namespace D05

/-- A linear map preserving the paper's first-slot-linear inner product. -/
def IsInnerIsometry {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W] (U : V →ₗ[F] W) : Prop :=
  ∀ x y, firstInner (F := F) (U x) (U y) = firstInner (F := F) x y

/-- Unitary over ℂ, orthogonal over ℝ; the domain and codomain may differ. -/
def IsUnitaryMap {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W] (U : V →ₗ[F] W) : Prop :=
  IsInnerIsometry U ∧ Function.Surjective U

end D05

namespace Specs.D05.M13.Unitary

universe u v w

/-- Type and value of the isometry predicate on linear maps. -/
def isometry_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {W : Type w} → [RCLike F] →
    [NormedAddCommGroup V] → [NormedAddCommGroup W] →
    [InnerProductSpace F V] → [InnerProductSpace F W] → (V →ₗ[F] W) → Prop

def isometry_value : isometry_type.{u, v, w} := fun U => _root_.D05.IsInnerIsometry U

def unitary_type : Type (max (u + 1) (v + 1) (w + 1)) := isometry_type.{u, v, w}

def unitary_value : unitary_type.{u, v, w} := fun U => _root_.D05.IsUnitaryMap U

/-- The real specialization has the name orthogonal. -/
def orthogonal_type : Type (max (v + 1) (w + 1)) :=
  {V : Type v} → {W : Type w} →
    [NormedAddCommGroup V] → [NormedAddCommGroup W] →
    [InnerProductSpace ℝ V] → [InnerProductSpace ℝ W] → (V →ₗ[ℝ] W) → Prop

def orthogonal_value : orthogonal_type.{v, w} := fun U => _root_.D05.IsUnitaryMap U

/-- The predicate agrees with Mathlib’s bundled linear isometries. -/
def isometry_iff_linearIsometry : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsInnerIsometry U ↔
    ∃ i : V →ₗᵢ[F] W, i.toLinearMap = U

/-- Norm preservation characterizes a linear isometry (polarization). -/
def isometry_iff_norm : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsInnerIsometry U ↔ ∀ x, ‖U x‖ = ‖x‖

/-- In particular, an inner-product isometry preserves norms. -/
def isometry_norm : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsInnerIsometry U → ∀ x, ‖U x‖ = ‖x‖

/-- Every isometry is injective. -/
def isometry_injective : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsInnerIsometry U → Function.Injective U

/-- The adjoint criterion for arbitrary domain and codomain. -/
def isometry_iff_adjoint_comp : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsInnerIsometry U ↔
    (_root_.LinearMap.adjoint U).comp U = LinearMap.id

/-- Surjective isometries are exactly the maps with both adjoint inverse identities. -/
def unitary_iff_adjoint_identities : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsUnitaryMap U ↔
    (_root_.LinearMap.adjoint U).comp U = LinearMap.id ∧
      U.comp (_root_.LinearMap.adjoint U) = LinearMap.id

/-- A surjective isometry between possibly different spaces is bijective. -/
def unitary_bijective : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsUnitaryMap U → Function.Bijective U

/-- Construct an actual linear equivalence with inverse equal to the adjoint. -/
def unitary_inverse : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsUnitaryMap U →
    ∃ e : V ≃ₗ[F] W, e.toLinearMap = U ∧
      e.symm.toLinearMap = _root_.LinearMap.adjoint U

/-- For any such equivalence its existing inverse is the adjoint. -/
def inverse_eq_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ e : V ≃ₗ[F] W, _root_.D05.IsInnerIsometry e.toLinearMap →
    e.symm.toLinearMap = _root_.LinearMap.adjoint e.toLinearMap

/-- The surjective predicate agrees with bundled linear isometric equivalences. -/
def unitary_iff_linearIsometryEquiv : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  ∀ U : V →ₗ[F] W, _root_.D05.IsUnitaryMap U ↔
    ∃ e : V ≃ₗᵢ[F] W, e.toLinearEquiv.toLinearMap = U

/-- Finite-dimensional isometric endomorphisms are surjective. -/
def endomorphism_isometry_iff_unitary : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ U : V →ₗ[F] V, _root_.D05.IsInnerIsometry U ↔ _root_.D05.IsUnitaryMap U

/-- The paper’s full endomorphism conclusion, starting with the one-sided identity. -/
def endomorphism_adjoint_criterion : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V],
  ∀ U : V →ₗ[F] V,
    (_root_.LinearMap.adjoint U).comp U = LinearMap.id →
      U.comp (_root_.LinearMap.adjoint U) = LinearMap.id ∧
      ∃ e : V ≃ₗ[F] V, e.toLinearMap = U ∧
        e.symm.toLinearMap = _root_.LinearMap.adjoint U

/-- The zero map is an isometry exactly when its domain is a zero space. -/
def zero_map_isometry_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  _root_.D05.IsInnerIsometry (0 : V →ₗ[F] W) ↔ Subsingleton V

/-- The zero map is unitary exactly when both spaces are zero spaces. -/
def zero_map_unitary_iff : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W],
  _root_.D05.IsUnitaryMap (0 : V →ₗ[F] W) ↔ Subsingleton V ∧ Subsingleton W

end Specs.D05.M13.Unitary
