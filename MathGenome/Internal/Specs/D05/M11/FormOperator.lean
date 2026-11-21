import MathGenome.Internal.Specs.D05.M11.Hermitian
import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.Specs.D05.M12.Riesz
import MathGenome.Internal.Specs.D05.M13.Adjoint

/-!
K05.11.form_operator, paper.tex:1805–1815. The inner-product structure
encodes the given positive definite `h`, using the shared convention
`D05.firstInner u v = inner F v u`. No positivity or symmetry of `B` is
assumed for representation. Real bilinear forms are included explicitly.
All finite-dimensional assertions include the zero space; no completeness
premise is imposed. The finite sums are indexed, including the empty sum.
-/
noncomputable section

namespace Specs.D05.M11.FormOperator

open Module
open scoped BigOperators

universe u v w

/-- The paper's sum, bundled as a linear map. It can be formed in any finite
basis, though its representation property requires orthonormality. -/
def basisOperator_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {I : Type w} → [RCLike F] →
    [AddCommGroup V] → [Module F V] → [Fintype I] → Basis I F V →
    Specs.D05.M11.Hermitian.sesquilinearForm_value F V → (V →ₗ[F] V)

def basisOperator_value : basisOperator_type.{u, v, w} :=
  fun e B => ∑ j, (B.flip (e j)).smulRight (e j)

/-- A canonical choice of basis for defining the representing operator. -/
def formOperator_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → [FiniteDimensional F V] →
    Specs.D05.M11.Hermitian.sesquilinearForm_value F V → (V →ₗ[F] V)

def formOperator_value : formOperator_type.{u, v} :=
  fun {F} {V} _ _ _ _ B => basisOperator_value (stdOrthonormalBasis F V).toBasis B

/-- Conjugation on ℝ is the identity, so this retains exactly the original
function of an arbitrary real bilinear form. -/
def realForm_type : Type (v + 1) :=
  {V : Type v} → [AddCommGroup V] → [Module ℝ V] →
    LinearMap.BilinForm ℝ V → Specs.D05.M11.Hermitian.sesquilinearForm_value ℝ V

def realForm_value : realForm_type.{v} := fun B => B

def basisOperator_apply : Prop :=
  ∀ {F V I : Type*} [RCLike F] [AddCommGroup V] [Module F V] [Fintype I]
    (e : Basis I F V) (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V)
    (u : V), basisOperator_value e B u = ∑ j, B u (e j) • e j

def representation_in_basis : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] (e : Basis I F V), _root_.D05.orthonormalFamily (F := F) e →
    ∀ (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V) (u v : V),
      _root_.D05.firstInner (F := F) (basisOperator_value e B u) v = B u v

/-- The canonical operator has the displayed sum in every orthonormal basis. -/
def formula_in_any_basis : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [Fintype I] (e : Basis I F V),
    _root_.D05.orthonormalFamily (F := F) e →
    ∀ (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V) (u : V),
      formOperator_value B u = ∑ j, B u (e j) • e j

/-- Uniqueness itself needs neither dimension nor completeness assumptions. -/
def representing_operator_unique : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V) (A A' : V →ₗ[F] V),
    (∀ u v, _root_.D05.firstInner (F := F) (A u) v = B u v) →
    (∀ u v, _root_.D05.firstInner (F := F) (A' u) v = B u v) → A = A'

def representation : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V)
    (u v : V), _root_.D05.firstInner (F := F) (formOperator_value B u) v = B u v

def exists_unique_representation : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V),
    ∃! A : V →ₗ[F] V, ∀ u v, _root_.D05.firstInner (F := F) (A u) v = B u v

/-- Each orthonormal basis, even with a different index type, yields the
same actual linear map. -/
def basis_independent : Prop :=
  ∀ {F V I J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] [Fintype J] (e : Basis I F V) (f : Basis J F V),
    _root_.D05.orthonormalFamily (F := F) e →
    _root_.D05.orthonormalFamily (F := F) f →
    ∀ B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V,
      basisOperator_value e B = basisOperator_value f B

def hermitian_iff_adjoint : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V),
    Specs.D05.M11.Hermitian.isHermitian_value B ↔
      LinearMap.adjoint (formOperator_value B) = formOperator_value B

def hermitian_iff_selfAdjoint : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V),
    Specs.D05.M11.Hermitian.isHermitian_value B ↔ IsSelfAdjoint (formOperator_value B)

/-- This equality gives the correspondence of all diagonal conditions. -/
def diagonal_identity : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V)
    (u : V), B u u = _root_.D05.firstInner (F := F) (formOperator_value B u) u

/-- Positivity includes Hermitian symmetry, so diagonal values are real.
The definition is vacuous on nonzero vectors of the zero space. -/
def positive_definite_iff : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V),
    (Specs.D05.M11.Hermitian.isHermitian_value B ∧
      ∀ u : V, u ≠ 0 → 0 < RCLike.re (B u u)) ↔
    (LinearMap.adjoint (formOperator_value B) = formOperator_value B ∧
      ∀ u : V, u ≠ 0 →
        0 < RCLike.re (_root_.D05.firstInner (F := F) (formOperator_value B u) u))

def positive_semidefinite_iff : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (B : Specs.D05.M11.Hermitian.sesquilinearForm_value F V),
    (Specs.D05.M11.Hermitian.isHermitian_value B ∧ ∀ u : V, 0 ≤ RCLike.re (B u u)) ↔
    (LinearMap.adjoint (formOperator_value B) = formOperator_value B ∧
      ∀ u : V, 0 ≤ RCLike.re
        (_root_.D05.firstInner (F := F) (formOperator_value B u) u))

def realForm_apply : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V)
    (u v : V), realForm_value B u v = B u v

def real_bilinear_representation : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
    ∃! A : V →ₗ[ℝ] V, ∀ u v, _root_.D05.firstInner (F := ℝ) (A u) v = B u v

def real_symmetric_iff_adjoint : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ u v, B u v = B v u) ↔
      LinearMap.adjoint (formOperator_value (realForm_value B)) =
        formOperator_value (realForm_value B)

end Specs.D05.M11.FormOperator
