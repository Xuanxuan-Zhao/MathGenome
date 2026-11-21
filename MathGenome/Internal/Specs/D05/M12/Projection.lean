import MathGenome.Internal.Specs.D05.M12.FourierParseval
import MathGenome.Internal.Specs.D05.M12.OrthogonalDecomposition
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Independent statements for K05.12.projection, paper.tex:2023–2031.
Only the subspace is finite dimensional. The ambient space need be neither
finite dimensional nor complete. The endomorphism has values in the ambient
space, so its range and kernel are submodules of that same space.
The component characterization bridges the library construction to the paper's
unique-decomposition definition. All Fourier coefficients use `D05.firstInner`.
-/

noncomputable section

namespace D05

/-- Orthogonal projection onto a finite-dimensional subspace, as an ambient
linear endomorphism. Completeness of the subspace follows from its dimension. -/
def orthogonalProjection {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (U : Submodule F V) [FiniteDimensional F U] : V →ₗ[F] V := by
  letI : CompleteSpace U := FiniteDimensional.complete F U
  exact U.starProjection.toLinearMap

end D05

namespace Specs.D05.M12.Projection

universe u v

def projection_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → (U : Submodule F V) → [FiniteDimensional F U] → V →ₗ[F] V

def projection_value : projection_type.{u, v} := fun {F} _ _ _ _ U _ => by
  letI : CompleteSpace U := FiniteDimensional.complete F U
  exact U.starProjection.toLinearMap

/-- Membership and an orthogonal residual characterize the unique component. -/
def component_characterization : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (v u : V),
    _root_.D05.orthogonalProjection U v = u ↔ u ∈ U ∧ v - u ∈ U.orthogonal

/-- Explicit identification with the component in any decomposition from the
preceding theorem, including the existence and uniqueness of that pair. -/
def unique_components : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (v : V),
    ∃! p : U × U.orthogonal,
      (p.1 : V) + (p.2 : V) = v ∧ _root_.D05.orthogonalProjection U v = (p.1 : V)

/-- Any finite orthonormal algebraic basis of U gives this ambient formula.
An empty basis (U = 0) is allowed. -/
def basis_formula : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] (U : Submodule F V) [FiniteDimensional F U]
    (b : Module.Basis I F U), _root_.D05.orthonormalFamily (F := F) b → ∀ v : V,
    _root_.D05.orthogonalProjection U v =
      ∑ j, _root_.D05.firstInner (F := F) v (b j : V) • (b j : V)

/-- The two bases can have different index types, orders, and cardinal witnesses. -/
def basis_independence : Prop :=
  ∀ {F V I J : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] [Fintype J] (U : Submodule F V) [FiniteDimensional F U]
    (b : Module.Basis I F U) (c : Module.Basis J F U),
    _root_.D05.orthonormalFamily (F := F) b →
    _root_.D05.orthonormalFamily (F := F) c → ∀ v : V,
      (∑ i, _root_.D05.firstInner (F := F) v (b i : V) • (b i : V)) =
        ∑ j, _root_.D05.firstInner (F := F) v (c j : V) • (c j : V)

def map_add : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (x y : V),
    _root_.D05.orthogonalProjection U (x + y) =
      _root_.D05.orthogonalProjection U x + _root_.D05.orthogonalProjection U y

def map_smul : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (a : F) (v : V),
    _root_.D05.orthogonalProjection U (a • v) = a • _root_.D05.orthogonalProjection U v

def fixes_subspace : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (u : V), u ∈ U →
    _root_.D05.orthogonalProjection U u = u

def idempotent : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U],
    (_root_.D05.orthogonalProjection U).comp (_root_.D05.orthogonalProjection U) =
      _root_.D05.orthogonalProjection U

def range_eq : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U],
    LinearMap.range (_root_.D05.orthogonalProjection U) = U

def kernel_eq : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U],
    LinearMap.ker (_root_.D05.orthogonalProjection U) = U.orthogonal

/-- The source's self-adjointness identity; it makes sense even when no global
adjoint operation on arbitrary endomorphisms of V is available. -/
def self_adjoint_identity : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (U : Submodule F V) [FiniteDimensional F U] (x y : V),
    _root_.D05.firstInner (F := F) (_root_.D05.orthogonalProjection U x) y =
      _root_.D05.firstInner (F := F) x (_root_.D05.orthogonalProjection U y)

end Specs.D05.M12.Projection
