import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.Specs.D05.M13.SelfAdjoint.DiagonalTests
import MathGenome.Internal.Specs.D05.M13.AdjointKernel
import MathGenome.Internal.Specs.D05.M12.OrthogonalDecomposition

/-!
Independent statements for K05.13.normal_basic, paper.tex:2155–2174 (norm,
kernel, image and orthogonal-decomposition stage). The adjoint, normality and
inner product are the canonical upstream objects. In particular the paper's
first-slot-linear h(u,v) is D05.firstInner u v = inner F v u.
All statements cover real and complex scalars and the zero space. There are
no spectral, positive-dimension, invertibility or extra completeness premises.
-/

namespace Specs.D05.M13.NormalBasic.NormKernel

universe u v

/-- The difference used by the diagonal test is self-adjoint for every T. -/
def commutator_selfAdjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.selfAdjoint
      ((LinearMap.adjoint T).comp T - T.comp (LinearMap.adjoint T))

/-- Scalar-valued norm squares, in the paper's inner-product convention. -/
def commutator_diagonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V) (x : V),
    _root_.D05.firstInner (F := F)
      (((LinearMap.adjoint T).comp T - T.comp (LinearMap.adjoint T)) x) x =
        (‖T x‖ : F) ^ 2 - (‖LinearMap.adjoint T x‖ : F) ^ 2

/-- Normality is exactly equality of the two norms at every vector. -/
def normal_iff_norm_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T ↔ ∀ x : V, ‖T x‖ = ‖LinearMap.adjoint T x‖

/-- Equality is between actual kernel subspaces of V. -/
def ker_eq_ker_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → LinearMap.ker T = LinearMap.ker (LinearMap.adjoint T)

/-- Equality is between actual image subspaces of V. -/
def range_eq_range_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T →
      LinearMap.range T = LinearMap.range (LinearMap.adjoint T)

/-- This identity specifies the orthogonality in the displayed direct sum. -/
def range_eq_orthogonal_ker : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → LinearMap.range T = (LinearMap.ker T).orthogonal

/-- The shared unique-expression predicate plus orthogonality of the summands. -/
def orthogonal_direct_sum : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then LinearMap.range T else LinearMap.ker T) ∧
      ∀ x ∈ LinearMap.ker T, ∀ y ∈ LinearMap.range T,
        _root_.D05.firstInner (F := F) x y = 0

/-- The same decomposition as a unique pair of actual kernel/image vectors. -/
def exists_unique_components : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → ∀ x : V,
      ∃! p : LinearMap.ker T × LinearMap.range T, (p.1 : V) + (p.2 : V) = x

end Specs.D05.M13.NormalBasic.NormKernel
