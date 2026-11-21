import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.Specs.D05.M12.OrthogonalDecomposition
import MathGenome.Internal.Specs.D05.M13.AdjointLaws

/-!
Independent statements for K05.13.adjoint_kernel, paper.tex:2103–2117.
The adjoint, kernel, image, and orthogonal complement are the upstream
canonical Mathlib objects. With `D05.firstInner u v = inner F v u`,
`Submodule.orthogonal` is exactly the paper's perpendicular subspace.
Rank is the natural-number dimension of the image, as in K05.03.image.
Both spaces are finite dimensional over a real or complex scalar field;
there is no nonzero, equal-dimension, or invertibility hypothesis.
-/

namespace Specs.D05.M13.AdjointKernel

universe u v w

/-- The adjoint kernel is the perpendicular of the image, inside W. -/
def ker_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ T : V →ₗ[F] W,
    LinearMap.ker (_root_.LinearMap.adjoint T) = (LinearMap.range T).orthogonal

/-- The adjoint image is the perpendicular of the kernel, inside V. -/
def range_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ T : V →ₗ[F] W,
    LinearMap.range (_root_.LinearMap.adjoint T) = (LinearMap.ker T).orthogonal

/-- The two images have equal dimensions, for arbitrary rectangular maps. -/
def rank_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ T : V →ₗ[F] W,
    Module.finrank F (LinearMap.range (_root_.LinearMap.adjoint T)) =
      Module.finrank F (LinearMap.range T)

/-- Composition with the adjoint preserves the original kernel. -/
def ker_adjoint_comp_self : Prop :=
  ∀ {F : Type u} {V : Type v} {W : Type w} [RCLike F]
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
  ∀ T : V →ₗ[F] W,
    LinearMap.ker ((_root_.LinearMap.adjoint T).comp T) = LinearMap.ker T

end Specs.D05.M13.AdjointKernel
