import MathGenome.Internal.Specs.D05.M14.Pseudoinverse
import MathGenome.Internal.Specs.D05.M13.Adjoint

/-!
Independent statements for the projection stage of K05.14.penrose,
paper.tex:2488–2503. The shared pseudoinverse is the inverse restriction
following projection, not a map assumed to satisfy the Penrose equations.
The scalar field is real or complex, uniformly expressed by `RCLike`.
Domain and codomain are independent types, with no nonzero-dimension premise.
`LinearMap.adjoint` is the canonical adjoint for the shared first-slot-linear
inner product, as specified and proved in K05.13.adjoint.
-/

namespace Specs.D05.M14.Penrose.Projections

/-- TT⁺ is the orthogonal projection onto the image. -/
def map_comp_pseudoinverse : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W),
    T.comp (_root_.D05.pseudoinverse T) = _root_.D05.orthogonalProjection T.range

/-- T⁺T is the orthogonal projection onto the perpendicular of the kernel. -/
def pseudoinverse_comp_map : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W),
    (_root_.D05.pseudoinverse T).comp T =
      _root_.D05.orthogonalProjection T.ker.orthogonal

/-- The first Penrose equation, TT⁺T = T. -/
def map_pseudoinverse_map : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W),
    (T.comp (_root_.D05.pseudoinverse T)).comp T = T

/-- The second Penrose equation, T⁺TT⁺ = T⁺. -/
def pseudoinverse_map_pseudoinverse : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W),
    ((_root_.D05.pseudoinverse T).comp T).comp (_root_.D05.pseudoinverse T) =
      _root_.D05.pseudoinverse T

/-- The third Penrose equation: TT⁺ is self-adjoint. -/
def map_comp_pseudoinverse_adjoint : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W),
    LinearMap.adjoint (T.comp (_root_.D05.pseudoinverse T)) =
      T.comp (_root_.D05.pseudoinverse T)

/-- The fourth Penrose equation: T⁺T is self-adjoint. -/
def pseudoinverse_comp_map_adjoint : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W),
    LinearMap.adjoint ((_root_.D05.pseudoinverse T).comp T) =
      (_root_.D05.pseudoinverse T).comp T

/-- For the zero map, the pseudoinverse and both products are zero. -/
def zero_map : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    _root_.D05.pseudoinverse (0 : V →ₗ[F] W) = 0 ∧
    (0 : V →ₗ[F] W).comp (_root_.D05.pseudoinverse (0 : V →ₗ[F] W)) = 0 ∧
    (_root_.D05.pseudoinverse (0 : V →ₗ[F] W)).comp (0 : V →ₗ[F] W) = 0

end Specs.D05.M14.Penrose.Projections
