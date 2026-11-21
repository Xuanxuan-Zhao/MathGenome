import MathGenome.Internal.Specs.D05.M14.Penrose.Projections
import MathGenome.Internal.Specs.D05.M14.Penrose.Uniqueness

/-!
Independent statements for K05.14.penrose, paper.tex:2488–2503.
The shared pseudoinverse is constructed by inverse restriction after orthogonal
projection. Dagger is the canonical adjoint, already related to the paper's
first-slot-linear inner product. The spaces may have different dimensions,
including zero; no injectivity or surjectivity assumption is imposed.
-/

namespace Specs.D05.M14.Penrose

/-- Both products are the stated ambient orthogonal projections. -/
def projection_identities : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    T.comp (_root_.D05.pseudoinverse T) =
      _root_.D05.orthogonalProjection T.range ∧
    (_root_.D05.pseudoinverse T).comp T =
      _root_.D05.orthogonalProjection T.ker.orthogonal

/-- The four Penrose equations for the constructed pseudoinverse. -/
def four_identities : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    (T.comp (_root_.D05.pseudoinverse T)).comp T = T ∧
    ((_root_.D05.pseudoinverse T).comp T).comp (_root_.D05.pseudoinverse T) =
      _root_.D05.pseudoinverse T ∧
    LinearMap.adjoint (T.comp (_root_.D05.pseudoinverse T)) =
      T.comp (_root_.D05.pseudoinverse T) ∧
    LinearMap.adjoint ((_root_.D05.pseudoinverse T).comp T) =
      (_root_.D05.pseudoinverse T).comp T

/-- Among all reverse linear maps, the four equations characterize T⁺. -/
def characterization : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (X : W →ₗ[F] V),
    ((T.comp X).comp T = T ∧
      (X.comp T).comp X = X ∧
      LinearMap.adjoint (T.comp X) = T.comp X ∧
      LinearMap.adjoint (X.comp T) = X.comp T) ↔
    X = _root_.D05.pseudoinverse T

end Specs.D05.M14.Penrose
