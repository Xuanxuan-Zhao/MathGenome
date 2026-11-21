import MathGenome.Internal.Specs.D05.M13.ComplexSpectral
import MathGenome.Internal.Specs.D05.M13.RealNormalBlocks
import MathGenome.Internal.Specs.D05.M08.Charpoly

/-! Independent statements for K05.13.normal_classification,
paper.tex:2343–2353. Domain and codomain are separately quantified; neither
positive nor equal dimension is assumed. The isometric equivalence includes
surjectivity and is unitary over ℂ, orthogonal over ℝ. -/
noncomputable section
namespace Specs.D05.M13.NormalClassification
universe u v w

/-- Forward implication, without any normality requirement. -/
def charpoly_of_intertwiner : Prop :=
  ∀ {F : Type u} [RCLike F] {V : Type v} {W : Type w}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace F V] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] V) (S : W →ₗ[F] W) (U : V ≃ₗᵢ[F] W),
    (∀ x, U (T x) = S (U x)) → T.charpoly = S.charpoly

/-- Polynomial equality itself forces dimension equality. -/
def dimension_of_charpoly : Prop :=
  ∀ {F : Type u} [Field F] {V : Type v} {W : Type w}
    [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] V) (S : W →ₗ[F] W),
    T.charpoly = S.charpoly → Module.finrank F V = Module.finrank F W

/-- Complex normal classification, including the empty eigenvalue list. -/
def complex_classification : Prop :=
  ∀ {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ V] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (T : V →ₗ[ℂ] V) (S : W →ₗ[ℂ] W),
    _root_.D05.normalOperator T → _root_.D05.normalOperator S →
    ((∃ U : V ≃ₗᵢ[ℂ] W, ∀ x, U (T x) = S (U x)) ↔ T.charpoly = S.charpoly)

/-- Real normal classification; the intertwiner is an orthogonal equivalence. -/
def real_classification : Prop :=
  ∀ {V : Type u} {W : Type v}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℝ V] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (T : V →ₗ[ℝ] V) (S : W →ₗ[ℝ] W),
    _root_.D05.normalOperator T → _root_.D05.normalOperator S →
    ((∃ U : V ≃ₗᵢ[ℝ] W, ∀ x, U (T x) = S (U x)) ↔ T.charpoly = S.charpoly)
end Specs.D05.M13.NormalClassification
