import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.LieStableSubspaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.TensorAndDual

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs

open LinearAlgebraicGroups.RationalRepresentations

/-- The graph of a linear map is a subcomodule of the rational direct sum exactly
when the map is equivariant. For each tangent vector, its graph is invariant under
the differentiated direct sum action exactly when it intertwines the two operators. -/
def DifferentiationGraphCriterion : Prop :=
  ∀ {k V W : Type u} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (σ : RightComodule k A W),
    ∃ τ : RightComodule k A (V × W),
      IsEquivariant A τ ρ (LinearMap.fst k V W) ∧
      IsEquivariant A τ σ (LinearMap.snd k V W) ∧
      (∀ f : V →ₗ[k] W, τ.IsSubcomodule f.graph ↔ IsEquivariant A ρ σ f) ∧
      ∀ (f : V →ₗ[k] W) (x : HopfTangentPoint A),
        (∀ v : f.graph, differentiatedCoaction A τ x v ∈ f.graph) ↔
        f.comp (differentiatedCoaction A ρ x) = (differentiatedCoaction A σ x).comp f

/-- Differentiation identifies the equivariant linear maps between two finite-dimensional
rational representations of a connected affine algebraic group in characteristic zero. -/
def FullyFaithfulDifferentiation : Prop :=
  ∀ {k V W : Type u} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] [ConnectedSpace (PrimeSpectrum A)]
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (f : V →ₗ[k] W),
    IsEquivariant A ρ σ f ↔ ∀ x : Lie k (specGroup A),
      f.comp (differentiatedCoaction A ρ (tangentPointOfLie A x)) =
        (differentiatedCoaction A σ (tangentPointOfLie A x)).comp f

/-- The same identification on the Lie algebra of an affine algebraic group given
with an isomorphism from its coordinate Hopf presentation. -/
def FullyFaithfulDifferentiationOfPresentation : Prop :=
  ∀ {k V W : Type u} [Field k] [CharZero k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (f : V →ₗ[k] W),
    IsEquivariant A ρ σ f ↔ ∀ x : Lie k G.val,
      f.comp (differentiatedCoaction A ρ (tangentPointOfLie A (mapPointKernel e.inv x))) =
        (differentiatedCoaction A σ (tangentPointOfLie A (mapPointKernel e.inv x))).comp f

end LinearAlgebraicGroups.Specs
