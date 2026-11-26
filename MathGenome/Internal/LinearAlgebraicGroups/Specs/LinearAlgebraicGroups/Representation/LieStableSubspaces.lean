import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.IdentityTangent

open AlgebraicGeometry CategoryTheory WithConv Bialgebra
open Specs.AdvCommAlg.Differentials.Tangent
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

/-- The identity tangent vector in the coordinate model of an affine group. -/
abbrev HopfTangentPoint (A : HopfAlgebraCategory k) :=
  PointLifts k A k (counitAlgHom k A)

/-- Differentiate a coaction by taking the coefficient of the dual-number parameter. -/
def differentiatedCoaction (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (x : HopfTangentPoint A) : V →ₗ[k] V :=
  ((TensorProduct.rid k V).toLinearMap.comp
    ((TrivSqZeroExt.sndHom k k).lTensor V)).comp
      (RationalRepresentations.evaluate A ρ x.val)

/-- A point belongs to the stabilizer if it and its inverse send the subspace into
its scalar extension. These two inclusions express preservation as a submodule. -/
def PreservesSubspace (A : HopfAlgebraCategory k) (ρ : RightComodule k A V)
    (W : Submodule k V) (R : TestAlgebra k) (g : (convolutionPoints A).obj R) : Prop :=
  (∀ v : W, RationalRepresentations.evaluate A ρ g.ofConv v ∈
    LinearMap.range (W.subtype.rTensor R)) ∧
  (∀ v : W, RationalRepresentations.evaluate A ρ (g⁻¹).ofConv v ∈
    LinearMap.range (W.subtype.rTensor R))

/-- Identify the Lie algebra of the spectrum with its counit lifts using affine duality. -/
def tangentPointOfLie (A : HopfAlgebraCategory k) (x : Specs.Lie k (specGroup A)) :
    HopfTangentPoint A :=
  hopfKernelLifts A (mapDualKernel
    (NatIso.ofComponents (fun R : TestAlgebra k =>
      (Spec.mapMulEquiv (R := k) (S := A) (T := R)).toGrpIso) (by
        intro R S a
        apply GrpCat.ext
        intro f
        apply Over.OverMorphism.ext
        exact Spec.map_comp (CommRingCat.ofHom f.ofConv.toRingHom)
          (CommRingCat.ofHom a.hom.toRingHom))).inv x)

namespace Specs

/-- The scheme stabilizer is a closed subgroup and its Lie algebra embeds in
the ambient Lie algebra with image given by the differentiated condition. -/
def LieSubspaceStabilizer : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (W : Submodule k V),
    ∃ (I : Ideal A) (_ : I.IsHopfIdeal k),
      let q := hopfQuotientMap A I
      let i := specGroupMap q
      IsClosedImmersion i.hom.hom.left ∧
      (∀ (R : TestAlgebra k) (g : (convolutionPoints A).obj R),
        PreservesSubspace A ρ W R g ↔
          ∃ h : hopfQuotient A I →ₐ[k] R, h.comp q.hom.toAlgHom = g.ofConv) ∧
      Function.Injective (mapPointKernel i) ∧
      Set.range (mapPointKernel i) = {x | ∀ v : W,
        differentiatedCoaction A ρ (tangentPointOfLie A x) v ∈ W}

/-- For a connected affine algebraic group in characteristic zero, a rational
subspace is stable if and only if the differentiated action preserves it. -/
def LieStableSubspaces : Prop :=
  ∀ {k V : Type u} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (A : HopfAlgebraCategory k) [Algebra.FiniteType k A]
    [ConnectedSpace (PrimeSpectrum A)] (ρ : RightComodule k A V) (W : Submodule k V),
    ρ.IsSubcomodule W ↔ ∀ (x : Lie k (specGroup A)) (v : W),
      differentiatedCoaction A ρ (tangentPointOfLie A x) v ∈ W

/-- Transport the criterion to the given affine algebraic group along its
coordinate Hopf presentation. -/
def LieStableSubspacesOfPresentation : Prop :=
  ∀ {k V : Type u} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (G : AffineAlgebraicGroup k) [ConnectedSpace G.val.X.left]
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val)
    (ρ : RightComodule k A V) (W : Submodule k V),
    ρ.IsSubcomodule W ↔ ∀ (x : Lie k G.val) (v : W),
      differentiatedCoaction A ρ (tangentPointOfLie A (mapPointKernel e.inv x)) v ∈ W

/-- The assertion also holds for a graph in a rational direct sum. -/
def LieStableGraphs : Prop :=
  ∀ {k V U : Type u} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A] [ConnectedSpace (PrimeSpectrum A)]
    (ρ : RightComodule k A (V × U)) (f : V →ₗ[k] U),
    ρ.IsSubcomodule f.graph ↔ ∀ (x : Lie k (specGroup A)) (v : f.graph),
      differentiatedCoaction A ρ (tangentPointOfLie A x) v ∈ f.graph

end Specs
end
end LinearAlgebraicGroups
