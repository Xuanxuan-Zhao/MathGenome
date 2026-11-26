import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import Mathlib.LinearAlgebra.Coevaluation

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u
noncomputable section

namespace LinearAlgebraicGroups

namespace RationalRepresentations

variable {k V W : Type u} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- The tensor coaction first collects the two vector factors, then multiplies
the two coordinate functions. -/
def tensorCoactionMap (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    V ⊗[k] W →ₗ[k] (V ⊗[k] W) ⊗[k] A :=
  ((LinearMap.mul' k A).lTensor (V ⊗[k] W)).comp
    ((TensorProduct.tensorTensorTensorComm k V A W A).toLinearMap.comp
      (TensorProduct.map ρ.coaction σ.coaction))

/-- The coaction equation for an equivariant linear map. -/
def IsEquivariant (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (σ : RightComodule k A W) (f : V →ₗ[k] W) : Prop :=
  (f.rTensor A).comp ρ.coaction = σ.coaction.comp f

end RationalRepresentations

namespace Specs.RationalOperations

open LinearAlgebraicGroups.RationalRepresentations

/-- The tensor product on finite-dimensional representations has the diagonal
coaction, and equivariant linear maps can be tensored. -/
def TensorProductOperation : Prop :=
  ∀ {k V W V' W' : Type u} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    (A : HopfAlgebraCategory k)
    (ρ : RightComodule k A V) (σ : RightComodule k A W)
    (ρ' : RightComodule k A V') (σ' : RightComodule k A W'),
    ∃ (τ : RightComodule k A (V ⊗[k] W)) (τ' : RightComodule k A (V' ⊗[k] W')),
      τ.coaction = tensorCoactionMap A ρ σ ∧ τ'.coaction = tensorCoactionMap A ρ' σ' ∧
      ∀ (f : V →ₗ[k] V') (g : W →ₗ[k] W'),
        IsEquivariant A ρ ρ' f → IsEquivariant A σ σ' g →
        IsEquivariant A τ τ' (TensorProduct.map f g)

/-- A trivial one-dimensional representation is a left and right tensor unit
via the usual multiplication maps of vector spaces. -/
def TensorUnit : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V),
    ∃ (unit : RightComodule k A k)
      (l : RightComodule k A (k ⊗[k] V)) (r : RightComodule k A (V ⊗[k] k)),
      unit.coaction = trivialLinearMap A ∧
      l.coaction = tensorCoactionMap A unit ρ ∧
      r.coaction = tensorCoactionMap A ρ unit ∧
      IsEquivariant A l ρ (TensorProduct.lid k V).toLinearMap ∧
      IsEquivariant A r ρ (TensorProduct.rid k V).toLinearMap

/-- The dual uses the inverse transpose in every basis. The canonical pairing and
the canonical map from the tensor unit to the endomorphism tensor are equivariant. -/
def Duality : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [Fintype ι] [DecidableEq ι]
    (A : HopfAlgebraCategory k) (b : Module.Basis ι k V) (ρ : RightComodule k A V),
    ∃ (σ : RightComodule k A (Module.Dual k V)) (unit : RightComodule k A k)
      (l : RightComodule k A (Module.Dual k V ⊗[k] V))
      (r : RightComodule k A (V ⊗[k] Module.Dual k V)),
      (∀ i j, coefficients A b.dualBasis σ i j = HopfAlgebra.antipode k (coefficients A b ρ j i)) ∧
      (∀ (R : TestAlgebra k) (g : A →ₐ[k] R), ∃ m : Matrix.GeneralLinearGroup ι R,
        m.val = g.mapMatrix (coefficients A b ρ) ∧
        g.mapMatrix (coefficients A b.dualBasis σ) = (m⁻¹).val.transpose) ∧
      unit.coaction = trivialLinearMap A ∧
      l.coaction = tensorCoactionMap A σ ρ ∧ r.coaction = tensorCoactionMap A ρ σ ∧
      IsEquivariant A l unit (contractLeft k V) ∧ IsEquivariant A unit r (coevaluation k V)

/-- Restriction along the group map dual to a Hopf map composes the coaction with
the pullback of coordinate functions on the second factor. -/
def Restriction : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {A B : HopfAlgebraCategory k} (a : A ⟶ B) (ρ : RightComodule k A V),
    ∃ σ : RightComodule k B V,
      σ.coaction = (a.hom.toAlgHom.toLinearMap.lTensor V).comp ρ.coaction

/-- Given coordinate models for two affine groups, restriction of a rational
representation by a group scheme morphism is the indicated coaction composition. -/
def SchemeRestriction : Prop :=
  ∀ {k V ι : Type u} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    {A B : HopfAlgebraCategory k} {G H : AffineGroupCategory k}
    (s : (affineHopfSpec k).obj (op A) ≅ G) (t : (affineHopfSpec k).obj (op B) ≅ H)
    (f : H ⟶ G) (L : GroupScheme k) (b : Module.Basis ι k V)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι),
    ∃ (a : A ⟶ B)
      (E : Specs.RationalRepresentations.representation G L l ≃ RightComodule k A V)
      (F : Specs.RationalRepresentations.representation H L l ≃ RightComodule k B V)
      (e : convolutionPoints A ≅ (groupPointsFunctor k).obj G.val)
      (d : convolutionPoints B ≅ (groupPointsFunctor k).obj H.val),
      t.hom ≫ f = (affineHopfSpec k).map a.op ≫ s.hom ∧
      (∀ (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)),
        (e.hom.app R g : Points G.val.X R).left =
          Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ s.hom.hom.hom.hom.left) ∧
      (∀ (R : TestAlgebra k) (g : WithConv (B →ₐ[k] R)),
        (d.hom.app R g : Points H.val.X R).left =
          Spec.map (CommRingCat.ofHom g.ofConv.toRingHom) ≫ t.hom.hom.hom.hom.left) ∧
      (∀ ψ, coefficients A b (E ψ) = universalMatrix A G L e l ψ) ∧
      (∀ ψ, coefficients B b (F ψ) = universalMatrix B H L d l ψ) ∧
      ∀ ψ, (F (f.hom ≫ ψ)).coaction =
        (a.hom.toAlgHom.toLinearMap.lTensor V).comp (E ψ).coaction

/-- The invariant subspace is the coaction equalizer, and it consists exactly
of the vectors fixed at every algebra-valued point. -/
def InvariantVectors : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
    (A : HopfAlgebraCategory k) (ρ : RightComodule k A V) (v : V),
    (v ∈ invariants A ρ ↔ ρ.coaction v = v ⊗ₜ[k] (1 : A)) ∧
    ((∀ (R : TestAlgebra k) (g : A →ₐ[k] R), evaluate A ρ g v = v ⊗ₜ[k] (1 : R)) ↔
      v ∈ invariants A ρ)

end Specs.RationalOperations
end LinearAlgebraicGroups
