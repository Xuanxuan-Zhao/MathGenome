import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import Mathlib.Algebra.DirectSum.Module

open CategoryTheory
open scoped DirectSum TensorProduct

universe u

namespace LinearAlgebraicGroups
namespace WeightDecomposition

noncomputable section

variable {k M V W : Type u} [Field k] [CommGroup M]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

local notation "A" => MonoidAlgebra k M
local notation "e" => MonoidAlgebra.of k M

/-- The subspace on which the coaction of `D(M)` is given by the character `m`.
The character group is written multiplicatively. -/
def weightSpace (ρ : RightComodule k A V) (m : M) : Submodule k V :=
  LinearMap.ker (ρ.coaction - (TensorProduct.mk k V A).flip (e m))

theorem mem_weightSpace {ρ : RightComodule k A V} {m : M} {v : V} :
    v ∈ weightSpace ρ m ↔ ρ.coaction v = v ⊗ₜ[k] e m := by
  simp [weightSpace, sub_eq_zero]

/-- The tensor coaction map multiplies the two coordinate functions after placing
the vector factors together. -/
def tensorCoactionMap (ρ : RightComodule k A V) (σ : RightComodule k A W) :
    V ⊗[k] W →ₗ[k] (V ⊗[k] W) ⊗[k] A :=
  (LinearMap.mul' k A).lTensor (V ⊗[k] W) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k V A W A).toLinearMap ∘ₗ
    TensorProduct.map ρ.coaction σ.coaction

/-- Evaluate the functional factor of a tensor on a vector. -/
def evaluateDualTensor : (Module.Dual k V ⊗[k] A) →ₗ[k] V →ₗ[k] A :=
  TensorProduct.lift LinearMap.smulRightₗ

/-- Apply a functional to the vector factor of a tensor. -/
def evaluateVectorTensor : (V ⊗[k] A) →ₗ[k] Module.Dual k V →ₗ[k] A :=
  TensorProduct.lift (LinearMap.smulRightₗ.comp (Module.Dual.eval k V))

end

end WeightDecomposition

namespace Specs.WeightDecomposition

open LinearAlgebraicGroups.WeightDecomposition

open DiagonalizableGroups (groupAlgebra)

/-- Rational representations of the actual group scheme `D(M)` use the same
right coactions as the weight-space statements below. -/
def DiagonalRepresentationComparison : Prop :=
  ∀ {k M V ι : Type u} [Field k] [CommGroup M] [Group.FG M]
    [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k V) (L : GroupScheme k)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι),
    let D := DiagonalizableGroups.diagonalGroup k M
    let G : AffineGroupCategory k := ⟨D.val, D.property.1⟩
    ∃ (e : convolutionPoints (groupAlgebra k M) ≅ (groupPointsFunctor k).obj D.val)
      (E : RationalRepresentations.representation G L l ≃ RightComodule k (groupAlgebra k M) V),
      ∀ f, LinearAlgebraicGroups.RationalRepresentations.coefficients (groupAlgebra k M) b (E f) =
        LinearAlgebraicGroups.RationalRepresentations.universalMatrix (groupAlgebra k M) G L e l f

/-- The canonical sum of the weight inclusions is an isomorphism. -/
def InternalWeightSum : Prop := by
  classical
  exact ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V]
    (ρ : RightComodule k (groupAlgebra k M) V), DirectSum.IsInternal (weightSpace ρ)

def FiniteWeights : Prop :=
  ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RightComodule k (groupAlgebra k M) V),
    {m | weightSpace ρ m ≠ ⊥}.Finite

/-- The trivial character is the identity in the multiplicative notation for `M`. -/
def Invariants : Prop :=
  ∀ {k M V : Type u} [Field k] [CommGroup M] [AddCommGroup V] [Module k V]
    (ρ : RightComodule k (groupAlgebra k M) V),
    LinearAlgebraicGroups.RationalRepresentations.invariants (groupAlgebra k M) ρ = weightSpace ρ 1

/-- Equivariant maps restrict to each weight, and the direct sum of these
restrictions commutes with the canonical sum maps. -/
def Functoriality : Prop := by
  classical
  exact ∀ {k M V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RightComodule k (groupAlgebra k M) V) (σ : RightComodule k (groupAlgebra k M) W)
    (f : V →ₗ[k] W) (_ : (f.rTensor (groupAlgebra k M)).comp ρ.coaction = σ.coaction.comp f),
    ∃ F : ∀ m, weightSpace ρ m →ₗ[k] weightSpace σ m,
      (∀ m (v : weightSpace ρ m), (F m v : W) = f v) ∧
      (DirectSum.coeLinearMap (weightSpace σ)).comp (DirectSum.lmap F) =
        f.comp (DirectSum.coeLinearMap (weightSpace ρ))

/-- A tensor product weight space is the sum of the images of the tensor
products of weight spaces with the given product of characters. -/
def TensorWeights : Prop :=
  ∀ {k M V W : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : RightComodule k (groupAlgebra k M) V) (σ : RightComodule k (groupAlgebra k M) W),
    ∃ τ : RightComodule k (groupAlgebra k M) (V ⊗[k] W),
      τ.coaction = tensorCoactionMap ρ σ ∧
      ∀ m, weightSpace τ m =
        ⨆ p : {p : M × M // p.1 * p.2 = m},
          LinearMap.range (TensorProduct.mapIncl (weightSpace ρ p.val.1) (weightSpace σ p.val.2))

/-- For the contragredient coaction, restriction identifies the weight-`m`
functionals with the dual of the weight-`m⁻¹` space. -/
def DualWeights : Prop :=
  ∀ {k M V : Type u} [Field k] [CommGroup M]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RightComodule k (groupAlgebra k M) V),
    ∃ τ : RightComodule k (groupAlgebra k M) (Module.Dual k V),
      (∀ (f : Module.Dual k V) (v : V),
        evaluateDualTensor (τ.coaction f) v =
          HopfAlgebra.antipode k (evaluateVectorTensor (ρ.coaction v) f)) ∧
      ∀ m, ∃ E : weightSpace τ m ≃ₗ[k] Module.Dual k (weightSpace ρ m⁻¹),
        ∀ (f : weightSpace τ m) (v : weightSpace ρ m⁻¹), E f v = (f : Module.Dual k V) v

end Specs.WeightDecomposition
end LinearAlgebraicGroups
