import MathGenome.Internal.Specs.D05.M03.HomDimension
import MathGenome.Internal.Specs.D05.M15.TensorBasis
import MathGenome.Internal.Specs.D05.M15.TensorMaps
import MathGenome.Internal.Specs.D05.M15.TensorPairing
import MathGenome.Internal.Specs.D05.M07.DualMap

/-!
Independent statements for K05.15.tensor_dual_hom, paper.tex:2823–2829.
The canonical Hom-tensor map is the linearization of tensoring maps. Its
isomorphism statement retains all four finite-dimensional hypotheses and
allows zero spaces. Duals mean algebraic duals over the same arbitrary field.
The naturality square is meaningful in all dimensions; finite perfect pairings
then express the equality after identifying the two dual tensor spaces.
-/
namespace Specs.D05.M15.TensorDualHom.EndomorphismActions

open scoped TensorProduct

/-- The specified forward map on elementary tensors. -/
def map_apply : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    TensorProduct.homTensorHomMap (.id K) V W V' W' (S ⊗ₜ[K] T) =
      TensorProduct.map S T

/-- The elementary formula characterizes this linearization uniquely. -/
def map_unique : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (F : ((V →ₗ[K] V') ⊗[K] (W →ₗ[K] W')) →ₗ[K]
      ((V ⊗[K] W) →ₗ[K] (V' ⊗[K] W'))),
    (∀ S T, F (S ⊗ₜ[K] T) = TensorProduct.map S T) →
      F = TensorProduct.homTensorHomMap (.id K) V W V' W'

/-- An isomorphism with the actual canonical map as its forward map. -/
def canonical_isomorphism : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
    ∃ E : ((V →ₗ[K] V') ⊗[K] (W →ₗ[K] W')) ≃ₗ[K]
      ((V ⊗[K] W) →ₗ[K] (V' ⊗[K] W')),
      E.toLinearMap = TensorProduct.homTensorHomMap (.id K) V W V' W'

/-- Both injectivity and surjectivity concern that same canonical map. -/
def canonical_bijective : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W'],
    Function.Bijective (TensorProduct.homTensorHomMap (.id K) V W V' W')

/-- Tensor products of matrix units act as product-basis matrix units.
Rows are target indices and columns are source indices, as upstream. -/
def matrix_unit_action : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    {n m n' m' : ℕ}
    (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (b' : Module.Basis (Fin n') K V') (c' : Module.Basis (Fin m') K W')
    (i : Fin n') (j : Fin n) (k : Fin m') (l : Fin m)
    (a : Fin n) (d : Fin m),
    TensorProduct.homTensorHomMap (.id K) V W V' W'
      (Specs.D05.M03.HomDimension.elementaryMap b b' i j ⊗ₜ[K]
        Specs.D05.M03.HomDimension.elementaryMap c c' k l)
      (b a ⊗ₜ[K] c d) =
      if j = a ∧ l = d then b' i ⊗ₜ[K] c' k else 0

/-- The dual of a tensor map commutes with canonical tensor evaluation. -/
def dual_naturality : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    (TensorProduct.map S T).dualMap.comp (TensorProduct.dualDistrib K V' W') =
      (TensorProduct.dualDistrib K V W).comp (TensorProduct.map S.dualMap T.dualMap)

/-- Under the two perfect pairings, the dual is exactly the tensor of duals.
The forward maps of the pairings are specified, so these are the upstream
canonical identifications rather than arbitrary coordinate isomorphisms. -/
def dual_tensor_map : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    ∃ E : (Module.Dual K V ⊗[K] Module.Dual K W) ≃ₗ[K]
        Module.Dual K (V ⊗[K] W),
    ∃ F : (Module.Dual K V' ⊗[K] Module.Dual K W') ≃ₗ[K]
        Module.Dual K (V' ⊗[K] W'),
      E.toLinearMap = TensorProduct.dualDistrib K V W ∧
      F.toLinearMap = TensorProduct.dualDistrib K V' W' ∧
      (TensorProduct.map S T).dualMap =
        E.toLinearMap.comp ((TensorProduct.map S.dualMap T.dualMap).comp F.symm.toLinearMap)

end Specs.D05.M15.TensorDualHom.EndomorphismActions
