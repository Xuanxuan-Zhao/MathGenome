import MathGenome.Internal.Specs.D05.M15.TensorDirectSum
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
Independent statements for K05.15.tensor_kernel, paper.tex:2785–2791.

All four spaces are finite-dimensional over the same arbitrary field. The
right-hand tensor subspaces are ranges of the actual natural inclusions;
they are submodules of the appropriate ambient tensor space. In particular,
no equality of incompatible tensor types is asserted. Supremum is subspace
sum. No injectivity, surjectivity, nonzero-space, or characteristic hypothesis
is added to either map formula.
-/

namespace Specs.D05.M15.TensorKernel

open scoped TensorProduct

/-- The natural map realizes the tensor of two subspaces as a subspace. -/
def subspace_tensor_inclusion : Prop :=
  ∀ {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (U : Submodule K V) (P : Submodule K W),
    Function.Injective (TensorProduct.map U.subtype P.subtype)

/-- Image formula, with the right-hand side embedded in `V' ⊗ W'`. -/
def range_tensorMap : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    LinearMap.range (TensorProduct.map S T) =
      LinearMap.range (TensorProduct.map S.range.subtype T.range.subtype)

/-- Kernel formula, with the two summands embedded in `V ⊗ W`. -/
def ker_tensorMap : Prop :=
  ∀ {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    [FiniteDimensional K V] [FiniteDimensional K W]
    [FiniteDimensional K V'] [FiniteDimensional K W']
    (S : V →ₗ[K] V') (T : W →ₗ[K] W'),
    LinearMap.ker (TensorProduct.map S T) =
      LinearMap.range (TensorProduct.map S.ker.subtype (LinearMap.id : W →ₗ[K] W)) ⊔
      LinearMap.range (TensorProduct.map (LinearMap.id : V →ₗ[K] V) T.ker.subtype)

end Specs.D05.M15.TensorKernel
