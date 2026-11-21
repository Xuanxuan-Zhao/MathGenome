import MathGenome.Internal.Specs.D05.M15.TensorBasis
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
K05.15.tensor_basis, paper.tex:2733. These statements concern algebraic
vector spaces of arbitrary dimension over any field. The elementary tensor
being compared is assumed nonzero, rather than assuming any proportionality
or a choice of decompositions. The finite family is heterogeneous and can have
any positive finite number of factors. Its indices retain repeated factors.
-/
namespace Specs.D05.M15.TensorBasis.SimpleTensors

open scoped TensorProduct BigOperators

/-- Two nonzero elementary binary tensors agree exactly under reciprocal
nonzero rescaling of their corresponding factors. -/
def binary_criterion : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (v v' : V) (w w' : W),
    v ⊗ₜ[K] w ≠ 0 →
      (v ⊗ₜ[K] w = v' ⊗ₜ[K] w' ↔
        ∃ a : K, a ≠ 0 ∧ v' = a • v ∧ w' = a⁻¹ • w)

/-- For any positive finite family of arbitrary-dimensional spaces, equality
of nonzero elementary tensors is equivalent to factorwise nonzero rescalings
whose product is one. No dimension or characteristic condition is imposed. -/
def finite_criterion : Prop :=
  ∀ {K I : Type*} {V : I → Type*} [Field K] [Fintype I] [Nonempty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (v v' : ∀ i, V i),
    PiTensorProduct.tprod K v ≠ 0 →
      (PiTensorProduct.tprod K v = PiTensorProduct.tprod K v' ↔
        ∃ a : I → K, (∀ i, a i ≠ 0) ∧ (∏ i, a i) = 1 ∧
          ∀ i, v' i = a i • v i)

/-- The nonzero hypothesis is essential, already for two one-dimensional
factors: the two displayed zero tensors admit no reciprocal rescaling. -/
def zero_counterexample : Prop :=
  ∀ (K : Type*) [Field K],
    (0 : K) ⊗ₜ[K] (1 : K) = (1 : K) ⊗ₜ[K] (0 : K) ∧
    (0 : K) ⊗ₜ[K] (1 : K) = 0 ∧
    ¬ ∃ a : K, a ≠ 0 ∧ (1 : K) = a • (0 : K) ∧
      (0 : K) = a⁻¹ • (1 : K)

end Specs.D05.M15.TensorBasis.SimpleTensors
