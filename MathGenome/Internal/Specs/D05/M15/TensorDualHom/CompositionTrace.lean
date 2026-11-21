import MathGenome.Internal.Specs.D05.M15.TensorDualHom
import MathGenome.Internal.Specs.D05.M15.TensorMaps

/-!
Independent specifications for paper.tex:2809–2814, the finite-dimensional
composition product and its unit. The trace pairing and the unrestricted
finite-rank assertion in the subsequent passages are separate obligations.

`phi` is the upstream canonical map, not a new identification. Transporting
composition defines a bilinear operation; its required elementary formula and
unit expansion below specify the manuscript's multiplication and normalization.
No positivity, characteristic restriction, nonzero dimension or chosen basis
is part of these constructions.
-/

namespace Specs.D05.M15.TensorDualHom.CompositionTrace

open scoped TensorProduct
open Specs.D05.M15.TensorDualHom (phi)

/-- Composition transported through the canonical tensor–Hom equivalence.
The nested linear-map type asserts bilinearity in the two tensors. -/
noncomputable def compositionProduct (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    (Module.Dual K V ⊗[K] V) →ₗ[K]
      (Module.Dual K V ⊗[K] V) →ₗ[K] (Module.Dual K V ⊗[K] V) :=
  (((LinearMap.llcomp K V V V).compl₂ (phi K V V)).comp
    (phi K V V)).compr₂ (dualTensorHomEquiv K V V).symm.toLinearMap

def compositionProduct_type :=
  (K V : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → (Module.Dual K V ⊗[K] V) →ₗ[K]
      (Module.Dual K V ⊗[K] V) →ₗ[K] (Module.Dual K V ⊗[K] V)

noncomputable def compositionProduct_value : compositionProduct_type := @compositionProduct

/-- The canonical preimage of the identity, defined without a basis. -/
noncomputable def unitTensor (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : Module.Dual K V ⊗[K] V :=
  (dualTensorHomEquiv K V V).symm LinearMap.id

def unitTensor_type :=
  (K V : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    [FiniteDimensional K V] → Module.Dual K V ⊗[K] V

noncomputable def unitTensor_value : unitTensor_type := @unitTensor

/-- The multiplication order, with the scalar acting on the dual factor. -/
def product_tmul : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g : Module.Dual K V) (v w : V),
    compositionProduct K V (f ⊗ₜ[K] v) (g ⊗ₜ[K] w) = (f w • g) ⊗ₜ[K] v

/-- Applying Phi gives exactly composition of endomorphisms. -/
def phi_product : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s t : Module.Dual K V ⊗[K] V),
    phi K V V (compositionProduct K V s t) = (phi K V V s).comp (phi K V V t)

/-- The formula on elementary tensors determines the bilinear product uniquely. -/
def product_unique : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (B : (Module.Dual K V ⊗[K] V) →ₗ[K]
      (Module.Dual K V ⊗[K] V) →ₗ[K] (Module.Dual K V ⊗[K] V)),
    (∀ f g v w, B (f ⊗ₜ[K] v) (g ⊗ₜ[K] w) = (f w • g) ⊗ₜ[K] v) →
      B = compositionProduct K V

/-- Associativity on all tensors, not only on elementary ones. -/
def product_assoc : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (r s t : Module.Dual K V ⊗[K] V),
    compositionProduct K V (compositionProduct K V r s) t =
      compositionProduct K V r (compositionProduct K V s t)

/-- The unit maps to the actual identity endomorphism. -/
def phi_unit : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], phi K V V (unitTensor K V) = LinearMap.id

/-- This property characterizes the unit tensor uniquely. -/
def unit_characterization : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (t : Module.Dual K V ⊗[K] V),
    phi K V V t = LinearMap.id ↔ t = unitTensor K V

def unit_left : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (t : Module.Dual K V ⊗[K] V),
    compositionProduct K V (unitTensor K V) t = t

def unit_right : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (t : Module.Dual K V ⊗[K] V),
    compositionProduct K V t (unitTensor K V) = t

/-- Every finite basis, including an empty basis, gives the same unit expansion. -/
def unit_basis : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I] (b : Module.Basis I K V),
    unitTensor K V = ∑ i, b.coord i ⊗ₜ[K] b i

/-- No identification of the two index types is required to change basis. -/
def unit_basis_independent : Prop :=
  ∀ {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I] [Fintype J]
    (b : Module.Basis I K V) (c : Module.Basis J K V),
    (∑ i, b.coord i ⊗ₜ[K] b i) = ∑ j, c.coord j ⊗ₜ[K] c j

end Specs.D05.M15.TensorDualHom.CompositionTrace
