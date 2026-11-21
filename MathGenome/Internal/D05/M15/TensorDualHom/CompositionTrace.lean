import MathGenome.Internal.Specs.D05.M15.TensorDualHom.CompositionTrace
import MathGenome.Internal.D05.M15.TensorDualHom
import MathGenome.Internal.D05.M15.TensorMaps

/-! The composition algebra on dual-vector tensors (paper.tex:2809–2814). -/

namespace D05.M15.TensorDualHom.CompositionTrace

open scoped TensorProduct
open D05.M15.TensorDualHom (phi)

/-- The bilinear composition product, using the upstream canonical Phi. -/
noncomputable abbrev compositionProduct (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :=
  Specs.D05.M15.TensorDualHom.CompositionTrace.compositionProduct K V

/-- The canonical tensor representing the identity. -/
noncomputable abbrev unitTensor (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :=
  Specs.D05.M15.TensorDualHom.CompositionTrace.unitTensor K V

/-- Transport gives composition on every tensor. -/
theorem phi_product : Specs.D05.M15.TensorDualHom.CompositionTrace.phi_product := by
  intro K V _ _ _ _ s t
  exact (dualTensorHomEquiv K V V).apply_symm_apply _

/-- Evaluating both endomorphisms proves the manuscript's rank-one formula. -/
theorem product_tmul : Specs.D05.M15.TensorDualHom.CompositionTrace.product_tmul := by
  intro K V _ _ _ _ f g v w
  apply (dualTensorHomEquiv K V V).injective
  change phi K V V (compositionProduct K V (f ⊗ₜ[K] v) (g ⊗ₜ[K] w)) =
    phi K V V ((f w • g) ⊗ₜ[K] v)
  rw [phi_product]
  ext x
  simp only [LinearMap.comp_apply, dualTensorHom_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_smul]
  rw [mul_comm]

/-- Spanning in each argument proves uniqueness of the bilinear extension. -/
theorem product_unique : Specs.D05.M15.TensorDualHom.CompositionTrace.product_unique := by
  intro K V _ _ _ _ B hB
  apply TensorProduct.ext'
  intro f v
  apply TensorProduct.ext'
  intro g w
  exact (hB f g v w).trans (product_tmul f g v w).symm

/-- Associativity is pulled back along the injective canonical Phi. -/
theorem product_assoc : Specs.D05.M15.TensorDualHom.CompositionTrace.product_assoc := by
  intro K V _ _ _ _ r s t
  apply (dualTensorHomEquiv K V V).injective
  change phi K V V (compositionProduct K V (compositionProduct K V r s) t) =
    phi K V V (compositionProduct K V r (compositionProduct K V s t))
  rw [phi_product, phi_product, phi_product, phi_product]
  rfl

theorem phi_unit : Specs.D05.M15.TensorDualHom.CompositionTrace.phi_unit := by
  intro K V _ _ _ _
  exact (dualTensorHomEquiv K V V).apply_symm_apply _

theorem unit_characterization :
    Specs.D05.M15.TensorDualHom.CompositionTrace.unit_characterization := by
  intro K V _ _ _ _ t
  constructor
  · intro h
    apply (dualTensorHomEquiv K V V).injective
    exact h.trans phi_unit.symm
  · rintro rfl
    exact phi_unit

theorem unit_left : Specs.D05.M15.TensorDualHom.CompositionTrace.unit_left := by
  intro K V _ _ _ _ t
  apply (dualTensorHomEquiv K V V).injective
  change phi K V V (compositionProduct K V (unitTensor K V) t) = phi K V V t
  rw [phi_product, phi_unit, LinearMap.id_comp]

theorem unit_right : Specs.D05.M15.TensorDualHom.CompositionTrace.unit_right := by
  intro K V _ _ _ _ t
  apply (dualTensorHomEquiv K V V).injective
  change phi K V V (compositionProduct K V t (unitTensor K V)) = phi K V V t
  rw [phi_product, phi_unit, LinearMap.comp_id]

/-- The upstream inverse formula at id is exactly the sum of dual basis tensors. -/
theorem unit_basis : Specs.D05.M15.TensorDualHom.CompositionTrace.unit_basis := by
  intro K V I _ _ _ _ _ b
  exact D05.M15.TensorDualHom.inverse_formula b (dualTensorHomEquiv K V V) rfl
    LinearMap.id

theorem unit_basis_independent :
    Specs.D05.M15.TensorDualHom.CompositionTrace.unit_basis_independent := by
  intro K V I J _ _ _ _ _ _ b c
  exact (unit_basis b).symm.trans (unit_basis c)

end D05.M15.TensorDualHom.CompositionTrace
