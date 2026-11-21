import MathGenome.Internal.Specs.D05.M15.TensorQuotient
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-! K05.15.tensor_quotient: canonical compatibility of tensor products and quotients. -/

namespace D05.M15.TensorQuotient

open scoped TensorProduct
open Specs.D05.M15.TensorQuotient (tensorRelations)

theorem canonical_quotient_iso : Specs.D05.M15.TensorQuotient.canonical_quotient_iso := by
  intro K V W _ _ _ _ _ U S
  refine ⟨TensorProduct.quotientTensorQuotientEquiv U S, fun _ _ => rfl, ?_⟩
  intro e he
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext'
  intro v w
  obtain ⟨v, rfl⟩ := U.mkQ_surjective v
  obtain ⟨w, rfl⟩ := S.mkQ_surjective w
  exact he v w

theorem inverse_quotient_formula : Specs.D05.M15.TensorQuotient.inverse_quotient_formula := by
  intro K V W _ _ _ _ _ U S e he
  have hi (v : V) (w : W) :
      e.symm ((tensorRelations U S).mkQ (v ⊗ₜ[K] w)) = U.mkQ v ⊗ₜ[K] S.mkQ w := by
    rw [← he v w, e.symm_apply_apply]
  refine ⟨hi, ?_⟩
  apply TensorProduct.ext'
  exact hi

theorem quotient_map_kernel : Specs.D05.M15.TensorQuotient.quotient_map_kernel := by
  intro K V W _ _ _ _ _ U S
  obtain ⟨e, he, _⟩ := canonical_quotient_iso U S
  have hf := (inverse_quotient_formula U S e he).2
  apply Submodule.ext
  intro t
  rw [← hf]
  change e.symm ((tensorRelations U S).mkQ t) = 0 ↔ t ∈ tensorRelations U S
  rw [e.symm.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem representative_independence : Specs.D05.M15.TensorQuotient.representative_independence := by
  intro K V W _ _ _ _ _ U S v v' w w' hv hw
  obtain ⟨e, he, _⟩ := canonical_quotient_iso U S
  have hvq : U.mkQ v' = U.mkQ v := (Submodule.Quotient.eq U).mpr hv
  have hwq : S.mkQ w' = S.mkQ w := (Submodule.Quotient.eq S).mpr hw
  rw [← he v' w', ← he v w, hvq, hwq]

end D05.M15.TensorQuotient
