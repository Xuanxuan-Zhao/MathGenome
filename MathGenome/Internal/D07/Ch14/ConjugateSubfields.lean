import MathGenome.Internal.D07.Ch14.FixedField
import MathGenome.Internal.Specs.D07.Ch14.ConjugateSubfields

/-! Conjugating an intermediate field conjugates its pointwise fixing subgroup.
The statement holds for every field extension, including infinite extensions.
-/

universe u v

namespace D07.Ch14.ConjugateSubfields

open Specs.D07.Ch14.ConjugateSubfields

theorem fixes_image_iff : FixesImageIff.{u, v} := by
  intro K L _ _ _ E σ τ
  simp only [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_map,
    AlgEquiv.coe_toAlgHom,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h x hx
    change σ.symm (τ (σ x)) = x
    rw [h x hx, σ.symm_apply_apply]
  · intro h x hx
    have hfix := h x hx
    change σ.symm (τ (σ x)) = x at hfix
    exact σ.symm.injective (hfix.trans (σ.symm_apply_apply x).symm)

theorem conjugate_fixing_subgroup : ConjugateFixingSubgroup.{u, v} := by
  intro K L _ _ _ E σ
  exact IsGalois.map_fixingSubgroup E σ

end D07.Ch14.ConjugateSubfields
