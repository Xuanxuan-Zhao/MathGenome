import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Foundations
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Correspondence.Conjugation

/-!
The conjugation assertions of FT-C05. Products apply the right factor first.
The field image and subgroup conjugate are the standard pointwise images;
these identities do not require algebraicity, normality, or separability.
-/

universe u v

namespace AdvancedFieldTheory

open scoped Pointwise

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- An automorphism transports the pointwise fixing subgroup by conjugation. -/
theorem fixingSubgroup_image (g : L ≃ₐ[K] L) (M : IntermediateField K L) :
    fixingSubgroup (M.map g.toAlgHom) = (MulAut.conj g) • fixingSubgroup M := by
  exact IsGalois.map_fixingSubgroup M g

/-- The fixed field of a conjugate subgroup is the image of the fixed field. -/
theorem fixedField_conjugate (g : L ≃ₐ[K] L) (H : Subgroup (L ≃ₐ[K] L)) :
    fixedField ((MulAut.conj g) • H) = (fixedField H).map g.toAlgHom := by
  ext y
  constructor
  · intro hy
    refine (IntermediateField.mem_map _).mpr ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    apply (mem_fixedField H (g.symm y)).mpr
    intro h hh
    have hc : g * h * g⁻¹ ∈ (MulAut.conj g) • H :=
      Subgroup.smul_mem_pointwise_smul h (MulAut.conj g) H hh
    have he := (mem_fixedField _ y).mp hy (g * h * g⁻¹) hc
    change g (h (g.symm y)) = y at he
    apply g.injective
    simpa only [AlgEquiv.apply_symm_apply] using he
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (IntermediateField.mem_map _).mp hy
    apply (mem_fixedField _ (g x)).mpr
    intro a ha
    obtain ⟨h, hh, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists a (MulAut.conj g) H).mp ha
    have he := (mem_fixedField H x).mp hx h hh
    change g (h (g.symm (g x))) = g x
    simpa only [AlgEquiv.symm_apply_apply] using congrArg g he

end AdvancedFieldTheory
