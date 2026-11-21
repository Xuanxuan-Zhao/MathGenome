import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.Foundations

/-!
Independent statements for the two conjugation assertions of FT-C05,
notes/003/advanced-field-theory.tex:754–759, 770–777.
`M.map g.toAlgHom` is the literal image field g(M). The pointwise action
of `MulAut.conj g` on a subgroup is its image under h ↦ g * h * g⁻¹.
Both assertions hold for arbitrary field extensions, and hence in particular
under the Galois convention of Chapter 3. No topology is needed.
-/

universe u v

namespace Specs.AdvancedFieldTheory

open scoped Pointwise

/-- G_{g(M)} = g G_M g⁻¹. -/
def fixingSubgroup_image_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (g : L ≃ₐ[K] L) (M : IntermediateField K L),
    (M.map g.toAlgHom).fixingSubgroup =
      (MulAut.conj g) • M.fixingSubgroup

/-- L^{g H g⁻¹} = g(L^H), for every subgroup H. -/
def fixedField_conjugate_type : Prop :=
  ∀ {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (g : L ≃ₐ[K] L) (H : Subgroup (L ≃ₐ[K] L)),
    IntermediateField.fixedField ((MulAut.conj g) • H) =
      (IntermediateField.fixedField H).map g.toAlgHom

end Specs.AdvancedFieldTheory
