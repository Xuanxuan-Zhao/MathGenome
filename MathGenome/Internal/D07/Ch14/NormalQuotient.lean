import MathGenome.Internal.Specs.D07.Ch14.NormalQuotient
import MathGenome.Internal.D07.Ch14.FundamentalCorrespondence
import MathGenome.Internal.D07.Ch14.NormalQuotientRestrictionSurjectivity

/-!
Normal subgroups and quotient Galois groups (K07.14.normal_quotient).

Normality of H makes its fixed field stable under all base automorphisms;
normality of L/K then gives normality of that fixed field over K.
Separability is inherited. Conversely a Galois intermediate field has a
normal fixing subgroup, and the fundamental correspondence identifies the
fixing subgroup of L^H with H. Finally restriction is surjective with kernel
H, so the quotient equivalence sends σH to the restriction of σ.
-/

universe u v

namespace D07.Ch14.NormalQuotient

open Specs.D07.Ch14.NormalQuotient

theorem galois_iff_normal : GaloisIffNormal.{u, v} := by
  intro K L _ _ _ _ _ H
  change IsGalois K (IntermediateField.fixedField H) ↔ H.Normal
  constructor
  · intro h
    let := h
    have hfix : (IntermediateField.fixedField H).fixingSubgroup.Normal :=
      IsGalois.fixingSubgroup_normal_of_isGalois (IntermediateField.fixedField H)
    have heq := FundamentalCorrespondence.fixing_subgroup_fixed_field K L H
    change (IntermediateField.fixedField H).fixingSubgroup = H at heq
    rw [heq] at hfix
    exact hfix
  · intro h
    let := h
    exact IsGalois.of_fixedField_normal_subgroup H

theorem quotient_restriction : QuotientRestriction.{u, v} := by
  intro K L _ _ _ _ _ H _
  dsimp only
  let E := Specs.D07.Ch14.FixedField.fixedFieldValue K L H
  let : IsGalois K E := (galois_iff_normal K L H).mpr inferInstance
  let f := NormalQuotientRestrictionSurjectivity.restrictionHom K E L
  have hf : Function.Surjective f :=
    NormalQuotientRestrictionSurjectivity.restriction_surjective K E L
  have hker : H = f.ker :=
    (FundamentalCorrespondence.fixing_subgroup_fixed_field K L H).symm.trans
      (NormalQuotientRestrictionSurjectivity.intermediate_restriction_kernel K L E).symm
  refine ⟨QuotientGroup.liftEquiv (φ := f) H hf hker, ?_⟩
  intro σ x
  exact NormalQuotientRestrictionSurjectivity.restriction_agrees K E L σ x

end D07.Ch14.NormalQuotient
