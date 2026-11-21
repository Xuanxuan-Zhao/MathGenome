import MathGenome.Internal.D07.Ch14.ArtinFixedFieldFixedFieldDimension
import MathGenome.Internal.Specs.D07.Ch14.ArtinFixedField

/-!
Artin's fixed-field theorem (paper.tex:4123–4144).

The accepted dimension theorem supplies finite dimension and the degree
formula without assuming that L already has finite degree. Mathlib's
`IsGalois.of_fixed_field` supplies normality and separability: its proof
uses the distinct orbit-root polynomial over the fixed subfield and the
minimal-polynomial divisibility criterion. Finally
`FixedPoints.toAlgAut_bijective` proves that the action homomorphism gives
all fixed-field automorphisms, by independence and the degree bound.
These results apply to arbitrary characteristic and allow the trivial group.
-/

universe u v

namespace D07.Ch14.ArtinFixedField

open Specs.D07.Ch14.ArtinFixedField

theorem faithful_action_artin : FaithfulActionArtin.{u, v} := by
  intro H L _ _ _ _ _
  have hd := ArtinFixedFieldFixedFieldDimension.faithful_action_dimension H L
  exact ⟨hd.1, IsGalois.of_fixed_field L H, hd.2,
    FixedPoints.toAlgAut_bijective H L⟩

theorem subgroup_artin : SubgroupArtin.{u, v} := by
  intro K L _ _ _ H _
  have h := faithful_action_artin H L
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro σ
  obtain ⟨g, hg⟩ := h.2.2.2.surjective σ
  exact ⟨g, fun x => (DFunLike.congr_fun hg x).symm⟩

end D07.Ch14.ArtinFixedField
