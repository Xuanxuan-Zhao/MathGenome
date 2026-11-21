import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.CentralPresentation
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.Central
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Homology.HopfFormula

namespace ALG02GroupTheory.Extensions.CentralPresentation

open HopfFormula (denominator numerator PresentationQuotient toKernelQuotient hopfEquiv)
open scoped commutatorElement

universe u v w

variable {R : Type u} {F : Type v} {G : Type w} [Group R] [Group F] [Group G]

abbrev PresentationGroup (S : GroupExtension R F G) := Spec.PresentationGroup S

abbrev projection (S : GroupExtension R F G) : PresentationGroup S →* G := Spec.projection S

abbrev kernelInclusion (S : GroupExtension R F G) :
    PresentationQuotient S.inl.range →* PresentationGroup S := Spec.kernelInclusion S

@[simp]
theorem projection_mk (S : GroupExtension R F G) (x : commutator F) :
    projection S (QuotientGroup.mk x) = S.rightHom x.val :=
  rfl

@[simp]
theorem kernelInclusion_mk (S : GroupExtension R F G) (x : numerator S.inl.range) :
    kernelInclusion S (QuotientGroup.mk x) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_right x : commutator F) :=
  rfl

theorem projection_surjective [Group.IsPerfect G] (S : GroupExtension R F G) :
    Function.Surjective (projection S) := by
  intro g
  have h : (commutator F).map S.rightHom = ⊤ := by
    rw [map_commutator_of_surjective S.rightHom_surjective, Group.IsPerfect.commutator_eq_top]
  have hg : g ∈ (commutator F).map S.rightHom := h.symm ▸ Subgroup.mem_top g
  obtain ⟨f, hf, rfl⟩ := hg
  exact ⟨QuotientGroup.mk ⟨f, hf⟩, rfl⟩

theorem kernelInclusion_injective (S : GroupExtension R F G) :
    Function.Injective (kernelInclusion S) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a
  induction a using QuotientGroup.induction_on with
  | _ x =>
    rw [kernelInclusion_mk, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff]
    exact id

theorem range_kernelInclusion (S : GroupExtension R F G) :
    (kernelInclusion S).range = (projection S).ker := by
  ext a
  induction a using QuotientGroup.induction_on with
  | _ x =>
    rw [MonoidHom.mem_ker, projection_mk]
    constructor
    · rintro ⟨z, hz⟩
      change projection S (QuotientGroup.mk x) = 1
      rw [← hz]
      induction z using QuotientGroup.induction_on with
      | _ z =>
        rw [kernelInclusion_mk, projection_mk]
        exact (S.range_inl_eq_ker_rightHom ▸ z.property.1 : z.val ∈ S.rightHom.ker)
    · intro hx
      have hx' : x.val ∈ S.inl.range := S.range_inl_eq_ker_rightHom.symm ▸
        (MonoidHom.mem_ker.mpr hx)
      exact ⟨QuotientGroup.mk ⟨x.val, hx', x.property⟩, rfl⟩

/-- The actual kernel of the induced projection, identified by inclusion of representatives. -/
noncomputable def kernelEquiv (S : GroupExtension R F G) :
    PresentationQuotient S.inl.range ≃* (projection S).ker :=
  (MonoidHom.ofInjective (kernelInclusion_injective S)).trans
    (MulEquiv.subgroupCongr (range_kernelInclusion S))

@[simp]
theorem kernelEquiv_val (S : GroupExtension R F G) (x : PresentationQuotient S.inl.range) :
    (kernelEquiv S x).val = kernelInclusion S x :=
  rfl

theorem kernel_identification : Spec.KernelIdentification.{u, v, w} :=
  fun S => ⟨kernelEquiv S, kernelEquiv_val S⟩

theorem projection_central (S : GroupExtension R F G) :
    (projection S).ker ≤ Subgroup.center (PresentationGroup S) := by
  intro a
  induction a using QuotientGroup.induction_on with
  | _ x =>
    intro hx
    have hx' : x.val ∈ S.inl.range :=
      S.range_inl_eq_ker_rightHom.symm ▸ (show x.val ∈ S.rightHom.ker from hx)
    apply Subgroup.mem_center_iff.mpr
    intro b
    induction b using QuotientGroup.induction_on with
    | _ y =>
      apply commutatorElement_eq_one_iff_mul_comm.mp
      let q := QuotientGroup.mk' ((denominator S.inl.range).subgroupOf (commutator F))
      change ⁅q y, q x⁆ = 1
      rw [← map_commutatorElement q]
      change (QuotientGroup.mk ⁅y, x⁆ : PresentationGroup S) = 1
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top y.val) hx')

theorem presentation_perfect [Group.IsPerfect G] (S : GroupExtension R F G) :
    Group.IsPerfect (PresentationGroup S) := by
  have hGeneration : commutator F ⊔ S.inl.range = ⊤ := by
    rw [S.range_inl_eq_ker_rightHom, ← Subgroup.comap_map_eq,
      map_commutator_of_surjective S.rightHom_surjective,
      Group.IsPerfect.commutator_eq_top, Subgroup.comap_top]
  have hDerived : ⁅commutator F, commutator F⁆ ⊔ denominator S.inl.range = commutator F := by
    apply le_antisymm
    · exact sup_le (Subgroup.commutator_le_self _)
        (Subgroup.commutator_mono_right le_top)
    · calc
        commutator F = ⁅commutator F ⊔ S.inl.range, commutator F ⊔ S.inl.range⁆ := by
          rw [hGeneration, commutator_def]
        _ = (⁅commutator F, commutator F⁆ ⊔ ⁅S.inl.range, commutator F⁆) ⊔
            denominator S.inl.range := by
          rw [Subgroup.commutator_sup_left, Subgroup.commutator_sup_right, hGeneration]
        _ ≤ ⁅commutator F, commutator F⁆ ⊔ denominator S.inl.range := by
          rw [Subgroup.commutator_comm S.inl.range (commutator F)]
          exact sup_le (sup_le le_sup_left
            ((Subgroup.commutator_mono_left le_top).trans le_sup_right)) le_sup_right
  let N := (denominator S.inl.range).subgroupOf (commutator F)
  have hTop : commutator (commutator F) ⊔ N = ⊤ := by
    rw [← Subgroup.map_subtype_inj, Subgroup.map_sup, Subgroup.map_subtype_commutator,
      Subgroup.map_top, Subgroup.range_subtype]
    rw [show N.map (commutator F).subtype = denominator S.inl.range from
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_mono_right le_top)]
    exact hDerived
  have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hTop
  rw [Subgroup.map_sup, map_commutator_of_surjective (QuotientGroup.mk'_surjective N),
    QuotientGroup.map_mk'_self, sup_bot_eq, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  exact ⟨h⟩

/-- The exact extension with the presented group as middle group. -/
def extension [Group.IsPerfect G] (S : GroupExtension R F G) :
    GroupExtension (PresentationQuotient S.inl.range) (PresentationGroup S) G where
  inl := kernelInclusion S
  rightHom := projection S
  inl_injective := kernelInclusion_injective S
  range_inl_eq_ker_rightHom := range_kernelInclusion S
  rightHom_surjective := projection_surjective S

theorem extension_central [Group.IsPerfect G] (S : GroupExtension R F G) :
    IsCentralExtension (extension S) :=
  (isCentralExtension_iff_ker_le_center (extension S)).mpr (projection_central S)

section Homology

open IntegralBar (homology)
variable {R F G : Type u} [Group R] [Group F] [Group G]

/-- The Hopf isomorphism followed by the identification with the kernel of the projection. -/
noncomputable def homologyKernelEquiv [IsFreeGroup F] (S : GroupExtension R F G) :
    Multiplicative (homology G 2) ≃* (projection S).ker :=
  (hopfEquiv S).trans (kernelEquiv S)

theorem homology_kernel_identification : Spec.HomologyKernelIdentification.{u} := by
  intro R F G _ _ _ _ S
  refine ⟨homologyKernelEquiv S, hopfEquiv S, Transgression.integralTransgression S,
    FiveTerm.signed_transgression S, ?_⟩
  intro x
  exact ⟨HopfFormula.hopfEquiv_transgression S x, rfl⟩

end Homology

end ALG02GroupTheory.Extensions.CentralPresentation
