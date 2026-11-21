import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ConeCriterion
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex
open Specs.AdvancedHomologicalAlgebra.ConeCriterion
namespace AdvancedHomologicalAlgebra.ConeCriterion

theorem identityConeContractible :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.identityConeContractibleType := by
  intro A _ _ _ X
  exact ⟨mappingCone.homotopyToZeroOfId X⟩

theorem coneCriterion :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.coneCriterionType := by
  intro A _ _ X Y f
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic A).trW_iff_of_distinguished
    (mappingCone.triangleh f) (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

noncomputable def integralTwoTerm :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.twoTermType := twoTerm
noncomputable def integralAugmentation :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.augmentationType := augmentation

lemma reduction_epi : Epi reduction := by
  rw [ModuleCat.epi_iff_surjective]
  change Function.Surjective (fun x : ℤ => (x : ZMod 2))
  exact ZMod.intCast_surjective

lemma doubling_reduction_zero : doubling ≫ reduction = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((2 * x : ℤ) : ZMod 2) = 0
  rw [Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]

lemma reduction_exact : (ShortComplex.mk doubling reduction doubling_reduction_zero).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change ((x : ℤ) : ZMod 2) = 0 at hx
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hx
  refine ⟨k, ?_⟩
  change 2 * k = x
  exact hk.symm

/-- Reduction modulo two induces the cohomology isomorphisms in every degree. -/
theorem augmentationQuasiIso :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.augmentationQuasiIsoType := by
  change QuasiIso augmentation
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    rw [quasiIsoAt_iff' augmentation (-1) 0 1
      ((ComplexShape.up ℤ).prev_eq' (by decide))
      ((ComplexShape.up ℤ).next_eq' (by decide)),
      ShortComplex.quasiIso_iff_of_zeros' _ (by
        change twoTerm.d 0 1 = 0
        exact double_d_eq_zero₀ _ _ _ _ (by decide)) (by rfl) (by rfl)]
    constructor
    · let d₀ := doubleXIso₀ doubling (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)
      let d₁ := doubleXIso₁ doubling (show (ComplexShape.up ℤ).Rel (-1) 0 by decide) (by decide)
      let e := singleObjXSelf (ComplexShape.up ℤ) 0 modTwo
      apply ShortComplex.exact_of_iso (ShortComplex.isoMk d₀ d₁ e ?_ ?_).symm reduction_exact
      · dsimp
        rw [show twoTerm.d (-1) 0 = d₀.hom ≫ doubling ≫ d₁.inv from double_d _ _ (by decide)]
        simp
      · dsimp
        simp [augmentation, d₁, e]
    · change Epi (augmentation.f 0)
      dsimp only [augmentation]
      rw [mkHomToSingle_f]
      have := reduction_epi
      infer_instance
  · have ht : stalk.ExactAt n := ExactAt.of_isZero
      (isZero_single_obj_X (ComplexShape.up ℤ) 0 modTwo n hn)
    rw [quasiIsoAt_iff_exactAt' augmentation n ht]
    by_cases hm : n = -1
    · subst n
      rw [exactAt_iff' twoTerm (-2) (-1) 0
        ((ComplexShape.up ℤ).prev_eq' (by decide))
        ((ComplexShape.up ℤ).next_eq' (by decide)),
        ShortComplex.exact_iff_mono _ (by
          change twoTerm.d (-2) (-1) = 0
          exact double_d_eq_zero₀ _ _ _ _ (by decide))]
      change Mono (twoTerm.d (-1) 0)
      dsimp only [twoTerm]
      rw [double_d _ _ (by decide)]
      have : Mono doubling := (ModuleCat.mono_iff_injective _).mpr (by
        intro x y h
        change 2 * x = 2 * y at h
        exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h)
      infer_instance
    · exact ExactAt.of_isZero (isZero_double_X doubling _ n hm hn)

/-- A map from the torsion module to the integers must vanish. -/
lemma modTwo_to_integers_zero (f : modTwo ⟶ integers) : f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : (2 : ℤ) • x = 0 := by
    rw [zsmul_eq_mul]
    change (2 : ZMod 2) * x = 0
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul]
  have hf : (2 : ℤ) • f x = 0 := by
    rw [← f.hom.map_smul, hx, map_zero]
  change (f x : ℤ) = 0
  change 2 * (f x : ℤ) = 0 at hf
  exact (mul_eq_zero.mp hf).resolve_left (by decide)

lemma stalk_to_twoTerm_zero (g : stalk ⟶ twoTerm) : g = 0 := by
  apply HomologicalComplex.from_single_hom_ext
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 modTwo
  let d := HomologicalComplex.doubleXIso₁ doubling
    (show (ComplexShape.up ℤ).Rel (-1) 0 by decide) (by decide)
  apply (cancel_epi e.inv).mp
  apply (cancel_mono d.hom).mp
  simpa using modTwo_to_integers_zero (e.inv ≫ g.f 0 ≫ d.hom)

/-- Every map back is zero, so the stalk identity cannot be recovered up to homotopy. -/
theorem augmentationNoHomotopyInverse :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.augmentationNoHomotopyInverseType := by
  intro g ⟨h⟩
  have hh := h.comm 0
  simp only [dNext, prevD, stalk,
    HomologicalComplex.single_obj_d, zero_comp, comp_zero] at hh
  simp only [stalk_to_twoTerm_zero g, zero_comp, HomologicalComplex.zero_f_apply,
    HomologicalComplex.id_f] at hh
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 modTwo
  have hh' := congrArg (fun k => e.inv ≫ k ≫ e.hom) hh
  have hh'' : (0 : modTwo ⟶ modTwo) = 𝟙 _ := by simpa using hh'
  have hz := congrArg (fun k : modTwo ⟶ modTwo => k (1 : ZMod 2)) hh''
  simp at hz

/-- The displayed integral augmentation witnesses the source's existential assertion. -/
theorem moduleCounterexample :
    Specs.AdvancedHomologicalAlgebra.ConeCriterion.moduleCounterexampleType := by
  refine ⟨twoTerm, stalk, augmentation, augmentationQuasiIso, ?_⟩
  rintro ⟨e, he⟩
  apply augmentationNoHomotopyInverse e.inv
  exact ⟨by simpa only [he] using e.homotopyInvHomId⟩

end AdvancedHomologicalAlgebra.ConeCriterion
