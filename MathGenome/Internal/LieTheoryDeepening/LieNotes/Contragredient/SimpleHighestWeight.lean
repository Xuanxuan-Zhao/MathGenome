import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.VermaModules
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.WeightExtraction
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.SimpleHighestWeight

/-! The simple highest-weight quotient of a contragredient Verma module. -/

namespace LieNotes.Contragredient.SimpleHighestWeight

open CartanQuotient (Algebra cartan)
open VermaModules (Verma)
open Specs.LieNotes.Contragredient.VermaModules (IsWeightCharacter IsHighestVector cartanAction)
open Specs.LieNotes.Contragredient.SimpleHighestWeight
  (RadicalIsGreatest SimpleModule TopHighest UniqueSimpleQuotient WeightSpaceImage)
open UniversalEnvelopingAlgebra (ι)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)

noncomputable section

universe u v w

abbrev radical := @Specs.LieNotes.Contragredient.SimpleHighestWeight.radical
abbrev L := @Specs.LieNotes.Contragredient.SimpleHighestWeight.L
abbrev quotientMap := @Specs.LieNotes.Contragredient.SimpleHighestWeight.quotientMap
abbrev top := @Specs.LieNotes.Contragredient.SimpleHighestWeight.top
abbrev weightSpaceAt := @Specs.LieNotes.Contragredient.SimpleHighestWeight.weightSpaceAt

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v}
  [AddCommGroup H] [Module ℂ H] [Finite I]
  (R : Realization A H) (Λ : Module.Dual ℂ H) (hχ : ∃! χ, IsWeightCharacter R Λ χ)

private theorem top_not_mem_of_proper {N : Submodule (U (Algebra R)) (Verma R Λ hχ)}
    (hN : N ≠ ⊤) : VermaModules.top R Λ hχ ∉ N := by
  intro ht
  apply hN (top_unique ?_)
  intro x _
  obtain ⟨a, rfl⟩ := VermaModules.top_cyclic R Λ hχ x
  exact N.smul_mem a ht

private theorem top_not_mem_radical : VermaModules.top R Λ hχ ∉ radical R Λ hχ := by
  classical
  let ρ := cartanAction R (Verma R Λ hχ)
  let W := VermaModules.weightSpaceAt R Λ hχ
  let otherWeights := ⨆ μ, ⨆ (_ : μ ≠ Λ), W μ
  have hspan : (⨆ μ, W μ) = ⊤ :=
    (VermaModules.weightDecomposition R Λ hχ).submodule_iSup_eq_top
  obtain ⟨htop, hline⟩ := VermaModules.topWeightSpace R Λ hχ
  change W Λ = ℂ ∙ VermaModules.top R Λ hχ at hline
  have hproper (N : Submodule (U (Algebra R)) (Verma R Λ hχ)) (hN : N ≠ ⊤) :
      N.restrictScalars ℂ ≤ otherWeights := by
    have hsplit : (⨆ μ, N.restrictScalars ℂ ⊓ W μ) = N.restrictScalars ℂ :=
      iSup_inf_weightSpace_eq ρ (N.restrictScalars ℂ)
        (fun h _ hx ↦ N.smul_mem (ι ℂ (cartan R h)) hx) id (fun _ _ h ↦ h) hspan
    rw [← hsplit]
    refine iSup_le fun μ ↦ ?_
    by_cases hμ : μ = Λ
    · subst μ
      intro x hx
      have hxline : x ∈ W Λ := hx.2
      rw [hline] at hxline
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxline
      have hc : c = 0 := by
        by_contra hc
        apply top_not_mem_of_proper R Λ hχ hN
        have hm := (N.restrictScalars ℂ).smul_mem c⁻¹ hx.1
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
      simp [hc]
    · exact inf_le_right.trans (le_iSup_of_le μ (le_iSup_of_le hμ le_rfl))
  have hbound : (radical R Λ hχ).restrictScalars ℂ ≤ otherWeights := by
    change (sSup {N : Submodule (U (Algebra R)) (Verma R Λ hχ) | N ≠ ⊤}).restrictScalars ℂ ≤ _
    rw [Submodule.restrictScalars_sSup]
    refine sSup_le ?_
    rintro _ ⟨N, hN, rfl⟩
    exact hproper N hN
  have hdisj : Disjoint (W Λ) otherWeights := weightSpace_iSupIndep ρ Λ
  intro hx
  have hmem : VermaModules.top R Λ hχ ∈ W Λ :=
    (VermaModules.mem_weightSpaceAt R Λ hχ).mpr (VermaModules.top_isHighest R Λ hχ).1
  exact htop (Submodule.disjoint_def.mp hdisj _ hmem (hbound hx))

theorem radicalIsGreatest : RadicalIsGreatest.{u, v} := by
  intro I A H _ _ _ R Λ hχ
  refine ⟨?_, fun N hN ↦ le_sSup hN⟩
  intro heq
  change radical R Λ hχ = ⊤ at heq
  apply top_not_mem_radical R Λ hχ
  rw [heq]
  exact Submodule.mem_top

private theorem radical_isCoatom : IsCoatom (radical R Λ hχ) := by
  have hr := radicalIsGreatest R Λ hχ
  refine ⟨hr.1, fun N hN ↦ ?_⟩
  by_contra h
  exact hN.not_ge (hr.2 h)

theorem simpleModule : SimpleModule.{u, v} := by
  intro I A H _ _ _ R Λ hχ
  exact isSimpleModule_iff_isCoatom.mpr (radical_isCoatom R Λ hχ)

theorem topHighest : TopHighest.{u, v} := by
  intro I A H _ _ _ R Λ hχ
  refine ⟨?_, ?_⟩
  · intro hz
    exact top_not_mem_radical R Λ hχ ((Submodule.Quotient.mk_eq_zero _).mp hz)
  · have ht := VermaModules.top_isHighest R Λ hχ
    let q := quotientMap R Λ hχ
    change IsHighestVector R Λ (q (VermaModules.top R Λ hχ))
    constructor
    · intro h
      simpa only [map_smul, q.map_smul_of_tower] using congrArg q (ht.1 h)
    · intro x
      simpa only [map_smul, map_zero] using congrArg q (ht.2 x)

theorem uniqueSimpleQuotient : UniqueSimpleQuotient.{u, v, w} := by
  intro I A H _ _ _ R Λ hχ V _ _ _ q hq
  have hk := q.isCoatom_ker_of_surjective hq
  have hr := radicalIsGreatest R Λ hχ
  have hle : LinearMap.ker q ≤ radical R Λ hχ := hr.2 hk.1
  have hker : radical R Λ hχ = LinearMap.ker q :=
    le_antisymm ((isCoatom_iff_ge_of_le.mp hk).2 _ hr.1 hle) hle
  let e := (Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hq)
  have he : e.toLinearMap.comp (quotientMap R Λ hχ) = q := by
    apply LinearMap.ext
    intro x
    change q.quotKerEquivOfSurjective hq
      (Submodule.quotEquivOfEq _ _ hker (Submodule.Quotient.mk x)) = q x
    rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  refine ⟨e, he, fun e' he' ↦ ?_⟩
  apply LinearEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (radical R Λ hχ).mkQ_surjective y
  exact LinearMap.congr_fun (he'.trans he.symm) x

theorem weightSpaceImage : WeightSpaceImage.{u, v} := by
  classical
  intro I A H _ _ _ R Λ hχ μ
  let W := VermaModules.weightSpaceAt R Λ hχ
  let q := quotientMap R Λ hχ
  let qℂ := q.restrictScalars ℂ
  let images := fun ν ↦ (W ν).map qℂ
  have hspan : (⨆ ν, images ν) = ⊤ := by
    change (⨆ ν, (W ν).map qℂ) = ⊤
    rw [← Submodule.map_iSup, (VermaModules.weightDecomposition R Λ hχ).submodule_iSup_eq_top]
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact (radical R Λ hχ).mkQ_surjective
  have hle : images ≤ weightSpaceAt R Λ hχ := by
    intro ν y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    intro h
    change (ι ℂ (cartan R h) : U (Algebra R)) • q x = ν h • q x
    simpa only [map_smul, q.map_smul_of_tower] using
      congrArg q ((VermaModules.mem_weightSpaceAt R Λ hχ).mp hx h)
  have hi : iSupIndep (weightSpaceAt R Λ hχ) := weightSpace_iSupIndep (cartanAction R (L R Λ hχ))
  exact (congrFun ((hi.le_iff_eq_of_iSup_eq_top hspan).mp hle) μ).symm

end

end LieNotes.Contragredient.SimpleHighestWeight
