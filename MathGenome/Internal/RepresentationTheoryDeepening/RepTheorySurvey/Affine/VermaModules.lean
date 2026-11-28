import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.VermaModules
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.VermaWeightSpaces
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightExactness

/-! The simple affine highest-weight quotient. -/

noncomputable section

namespace RepTheorySurvey.Affine

universe u v

open _root_.Specs.RepTheorySurvey.Affine.VermaModules
open _root_.Specs.RepTheorySurvey.Affine.VermaWeightSpaces
open _root_.Specs.RepTheorySurvey.Affine.LoopAlgebra (K_value affineBracket_value)
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular)
open _root_.RepTheorySurvey.CategoryO
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U inclusion)
open UniversalEnvelopingAlgebra (ι)
open scoped DirectSum

abbrev affineVermaRadical := @affineVermaRadical_value
abbrev affineSimple := @affineSimple_value
abbrev affineSimpleProjection := @affineSimpleProjection_value
abbrev affineSimpleTop := @affineSimpleTop_value
abbrev affineSimpleWeightSpace := @affineSimpleWeightSpace_value

abbrev affineSimpleAt := @affineSimpleAt_value
abbrev affineSimpleTopAt := @affineSimpleTopAt_value
abbrev affineLevel := @affineLevel_value

theorem affineVermaProperties : affineVermaProperties_type.{u, v} :=
  ⟨affineVermaCharacter, affineVermaUniversal, affineVermaWeights⟩

section CartanAction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] (T : LieSubalgebra ℂ L)
variable (V : Type v) [AddCommGroup V] [Module ℂ V] [Module (U L) V]

local instance envelopingCartanLieRingModule : LieRingModule T V :=
  letI := LieRingModule.ofAssociativeModule (A := U L) (M := V)
  LieRingModule.compLieHom V ((ι ℂ).comp T.incl)

local instance envelopingCartanLieModule [IsScalarTower ℂ (U L) V] : LieModule ℂ T V :=
  letI := LieRingModule.ofAssociativeModule (A := U L) (M := V)
  letI := LieModule.ofAssociativeModule (R := ℂ) (A := U L) (M := V)
  LieModule.compLieHom V ((ι ℂ).comp T.incl)

variable [IsScalarTower ℂ (U L) V]

private theorem mem_envelopingCartanWeightSpace (μ : Module.Dual ℂ T) (x : V) :
    x ∈ WeightExactness.weightSpace V μ ↔ ∀ h : T, ι ℂ (h : L) • x = μ h • x :=
  LieModule.mem_weightSpace μ x

private def envelopingCartanSubmodule (S : Submodule (U L) V) : LieSubmodule ℂ T V where
  __ := S.restrictScalars ℂ
  lie_mem := S.smul_mem _

private def envelopingCartanMap {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    [Module (U L) Y] [IsScalarTower ℂ (U L) Y] (f : V →ₗ[U L] Y) : V →ₗ⁅ℂ,T⁆ Y where
  __ := f.restrictScalars ℂ
  map_lie' := fun {_ _} => f.map_smul _ _

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}
  (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ)

private theorem vermaWeightSpace_eq (μ : Weight B H) :
    affineVermaWeightSpace D χ μ =
      WeightExactness.weightSpace (affineVerma D χ) (H := cartan D) μ := by
  ext x
  exact (mem_affineVermaWeightSpace D χ μ x).trans
    (mem_envelopingCartanWeightSpace (cartan D) (affineVerma D χ) μ x).symm

private theorem simpleWeightSpace_eq (μ : Weight B H) :
    affineSimpleWeightSpace D χ μ =
      WeightExactness.weightSpace (affineSimple D χ) (H := cartan D) μ := by
  ext x
  refine Iff.trans ?_ (mem_envelopingCartanWeightSpace (cartan D) (affineSimple D χ) μ x).symm
  simp only [affineSimpleWeightSpace, affineSimpleWeightSpace_value, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

open scoped Classical in
private theorem verma_isWeightModule (hw : DirectSum.IsInternal (affineVermaWeightSpace D χ)) :
    WeightExactness.IsWeightModule (H := cartan D) (affineVerma D χ) := by
  change DirectSum.IsInternal (fun μ : Weight B H =>
    WeightExactness.weightSpace (affineVerma D χ) (H := cartan D) μ)
  rw [← funext (vermaWeightSpace_eq D χ)]
  exact hw

theorem affineVermaRadicalProper : affineVermaRadicalProper_type.{u} := by
  classical
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ
  let W := affineVermaWeightSpace D χ
  let t := affineVermaTop D χ
  let T := ⨆ (μ : Weight B H) (_ : μ ≠ Λ), W μ
  obtain ⟨hW, _, ht, htop⟩ := affineVermaWeights B H φ D hB hφ Λ χ hχ
  have hweight := verma_isWeightModule D χ hW
  obtain ⟨F, hF⟩ := affineVermaPBW B H φ D hB hφ Λ χ hχ
  have hproper (S : Submodule (U (Carrier D)) (affineVerma D χ)) (hS : S ≠ ⊤) :
      S.restrictScalars ℂ ≤ T := by
    have htS : t ∉ S := fun htS => hS (eq_top_iff.mpr (fun x _ => by
      obtain ⟨a, rfl⟩ := F.surjective x
      rw [hF]
      exact S.smul_mem _ htS))
    have hspan := (WeightExactness.stableSubspace
      (envelopingCartanSubmodule (cartan D) (affineVerma D χ) S) hweight).2.2
    change (⨆ μ : Weight B H, S.restrictScalars ℂ ⊓
      WeightExactness.weightSpace _ (H := cartan D) μ) = S.restrictScalars ℂ at hspan
    rw [← hspan]
    refine iSup_le fun μ => ?_
    rw [← vermaWeightSpace_eq D χ]
    by_cases hμ : μ = Λ
    · subst μ
      intro x hx
      have hxW : x ∈ affineVermaWeightSpace_value D χ Λ := hx.2
      rw [htop] at hxW
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxW
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply htS
        have hmem := (S.restrictScalars ℂ).smul_mem c⁻¹ hx.1
        simpa [smul_smul, inv_mul_cancel₀ hc] using hmem
    · exact inf_le_right.trans (le_iSup_of_le μ (le_iSup (fun _ : μ ≠ Λ => W μ) hμ))
  have hradical : (affineVermaRadical D χ).restrictScalars ℂ ≤ T := by
    rw [affineVermaRadical, affineVermaRadical_value, Submodule.restrictScalars_sSup]
    exact sSup_le (by rintro _ ⟨S, hS, rfl⟩; exact hproper S hS)
  have hd : Disjoint (W Λ) T := iSupIndep_def.mp hW.submodule_iSupIndep Λ
  intro h
  have hmem : t ∈ W Λ := by
    change affineVermaTop_value D χ ∈ affineVermaWeightSpace_value D χ Λ
    rw [htop]
    exact Submodule.mem_span_singleton_self _
  exact ht (Submodule.disjoint_def.mp hd t hmem (hradical h))

theorem affineSimpleWeights : affineSimpleWeights_type.{u} := by
  classical
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ
  obtain ⟨hW, hfinite, _, htop⟩ := affineVermaWeights B H φ D hB hφ Λ χ hχ
  let q := affineSimpleProjection D χ
  let f := envelopingCartanMap (cartan D) (affineVerma D χ) q
  have hq : Function.Surjective q := (affineVermaRadical D χ).mkQ_surjective
  have hX := verma_isWeightModule D χ hW
  change DirectSum.IsInternal (affineVermaWeightSpace D χ) at hW
  change affineVermaWeightSpace D χ Λ = ℂ ∙ affineVermaTop D χ at htop
  have hmap (μ : Weight B H) :
      (affineVermaWeightSpace D χ μ).map (q.restrictScalars ℂ) = affineSimpleWeightSpace D χ μ := by
    rw [vermaWeightSpace_eq D χ, simpleWeightSpace_eq D χ]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (WeightExactness.weightMap f μ ⟨x, hx⟩).property
    · intro y hy
      obtain ⟨x, hx⟩ := WeightExactness.weightMap_surjective f hX hq μ ⟨y, hy⟩
      exact ⟨x, x.property, congrArg Subtype.val hx⟩
  change DirectSum.IsInternal (affineSimpleWeightSpace D χ) ∧
    (∀ μ, FiniteDimensional ℂ (affineSimpleWeightSpace D χ μ)) ∧
    affineSimpleWeightSpace D χ Λ = ℂ ∙ affineSimpleTop D χ
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_, ?_, ?_⟩
  · rw [funext (simpleWeightSpace_eq D χ)]
    exact WeightExactness.weightSpaces_independent (H := cartan D) (X := affineSimple D χ)
  · rw [← funext hmap, ← Submodule.map_iSup, hW.submodule_iSup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hq
  · intro μ
    rw [← hmap]
    let _ := hfinite μ
    infer_instance
  · rw [← hmap, htop, Submodule.map_span, Set.image_singleton]
    rfl

end CartanAction

section SimpleQuotient

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}
  (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ)

private theorem le_affineVermaRadical {S : Submodule (U (Carrier D)) (affineVerma D χ)}
    (hS : S ≠ ⊤) : S ≤ affineVermaRadical D χ :=
  le_sSup hS

private theorem affineVermaRadical_isCoatom (ht : affineVermaTop D χ ∉ affineVermaRadical D χ) :
    IsCoatom (affineVermaRadical D χ) :=
  isCoatom_iff_ge_of_le.mpr ⟨fun h => ht (h ▸ Submodule.mem_top), fun _ hS _ =>
    le_affineVermaRadical D χ hS⟩

end SimpleQuotient

theorem affineSimpleHighestWeight : affineSimpleHighestWeight_type.{u} := by
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ
  let q := affineSimpleProjection D χ
  have ht := affineVermaRadicalProper B H φ D hB hφ Λ χ hχ
  have hw := (affineVermaUniversal.{u, u} B H φ D hB hφ Λ χ hχ).1
  refine ⟨isSimpleModule_iff_isCoatom.mpr (affineVermaRadical_isCoatom D χ ht), ?_, ⟨?_, ?_⟩, ?_⟩
  · exact fun h => ht ((Submodule.Quotient.mk_eq_zero _).mp h)
  · intro h
    change ι ℂ (h : Carrier D) • q (affineVermaTop D χ) = Λ ⟨h.1, h.2⟩ • q (affineVermaTop D χ)
    calc
      _ = q (ι ℂ (h : Carrier D) • affineVermaTop D χ) := (q.map_smul _ _).symm
      _ = q (Λ ⟨h.1, h.2⟩ • affineVermaTop D χ) := congrArg q (hw.1 h)
      _ = _ := (q.restrictScalars ℂ).map_smul _ _
  · intro x
    change ι ℂ (x : Carrier D) • q (affineVermaTop D χ) = 0
    rw [← q.map_smul, hw.2 x, map_zero]
  · intro y
    obtain ⟨x, rfl⟩ := (affineVermaRadical D χ).mkQ_surjective y
    obtain ⟨F, hF⟩ := affineVermaPBW B H φ D hB hφ Λ χ hχ
    obtain ⟨a, rfl⟩ := F.surjective x
    refine ⟨inclusion (negative D) a, ?_⟩
    change inclusion (negative D) a • q (affineVermaTop D χ) = q (F a)
    rw [← q.map_smul, hF]

theorem affineSimpleUnique : affineSimpleUnique_type.{u, v} := by
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ V _ _ _ f hf
  have ht := affineVermaRadicalProper B H φ D hB hφ Λ χ hχ
  have hR := affineVermaRadical_isCoatom D χ ht
  have hker := f.isCoatom_ker_of_surjective hf
  have heq := le_antisymm
    ((isCoatom_iff_ge_of_le.mp hker).2 _ hR.ne_top (le_affineVermaRadical D χ hker.ne_top))
    (le_affineVermaRadical D χ hker.ne_top)
  let e := (Submodule.quotEquivOfEq _ _ heq).trans (f.quotKerEquivOfSurjective hf)
  have he (x : affineVerma D χ) : e (affineSimpleProjection D χ x) = f x := by
    change e (Submodule.Quotient.mk x) = _
    simp [e]
  refine ⟨e, he, fun E hE => LinearEquiv.ext fun y => ?_⟩
  obtain ⟨x, rfl⟩ := (affineVermaRadical D χ).mkQ_surjective y
  exact (hE x).trans (he x).symm

section Level

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem envelopingCentralGenerator {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ)
    (a : U (Carrier D)) : Commute (ι ℂ (show Carrier D from K_value B)) a := by
  let k : Carrier D := K_value B
  induction a using Shared.Lie.enveloping_induction ℂ (Carrier D) with
  | scalar c => exact (Algebra.commutes c (ι ℂ k)).symm
  | generator x =>
    have h : ⁅k, x⁆ = 0 := by
      change affineBracket_value B (K_value B) x = 0
      exact (affineBracket_eq B (K B) x).symm.trans (centralGenerator B x)
    apply sub_eq_zero.mp
    change (⁅ι ℂ k, ι ℂ x⁆ : U (Carrier D)) = 0
    rw [← (ι ℂ).map_lie, h, map_zero]
  | mul a b ha hb => exact ha.mul_right hb
  | add a b ha hb => exact ha.add_right hb

theorem affineLevelAction : affineLevelAction_type.{u} := by
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ
  let k : Carrier D := K_value B
  let level := affineLevel B H Λ
  let t := affineVermaTop D χ
  let hc := centralCartanElement B H
  let c : cartan D := ⟨hc.1, hc.2⟩
  have htop : ι ℂ k • t = level • t :=
    (affineVermaUniversal.{u, u} B H φ D hB hφ Λ χ hχ).1.1 c
  obtain ⟨F, hF⟩ := affineVermaPBW B H φ D hB hφ Λ χ hχ
  have hM (x : affineVerma D χ) : ι ℂ k • x = level • x := by
    obtain ⟨a, rfl⟩ := F.surjective x
    rw [hF, ← mul_smul, (envelopingCentralGenerator D (inclusion (negative D) a)).eq,
      mul_smul, htop, smul_comm]
  refine ⟨hM, fun y => ?_⟩
  let q := affineSimpleProjection D χ
  obtain ⟨x, rfl⟩ := (affineVermaRadical D χ).mkQ_surjective y
  change ι ℂ k • q x = level • q x
  rw [← q.map_smul, hM]
  exact (q.restrictScalars ℂ).map_smul level x

end Level

end RepTheorySurvey.Affine
