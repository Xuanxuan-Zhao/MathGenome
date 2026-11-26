import Specs.LinearAlgebraicGroups.Arithmetic.LocalMinimalParabolicDynamics
import LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
import LinearAlgebraicGroups.Classification.RankTwoRelations
import LinearAlgebraicGroups.Descent.RelativeRank
import LinearAlgebraicGroups.Relative.RelativeBruhat
import LinearAlgebraicGroups.Relative.RelativeChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Topology
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMinimalParabolicDynamics

open _root_.LinearAlgebraicGroups.Specs
  (AffineAlgebraicGroup ClosedSubgroup GroupScheme SubgroupSections)
open Specs.Arithmetic.LocalMinimalParabolicDynamics
  (ExistsProperMinimalParabolic NormalSubgroupCentralizesCocharacter)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsReductive)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.Relative.RelativeChambers (IsRegular)
open Specs.RelativeRank (HasProperParabolic IsCentralCocharacter)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open LocalAlgebraicTransport (RationalPoints evaluation pointTopology)
open CocharacterDynamics (LimitDecomposition HasExtension HasLimit
  existsLimitDecomposition oppositeCocharacter oppositeLimit_intersection_onPoints)

open private unipotentGenerated_eq_bot_of_noProperParabolic
  from LinearAlgebraicGroups.Arithmetic.TrialitarianLocalForms
open private opposite_pairing from LinearAlgebraicGroups.Classification.RankTwoRelations
open private minimalParabolicExists from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private section_conjugated from LinearAlgebraicGroups.Relative.RelativeBruhat
open private isIso_of_section from LinearAlgebraicGroups.Relative.RelativeChambers
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_hasLimit from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private pairing_inv from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private centralizes_opposite_iff parabolic_of_cast from LinearAlgebraicGroups.RootData.RankOneFlag

variable {F : Type u} [Field F]

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
private theorem rationalPointsT2 [TopologicalSpace F] [T2Space F]
    (J : AffineAlgebraicGroup F) :
    letI := pointTopology J.val.X
    T2Space (RationalPoints J.val.X) := by
  letI := pointTopology J.val.X
  letI := J.property.1
  let ev (p : RationalPoints J.val.X) (a : Γ(J.val.X.left, ⊤)) := evaluation p a
  have hinj : Function.Injective ev := by
    intro p q h
    apply Over.OverMorphism.ext
    apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of F)).hom).mp
    apply CommRingCat.hom_ext
    exact DFunLike.ext _ _ (congrFun h)
  exact (show IsEmbedding ev from ⟨⟨rfl⟩, hinj⟩).t2Space

private theorem isIso_inclusion_of_contains_whole {G : GroupScheme F}
    {P Q : ClosedSubgroup G} [IsIso P.inclusion] (h : IsSubgroupOf P Q) :
    IsIso Q.inclusion := by
  obtain ⟨f, hf⟩ := h
  apply isIso_of_section Q (inv P.inclusion ≫ f)
  rw [Category.assoc, hf, IsIso.inv_hom_id]

set_option linter.style.haveILetI false in
private theorem hasProperParabolic_of_dense_radicals
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (J : AffineAlgebraicGroup F) (hJ : IsReductive J)
    (hne : ∃ g : RationalPoints J.val.X, g ≠ 1)
    (hdense : letI := pointTopology J.val.X
      Dense {g : RationalPoints J.val.X | ∃ x ∈ unipotentGenerated J,
        toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ x = g}) :
    HasProperParabolic J := by
  by_contra h
  have hbot := unipotentGenerated_eq_bot_of_noProperParabolic hJ h
  letI := pointTopology J.val.X
  letI := rationalPointsT2 J
  have hsub : {g : RationalPoints J.val.X | ∃ x ∈ unipotentGenerated J,
      toUnit ((testSpec F).obj (op (CommAlgCat.of F F))) ≫ x = g} ⊆
      ({1} : Set (RationalPoints J.val.X)) := by
    rintro g ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, Set.mem_singleton_iff]
    exact MonObj.comp_one _
  obtain ⟨g, hg⟩ := hne
  exact hg (closure_minimal hsub isClosed_singleton (hdense g))

theorem existsProperMinimalParabolic : ExistsProperMinimalParabolic.{u} := by
  intro F _ _ _ _ J hJ hne hdense
  obtain ⟨Q, hQ, hQproper⟩ := hasProperParabolic_of_dense_radicals J hJ hne hdense
  obtain ⟨P, hP⟩ := minimalParabolicExists J hJ
  have hPproper : ¬ IsIso P.inclusion := by
    intro h
    apply hQproper
    apply isIso_inclusion_of_contains_whole (P := P)
    exact hP.2 Q hQ ⟨Q.inclusion ≫ inv P.inclusion, by simp⟩
  obtain ⟨S, hS, hSP, _⟩ := Relative.RelativeWeylScheme.commonMaximalSplitTorus J hJ P P hP hP
  obtain ⟨c, D, hPD⟩ := Relative.RelativeChambers.parabolicThroughSplitTorus J S hS P hP.1 hSP
  have hD := Descent.RelativeRank.properDynamicParabolic J hJ (c ≫ S.inclusion) D
  have hmin : IsMinimalParabolic J D.parabolic := by
    refine ⟨hD.1, fun B hB hBD ↦ ?_⟩
    exact subgroupOf_trans hPD.2
      (hP.2 B hB (subgroupOf_trans hBD hPD.2))
  have hproper : ¬ IsIso D.parabolic.inclusion := fun _ ↦
    hPproper (isIso_inclusion_of_contains_whole hPD.2)
  refine ⟨S, c, D, hS, (Relative.RelativeChambers.minimalLimitParabolic J hJ S hS c D).mp hmin,
    hmin, hproper, ?_⟩
  have hnc := hD.2.mp hproper
  unfold IsCentralCocharacter at hnc
  push Not at hnc
  exact hnc

private theorem centralizes_of_opposite_extensions {J : AffineAlgebraicGroup F}
    (c : Cocharacter J.val) (E : LimitDecomposition (oppositeCocharacter c))
    {g : RationalPoints J.val.X} (h : HasExtension c g)
    (hneg : HasExtension (oppositeCocharacter c) g) : Centralizes c g := by
  let R := CommAlgCat.of F F
  obtain ⟨p, hp⟩ := (E.parabolic_points R g).mp hneg
  let z : RationalPoints J.val.X := p ≫ E.limit.hom.hom ≫ E.centralizer.inclusion.hom.hom
  have hzc' : Centralizes (oppositeCocharacter c) z :=
    (E.centralizer_points _ z).mpr ⟨p ≫ E.limit.hom.hom, Category.assoc _ _ _⟩
  have hzc : Centralizes c z := (centralizes_opposite_iff c z).mp hzc'
  have hlim : HasLimit (oppositeCocharacter c) g z := by
    have hh := E.limit_points R p
    change HasLimit (oppositeCocharacter c) _ z at hh
    rwa [hp] at hh
  obtain ⟨z₀, hz₀⟩ := h
  have hplus := hz₀.mul (centralizes_hasLimit c hzc).inv
  have hminus : HasLimit (oppositeCocharacter c) (g * z⁻¹) (1 : RationalPoints J.val.X) :=
    (mul_inv_cancel z) ▸ (hlim.mul (centralizes_hasLimit (oppositeCocharacter c) hzc').inv)
  have he := oppositeLimit_intersection_onPoints J.property.1 c (g * z⁻¹)
    ⟨_, hplus⟩ hminus
  have hg : g = z := mul_inv_eq_one.mp he
  simpa only [hg] using hzc

theorem normalSubgroupCentralizesCocharacter : NormalSubgroupCentralizesCocharacter.{u} := by
  intro F _ J hJ S c D hS hc hmin _ _ N hNormal hN x hx
  let R := CommAlgCat.of F F
  let X := (testSpec F).obj (op R)
  have hcneg : IsRegular S (oppositeCocharacter c) := by
    intro a
    have h := opposite_pairing hS.1 a.val⁻¹ c
    rw [inv_inv, pairing_inv _ hS.1] at h
    rw [h]
    exact neg_ne_zero.mpr (hc a)
  obtain ⟨E⟩ := existsLimitDecomposition J (oppositeCocharacter c ≫ S.inclusion)
  have hE := (Relative.RelativeChambers.minimalLimitParabolic J hJ S hS
    (oppositeCocharacter c) E).mpr hcneg
  obtain ⟨g, hg⟩ := Relative.MaximalSplitTori.minimalParabolicsConjugate J D.parabolic E.parabolic
    hmin hE
  let t : RationalPoints J.val.X := toUnit X ≫ g
  have hxE : x ∈ SubgroupSections E.parabolic X := by
    have hy := hN (hNormal.conj_mem' x hx t)
    have hz := section_conjugated hg (Y := X) hy
    change t * (t⁻¹ * x * t) * t⁻¹ ∈ SubgroupSections E.parabolic X at hz
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right] using hz
  have hcomp : oppositeCocharacter c ≫ S.inclusion = oppositeCocharacter (c ≫ S.inclusion) := by
    simp only [oppositeCocharacter, Category.assoc]
  let Eneg : LimitDecomposition (oppositeCocharacter (c ≫ S.inclusion)) := hcomp ▸ E
  have hEq : Eneg.parabolic = E.parabolic := parabolic_of_cast hcomp E
  apply centralizes_of_opposite_extensions (c ≫ S.inclusion) Eneg
  · exact (D.parabolic_points R x).mpr (hN hx)
  · apply (Eneg.parabolic_points R x).mpr
    change x ∈ SubgroupSections Eneg.parabolic X
    rwa [hEq]

end LinearAlgebraicGroups.Arithmetic.LocalMinimalParabolicDynamics
