import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitRadicalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.Parabolics
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitRadicalGeneration

open LinearAlgebraicGroups.Specs
open Specs.BorelProper (IsParabolic)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsTorus IsUnipotentRadical)
open Specs.QuasiSplitLocalGeneration (generatedByBorelRadicals)
open Specs.QuasiSplitOrbitAmbientWords (groundPointIso)
open Specs.QuasiSplitPinnedPairModel (BorelPair)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.Arithmetic.RelativeRayGeneration (unipotentGenerated)
open CocharacterDynamics (LimitDecomposition existsLimitDecomposition oppositeCocharacter)

open private kBorel_smooth_connected connected_of_geometricallyConnected
  reductive_geometricGroup regular_of_centralizer regular_isBorel centralizer_of_cast
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extendSubgroup extend_subgroupOf centralizes_opposite_iff same_subgroup_of_same_sections
  limits_subgroups_extend same_subgroup_trans borel_of_same parabolic_of_cast
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private split_of_maximal geometricMaximal_of_maximal
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private borelDefiningCocharacter from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private limitBorelIntersection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
open private multiplicativeBaseChange multiplicativeBaseChange_unit extendCocharacter
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private terminalPointHom terminalSubgroup_map
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration

noncomputable section

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

set_option backward.isDefEq.respectTransparency false in
private theorem maximalTorusInBorel (hG : IsReductive G)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) :
    ∃ T : ClosedSubgroup G.val, IsTorus T.group ∧ IsGeometricallyMaximal T ∧ IsSubgroupOf T B := by
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected G B hB
  obtain ⟨S, hS, _, hSm⟩ :=
    MaximalToriExist.geometricallyMaximalTorusExists (closedSubgroupAlgebraicGroup B) hs hc
  let K := AlgebraicClosure F
  let H := GeometricGroup G
  let T := subgroupOfSubgroup B S
  let Bbar := extendSubgroup K B
  let Tbar := extendSubgroup K T
  let Sbar := extendSubgroup K S
  have hH := reductive_geometricGroup G hG
  have hBbar : GeometricBorelConjugacy.IsBorel Bbar := hB.choose_spec
  have hM := (MaximalToriConjugate.borelMaximalTorusIff H hH.1
    (connected_of_geometricallyConnected hH.2.1) Bbar hBbar Sbar).mp hSm
  have hcomp : (subgroupOfSubgroup Bbar Sbar).inclusion = Tbar.inclusion := by
    change (groupBaseChange F K).map S.inclusion ≫ (groupBaseChange F K).map B.inclusion =
      (groupBaseChange F K).map (S.inclusion ≫ B.inclusion)
    exact ((groupBaseChange F K).map_comp _ _).symm
  have hTbar : IsMaximalTorus Tbar :=
    maximal_of_square (Iso.refl _) (subgroupOfSubgroup Bbar Sbar) Tbar (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using hcomp.symm) hM
  exact ⟨T, hS, ⟨Tbar.isClosedImmersion, hTbar⟩, ⟨S.inclusion, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem limitIsBorel (hG : IsReductive G) (T : ClosedSubgroup G.val)
    (hT : IsGeometricallyMaximal T) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion)) (hZ : SameSubgroup D.centralizer T) :
    IsKBorel D.parabolic := by
  let K := AlgebraicClosure F
  let H := GeometricGroup G
  let Tbar := extendSubgroup K T
  let cbar : Cocharacter Tbar.group := extendCocharacter K c
  have hcomp : extendCocharacter K (c ≫ T.inclusion) = cbar ≫ Tbar.inclusion := by
    change (multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map (c ≫ T.inclusion) =
      ((multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map c) ≫
        (groupBaseChange F K).map T.inclusion
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨E₀⟩ := existsLimitDecomposition H (extendCocharacter K (c ≫ T.inclusion))
  let E : LimitDecomposition (cbar ≫ Tbar.inclusion) := hcomp ▸ E₀
  obtain ⟨hP, _, hC⟩ :=
    limits_subgroups_extend G D (multiplicativeBaseChange F K) (multiplicativeBaseChange_unit K) E₀
  have hE : SameSubgroup E.centralizer Tbar := by
    change SameSubgroup (hcomp ▸ E₀ : LimitDecomposition (cbar ≫ Tbar.inclusion)).centralizer Tbar
    rw [centralizer_of_cast hcomp E₀]
    exact same_subgroup_trans hC ⟨extend_subgroupOf hZ.1, extend_subgroupOf hZ.2⟩
  have hH := reductive_geometricGroup G hG
  have hm : IsMaximalTorus Tbar := hT.choose_spec
  have hs := split_of_maximal (A := H) hm
  have hm' := geometricMaximal_of_maximal H Tbar hm
  have hr := regular_of_centralizer H hH Tbar hs hm' cbar E hE
  have hb := regular_isBorel H hH Tbar hs hm' cbar hr E hE
  refine ⟨(extendSubgroup K D.parabolic).isClosedImmersion, borel_of_same (H := H) hb ?_⟩
  change SameSubgroup (hcomp ▸ E₀ : LimitDecomposition (cbar ≫ Tbar.inclusion)).parabolic _
  rw [parabolic_of_cast hcomp E₀]
  exact hP

set_option backward.isDefEq.respectTransparency false in
private theorem oppositeBorelPair (hG : IsReductive G)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) : Nonempty (BorelPair G) := by
  obtain ⟨T, ht, hm, hTB⟩ := maximalTorusInBorel hG B hB
  obtain ⟨c, D, hBD, hC⟩ := borelDefiningCocharacter G hG B T hB ht hm hTB
  let c' := oppositeCocharacter c
  have hop : oppositeCocharacter (c ≫ T.inclusion) = c' ≫ T.inclusion := by
    unfold c' oppositeCocharacter
    rw [Category.assoc]
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter (c ≫ T.inclusion))
  have hEC : RepresentsSubgroup T
      (fun _ g ↦ Centralizes (oppositeCocharacter (c ≫ T.inclusion)) g) :=
    fun X g ↦ (centralizes_opposite_iff (c ≫ T.inclusion) g).trans (hC X g)
  have hZ : SameSubgroup E.centralizer T := same_subgroup_of_same_sections E.centralizer_points hEC
  have hBE : IsKBorel E.parabolic := by
    let E' : LimitDecomposition (c' ≫ T.inclusion) := hop ▸ E
    have hz' : SameSubgroup E'.centralizer T := by
      change SameSubgroup (hop ▸ E : LimitDecomposition (c' ≫ T.inclusion)).centralizer T
      rw [centralizer_of_cast hop E]
      exact hZ
    have hb := limitIsBorel hG T hm c' E' hz'
    change IsKBorel (hop ▸ E : LimitDecomposition (c' ≫ T.inclusion)).parabolic at hb
    rwa [parabolic_of_cast hop E] at hb
  have hTE : IsSubgroupOf T E.parabolic :=
    subgroupOf_trans hZ.2 ⟨E.sectionMap, E.section_in_G⟩
  have hBP := (QuasiSplitFixedWeyl.borelIsMinimalParabolic G hG B hB).1
  obtain ⟨_, _, _, U, _, _, _, _, _, _, _, _, _, _, hu, _⟩ :=
    Relative.Parabolics.rationalParabolics.1 G B hBP
  have hv := (Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG _ E).1
  exact ⟨⟨B, E.parabolic, T, U, contractingSubgroup E, hB, hBE, ht, hm,
    limitBorelIntersection G T B D E hBD hZ hTB hTE, hu, hv⟩⟩

private theorem radicalSections_le (P : ClosedSubgroup G.val) (hP : IsParabolic G P)
    (U : ClosedSubgroup P.group) (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U) :
    SubgroupSections (subgroupOfSubgroup P U) (𝟙_ (SchemeOver F)) ≤ unipotentGenerated G := by
  apply le_iSup_of_le P
  apply le_iSup_of_le hP
  apply le_iSup_of_le U
  exact le_iSup
    (fun _ : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U =>
      SubgroupSections (subgroupOfSubgroup P U) (𝟙_ (SchemeOver F))) hU

set_option backward.isDefEq.respectTransparency false in
private theorem terminalGeneration (hG : IsReductive G) (M : BorelPair G)
    (hgen : generatedByBorelRadicals M = ⊤) : unipotentGenerated G = ⊤ := by
  let U := SubgroupSections (M.subgroup .positiveRadical) (𝟙_ (SchemeOver F))
  let V := SubgroupSections (M.subgroup .negativeRadical) (𝟙_ (SchemeOver F))
  let f := terminalPointHom G.val
  have hU : U ≤ unipotentGenerated G :=
    radicalSections_le M.positive
      (QuasiSplitFixedWeyl.borelIsMinimalParabolic G hG M.positive M.positiveBorel).1
      M.positiveRadical M.positiveUnipotentRadical
  have hV : V ≤ unipotentGenerated G :=
    radicalSections_le M.negative
      (QuasiSplitFixedWeyl.borelIsMinimalParabolic G hG M.negative M.negativeBorel).1
      M.negativeRadical M.negativeUnipotentRadical
  have hmap : (U ⊔ V).map f = ⊤ := by
    rw [Subgroup.map_sup]
    change (SubgroupSections (M.subgroup .positiveRadical) _).map f ⊔
      (SubgroupSections (M.subgroup .negativeRadical) _).map f = ⊤
    rw [terminalSubgroup_map, terminalSubgroup_map]
    exact hgen
  have hf : Function.Injective f := by
    intro x y h
    change (groundPointIso F).inv ≫ x = (groundPointIso F).inv ≫ y at h
    exact (cancel_epi (groundPointIso F).inv).mp h
  apply top_unique
  intro g _
  have hg : f g ∈ (U ⊔ V).map f := hmap.symm ▸ Subgroup.mem_top (f g)
  obtain ⟨p, hp, he⟩ := hg
  exact hf he ▸ (sup_le hU hV hp)

theorem quasiSplitRadicalGeneration :
    Specs.Arithmetic.QuasiSplitRadicalGeneration.Statement.{u} := by
  intro F _ hF G hG hsc ⟨hred, B, hB⟩
  obtain ⟨M⟩ := oppositeBorelPair hred B hB
  exact terminalGeneration hred M
    (QuasiSplitLocalGeneration.quasiSplitLocalGeneration hF G hG hsc M)

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitRadicalGeneration
