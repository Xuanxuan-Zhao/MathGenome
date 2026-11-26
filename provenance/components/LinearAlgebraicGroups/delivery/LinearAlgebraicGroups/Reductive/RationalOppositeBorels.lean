import Specs.LinearAlgebraicGroups.Reductive.RationalOppositeBorels
import LinearAlgebraicGroups.Relative.RationalCocharacter
import LinearAlgebraicGroups.RootData.BorelNormalizer
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Reductive.RationalOppositeBorels

open _root_.LinearAlgebraicGroups.Specs
open Specs.BorelsAndChambers (IsRegular subgroupRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsMaximalTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.RationalOppositeBorels
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics

open private kBorel_smooth_connected reductive_geometricGroup
  connected_of_geometricallyConnected maximalTorus_of_geometricallyMaximal
  centralizer_of_regular regular_isBorel root_and_opposite_not_in_borel pairing_inv
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_maximal geometricMaximal_of_maximal
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private extendSubgroup extend_subgroupOf subgroupOf_of_extend subgroupIso_of_same
  limits_subgroups_extend opposite_baseChange borel_of_same same_subgroup_symm same_subgroup_trans
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private limitParabolic_root_iff parabolicThroughGeometricTorus
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private opposite_regular from LinearAlgebraicGroups.Flag.StandardParabolics
open private gm_baseChange pointHom from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- A limit cocharacter in a split maximal torus is regular if its limit
parabolic is a Borel. A root of weight zero would place both opposite root
lines in the Borel. -/
private theorem regular_of_limitBorel [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion))
    (hB : IsBorel D.parabolic) (hTB : IsSubgroupOf T D.parabolic) :
    IsRegular T c := by
  intro α hz
  have hroot := (RootData.RootGroups.rootSubgroups G hG T hT hm).2 α.val α.property
  let β : ↥(absoluteRoots T) := ⟨α.val⁻¹, ((hroot.2.1 _).mpr (Or.inr rfl)).1⟩
  have hz' : pairing T.group β.val c = 0 := by
    change pairing T.group α.val⁻¹ c = 0
    rw [pairing_inv _ hT, hz, neg_zero]
  exact root_and_opposite_not_in_borel G hG T D.parabolic hT hm hB hTB α β rfl
    ((limitParabolic_root_iff G T c D α).mpr hz.ge)
    ((limitParabolic_root_iff G T c D β).mpr hz'.ge)

/-- Compare the two limit subgroups along the scalar-extended cocharacter. -/
private theorem scalarExtendedLimits {K : Type u} [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) {c : Cocharacter G.val} (D : LimitDecomposition c)
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange k K).obj (specGroup (groupAlgebra k IntegerCharacters)))
    (he : ∀ (R : TestAlgebra K) (s : Rˣ),
      baseChangePointGroupEquiv K (specGroup (groupAlgebra k IntegerCharacters)) R
        (pointHom e.hom R (unitPoint R s)) = unitPoint ((restrictTestAlgebra k K).obj R) s)
    {d : Cocharacter ((groupBaseChange k K).obj G.val)}
    (hd : e.hom ≫ (groupBaseChange k K).map c = d) (E : LimitDecomposition d) :
    SameSubgroup E.parabolic (extendSubgroup K D.parabolic) ∧
      SameSubgroup E.centralizer (extendSubgroup K D.centralizer) := by
  subst d
  obtain ⟨hp, _, hz⟩ := limits_subgroups_extend G D e he E
  exact ⟨hp, hz⟩

private theorem opposite_geometricBorel [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (c : Cocharacter T.group)
    (D : LimitDecomposition (c ≫ T.inclusion))
    (E : LimitDecomposition (oppositeCocharacter c ≫ T.inclusion))
    (hB : IsBorel D.parabolic) (hTB : IsSubgroupOf T D.parabolic) :
    IsBorel E.parabolic ∧ SameSubgroup E.centralizer T := by
  have hc := regular_of_limitBorel G hG T hT hm c D hB hTB
  have hn := opposite_regular (G := G) (T := T) (c := c) hc
  have hz := centralizer_of_regular G hG T hT hm (oppositeCocharacter c) hn E
  exact ⟨regular_isBorel G hG T hT hm (oppositeCocharacter c) hn E hz, hz⟩

/-- The opposite limit parabolic is a rational Borel when the positive one
is, and its centralizer is the specified common torus. -/
private theorem opposite_limitBorel (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hm : IsGeometricallyMaximal T)
    (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion))
    (E : LimitDecomposition (oppositeCocharacter (c ≫ T.inclusion)))
    (hB : IsKBorel D.parabolic) (hTB : IsSubgroupOf T D.parabolic) :
    IsKBorel E.parabolic ∧ SameSubgroup E.centralizer T := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Gbar := GeometricGroup G
  let Tbar := extendSubgroup K T
  have hGbar := reductive_geometricGroup G hG
  have hTm : IsMaximalTorus Tbar := hm.choose_spec
  have hTbar := split_of_maximal (A := Gbar) hTm
  have hTgeom := geometricMaximal_of_maximal Gbar Tbar hTm
  obtain ⟨e, he⟩ := gm_baseChange k K
  let cbar : Cocharacter Tbar.group := e.hom ≫ F.map c
  have hc : e.hom ≫ F.map (c ≫ T.inclusion) = cbar ≫ Tbar.inclusion := by
    change e.hom ≫ F.map (c ≫ T.inclusion) = (e.hom ≫ F.map c) ≫ F.map T.inclusion
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨Dbar⟩ := existsLimitDecomposition Gbar (cbar ≫ Tbar.inclusion)
  obtain ⟨hDP, _⟩ := scalarExtendedLimits G D e he hc Dbar
  have hDbarB : IsBorel Dbar.parabolic :=
    borel_of_same (H := Gbar) hB.choose_spec (same_subgroup_symm hDP)
  have hDbarT : IsSubgroupOf Tbar Dbar.parabolic := by
    obtain ⟨f, hf⟩ := extend_subgroupOf (K := K) hTB
    obtain ⟨g, hg⟩ := hDP.2
    exact ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩
  have hn : e.hom ≫ F.map (oppositeCocharacter (c ≫ T.inclusion)) =
      oppositeCocharacter cbar ≫ Tbar.inclusion := by
    rw [← opposite_baseChange (c ≫ T.inclusion) e he, hc]
    change oppositeCocharacter (cbar ≫ Tbar.inclusion) =
      oppositeCocharacter cbar ≫ Tbar.inclusion
    simp only [oppositeCocharacter, Category.assoc]
  obtain ⟨Ebar⟩ := existsLimitDecomposition Gbar (oppositeCocharacter cbar ≫ Tbar.inclusion)
  obtain ⟨hEB, hZ⟩ :=
    opposite_geometricBorel Gbar hGbar Tbar hTbar hTgeom cbar Dbar Ebar hDbarB hDbarT
  obtain ⟨hEP, hEZ⟩ := scalarExtendedLimits G E e he hn Ebar
  have h := same_subgroup_trans (same_subgroup_symm hEZ) hZ
  refine ⟨⟨(extendSubgroup K E.parabolic).isClosedImmersion,
    borel_of_same (H := Gbar) hEB hEP⟩, ⟨?_, ?_⟩⟩
  · exact subgroupOf_of_extend (K := K) h.1
  · exact subgroupOf_of_extend (K := K) h.2

/-- The scheme intersection of opposite limit parabolics is their common
centralizer. The argument tests sections over arbitrary schemes. -/
private theorem intersection_of_opposite_limits (G : AffineAlgebraicGroup k)
    (c : Cocharacter G.val) (D : LimitDecomposition c)
    (E : LimitDecomposition (oppositeCocharacter c)) {B T : ClosedSubgroup G.val}
    (hBD : IsSubgroupOf B D.parabolic) (hZ : SameSubgroup E.centralizer T)
    (i : T.group ⟶ B.group) (hi : i ≫ B.inclusion = T.inclusion) :
    ∃ j : T.group ⟶ E.parabolic.group,
      j ≫ E.parabolic.inclusion = T.inclusion ∧
        IsPullback i.hom.hom j.hom.hom B.inclusion.hom.hom E.parabolic.inclusion.hom.hom := by
  obtain ⟨e, he⟩ := subgroupIso_of_same hZ
  let j := e.inv ≫ E.sectionMap
  have hj : j ≫ E.parabolic.inclusion = T.inclusion := by
    change (e.inv ≫ E.sectionMap) ≫ E.parabolic.inclusion = _
    rw [Category.assoc, E.section_in_G, ← he, Iso.inv_hom_id_assoc]
  have hjlimit : j ≫ E.limit = e.inv := by
    change (e.inv ≫ E.sectionMap) ≫ E.limit = _
    rw [Category.assoc, E.section_limit, Category.comp_id]
  refine ⟨j, hj, ⟨⟨(Grp.forget _).congr_map (hi.trans hj.symm)⟩, ⟨?_⟩⟩⟩
  letI : Mono B.inclusion.hom.hom := mono_over _ B.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := mono_over _ T.isClosedImmersion
  have hright (C : PullbackCone B.inclusion.hom.hom E.parabolic.inclusion.hom.hom) :
      (C.snd ≫ (E.limit ≫ e.hom).hom.hom) ≫ j.hom.hom = C.snd := by
    let X := C.pt
    let l : X ⟶ T.group.X := C.snd ≫ (E.limit ≫ e.hom).hom.hom
    let q : X ⟶ E.parabolic.group.X := (l ≫ j.hom.hom)⁻¹ * C.snd
    have hl : (l ≫ j.hom.hom) ≫ E.limit.hom.hom = C.snd ≫ E.limit.hom.hom := by
      change ((C.snd ≫ (E.limit ≫ e.hom).hom.hom) ≫ j.hom.hom) ≫ E.limit.hom.hom = _
      simp only [Category.assoc]
      change C.snd ≫ ((E.limit ≫ e.hom) ≫ j ≫ E.limit).hom.hom = _
      rw [hjlimit, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have hq : q ≫ E.limit.hom.hom = toUnit X ≫ η[E.centralizer.group.X] := by
      simp only [q, MonObj.mul_comp, GrpObj.inv_comp, hl, inv_mul_cancel]
      rfl
    obtain ⟨n, hn, _⟩ := E.isKernel.exists_lift q (toUnit X) hq
    obtain ⟨b, hb⟩ := hBD
    let p : X ⟶ B.group.X := (l ≫ i.hom.hom)⁻¹ * C.fst
    have himage : n ≫ E.contracting.inclusion.hom.hom = p ≫ B.inclusion.hom.hom := by
      rw [← show E.contractingToParabolic.hom.hom ≫ E.parabolic.inclusion.hom.hom =
        E.contracting.inclusion.hom.hom from (Grp.forget _).congr_map E.contracting_in_G,
        ← Category.assoc, hn]
      simp only [p, q, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc,
        show j.hom.hom ≫ E.parabolic.inclusion.hom.hom = T.inclusion.hom.hom
          from (Grp.forget _).congr_map hj,
        show i.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom
          from (Grp.forget _).congr_map hi, C.condition]
    have himage' : n ≫ E.contracting.inclusion.hom.hom =
        (p ≫ b.hom.hom) ≫ D.parabolic.inclusion.hom.hom := by
      rw [Category.assoc, show b.hom.hom ≫ D.parabolic.inclusion.hom.hom =
        B.inclusion.hom.hom from (Grp.forget _).congr_map hb, himage]
    obtain ⟨a, ha, _⟩ := (oppositeLimitIntersection G c D E).exists_lift
      n (p ≫ b.hom.hom) himage'
    have hn1 : n = 1 := by rw [← ha, toUnit_unique a (toUnit X)]; rfl
    have hq1 : q = 1 := by
      rw [← hn, hn1, MonObj.one_comp]
    exact inv_mul_eq_one.mp hq1
  apply PullbackCone.IsLimit.mk _ (fun C => C.snd ≫ (E.limit ≫ e.hom).hom.hom)
  · intro C
    apply (cancel_mono B.inclusion.hom.hom).mp
    change (C.snd ≫ (E.limit ≫ e.hom).hom.hom) ≫ i.hom.hom ≫ B.inclusion.hom.hom =
      C.fst ≫ B.inclusion.hom.hom
    rw [show i.hom.hom ≫ B.inclusion.hom.hom = j.hom.hom ≫ E.parabolic.inclusion.hom.hom
      from (Grp.forget _).congr_map (hi.trans hj.symm), ← Category.assoc, hright C, ← C.condition]
  · exact hright
  · intro C f _ hg
    apply (cancel_mono T.inclusion.hom.hom).mp
    have hj' : j.hom.hom ≫ E.parabolic.inclusion.hom.hom = T.inclusion.hom.hom :=
      (Grp.forget _).congr_map hj
    calc
      f ≫ T.inclusion.hom.hom = (f ≫ j.hom.hom) ≫ E.parabolic.inclusion.hom.hom := by
        rw [Category.assoc, hj']
      _ = C.snd ≫ E.parabolic.inclusion.hom.hom := by rw [hg]
      _ = (C.snd ≫ (E.limit ≫ e.hom).hom.hom) ≫ T.inclusion.hom.hom := by
        rw [← hj', ← Category.assoc, hright C]

/-- Every specified rational Borel has an opposite over the ground field. -/
theorem rationalOppositeBorelsExist : RationalOppositeBorelsExist.{u} := by
  intro k _ _ G hG B hB
  obtain ⟨hBs, hBc⟩ := kBorel_smooth_connected G B hB
  have hP : Specs.BorelProper.IsParabolic G B :=
    ⟨hG, hBs, hB.choose, _, hB.choose_spec, ⟨𝟙 _, Category.id_comp _⟩⟩
  obtain ⟨S, hS, hSm⟩ := MaximalToriExist.geometricallyMaximalTorusExists
    (closedSubgroupAlgebraicGroup B) hBs hBc
  let T := subgroupOfSubgroup B S
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let Gbar := GeometricGroup G
  let Bbar := extendSubgroup K B
  let Sbar := extendSubgroup K S
  have hTbar : subgroupOfSubgroup Bbar Sbar = extendSubgroup K T := by
    change Specs.ClosedSubgroup.mk _ (F.map S.inclusion ≫ F.map B.inclusion) _ =
      Specs.ClosedSubgroup.mk _ (F.map (S.inclusion ≫ B.inclusion)) _
    congr 1
    exact (F.map_comp S.inclusion B.inclusion).symm
  have hGbar := reductive_geometricGroup G hG
  have hGc : ConnectedSpace Gbar.val.X.left := connected_of_geometricallyConnected hGbar.2.1
  have hSm' : IsMaximalTorus Sbar := hSm.choose_spec
  have hTmax : IsGeometricallyMaximal T := by
    refine ⟨(extendSubgroup K T).isClosedImmersion, ?_⟩
    change IsMaximalTorus (extendSubgroup K T)
    rw [← hTbar]
    exact (MaximalToriConjugate.borelMaximalTorusIff Gbar hGbar.1 hGc Bbar hB.choose_spec Sbar).mp hSm'
  obtain ⟨c, D, hBD, _, _⟩ := parabolicThroughGeometricTorus
    LinearAlgebraicGroups.Flag.StandardParabolics.standardParabolicClassification G B hP S hS hSm
  obtain ⟨E⟩ := existsLimitDecomposition G (oppositeCocharacter (c ≫ T.inclusion))
  have hD : IsKBorel D.parabolic :=
    ⟨(extendSubgroup K D.parabolic).isClosedImmersion,
      borel_of_same (H := Gbar) hB.choose_spec
        ⟨extend_subgroupOf hBD.1, extend_subgroupOf hBD.2⟩⟩
  have hTD : IsSubgroupOf T D.parabolic := by
    obtain ⟨f, hf⟩ := hBD.1
    exact ⟨S.inclusion ≫ f, by rw [Category.assoc, hf]; rfl⟩
  obtain ⟨hE, hZ⟩ := opposite_limitBorel G hG T hTmax c D E hD hTD
  obtain ⟨j, hj, hsq⟩ := intersection_of_opposite_limits G _ D E hBD.1 hZ S.inclusion rfl
  have hTk := maximalTorus_of_geometricallyMaximal G T hS hTmax
  exact ⟨E.parabolic, T, hB, hE, hTk, hTmax, S.inclusion, j, rfl, hj, hsq⟩

end

end LinearAlgebraicGroups.Reductive.RationalOppositeBorels
