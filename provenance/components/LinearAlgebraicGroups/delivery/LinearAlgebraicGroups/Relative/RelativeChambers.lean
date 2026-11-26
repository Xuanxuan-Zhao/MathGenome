import Specs.LinearAlgebraicGroups.Relative.RelativeChambers
import LinearAlgebraicGroups.Relative.MaximalSplitTori
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.TensorProduct.Basis

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct BigOperators

universe u

namespace LinearAlgebraicGroups.Relative.RelativeChambers

open LinearAlgebraicGroups.Specs
open Specs.Relative.RelativeChambers (IsRegular IsChamber nonnegativeRoots)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots adjointWeightSpace adjointWeightVectors pairing)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsTorus)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.BorelProper (IsParabolic)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition existsLimitDecomposition lieImage multiplyFactors
  limitSubgroupsSmooth geometricallyConnectedLimitSubgroups lieWeights)

open private exists_maximal_torus_over restrictSubgroup inclusion_mono
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private geometricMaximal_of_rationalMaximal limitParabolic_root_iff
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private cocharacterFactorsThroughMaximalSplit limitIsParabolic
  from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private preservesSignsOnFiniteSet connected_of_geometricallyConnected
  subgroupOf_of_lieImage isIso_of_closedImmersion_of_differential
  torus_subgroupOf_centralizer limitLie_weightSpans lieImage_mono
  pairing_one map_weightVector map_parabolic_of_comp differential_injective cocharacter_weight_coordinates
  splitTorus_baseChange
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private canonicalZero_eq isTorus_of_split zeroWeightVectors_iff_centralizes
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private adjointWeightsInternal from LinearAlgebraicGroups.RootData.RootGroups
open private subgroupOf_trans factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private subgroupIso_of_same subgroup_inclusion_of_represents same_subgroup_trans
  same_subgroup_symm parabolic_of_cast from LinearAlgebraicGroups.RootData.RankOneFlag
open private factor_closed isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private conjugationAction isFixedBy_conjugation_iff
  from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private centralizes_iff mono_over from LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

abbrev relativeRoots : Specs.Relative.RelativeChambers.RelativeRootsType.{u} :=
  Specs.Relative.RelativeChambers.relativeRoots

theorem relativeRootsFinite : Specs.Relative.RelativeChambers.RelativeRootsFinite.{u} :=
  RootData.CharacterPairing.finiteAbsoluteRoots

theorem maximalTorusOverSplitTorus :
    Specs.Relative.RelativeChambers.MaximalTorusOverSplitTorus.{u} := by
  intro k _ G hG S hS
  obtain ⟨T, hT, hST⟩ := exists_maximal_torus_over G S (isTorus_of_split hS.1)
  exact ⟨T, hT.1,
    geometricMaximal_of_rationalMaximal G hG.1
      (connected_of_geometricallyConnected hG.2.1) T hT, hST⟩

theorem parabolicThroughSplitTorus :
    Specs.Relative.RelativeChambers.ParabolicThroughSplitTorus.{u} := by
  intro k _ G S hS P hP hSP
  obtain ⟨j, hj⟩ := hSP
  let A := closedSubgroupAlgebraicGroup P
  let S' := restrictSubgroup S P j hj
  obtain ⟨T, hT, hST⟩ := exists_maximal_torus_over A S' (isTorus_of_split hS.1)
  obtain ⟨b, hb⟩ := hST
  obtain ⟨c, D, hPD, _, _⟩ := RationalCocharacter.rationalParabolicThroughTorus G P hP T hT
  let Tg := subgroupOfSubgroup P T
  have hb' : b ≫ Tg.inclusion = S.inclusion := by
    change b ≫ T.inclusion ≫ P.inclusion = S.inclusion
    rw [← Category.assoc, hb]
    exact hj
  obtain ⟨a, ha⟩ := cocharacterFactorsThroughMaximalSplit G S Tg hS hT.1 b hb' c
  have hc : c ≫ Tg.inclusion = a ≫ S.inclusion := by
    calc
      c ≫ Tg.inclusion = (a ≫ b) ≫ Tg.inclusion := congrArg (· ≫ Tg.inclusion) ha.symm
      _ = a ≫ S.inclusion := by rw [Category.assoc, hb']
  refine ⟨a, hc ▸ D, ?_⟩
  change SameSubgroup P (hc ▸ D : LimitDecomposition (a ≫ S.inclusion)).parabolic
  rwa [parabolic_of_cast]

theorem limitParabolicThroughSplitTorus :
    Specs.Relative.RelativeChambers.LimitParabolicThroughSplitTorus.{u} := by
  intro k _ G hG S hS c D
  exact ⟨limitIsParabolic G hG _ D,
    subgroupOf_trans (torus_subgroupOf_centralizer hS c D) ⟨D.sectionMap, D.section_in_G⟩⟩

/-- Every nonzero tangent weight in a smooth connected subgroup containing
the split torus can be checked after applying the subgroup's Lie inclusion. -/
private theorem limitContains_of_lieImage
    (G : AffineAlgebraicGroup k) (S B : ClosedSubgroup G.val) (hS : IsSplitTorus S.group)
    (hBs : Smooth B.group.X.hom) (hBc : ConnectedSpace B.group.X.left)
    (hSB : IsSubgroupOf S B)
    (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion))
    (hLie : lieImage B ⊆ lieImage D.parabolic) : IsSubgroupOf B D.parabolic := by
  classical
  obtain ⟨j, hj⟩ := hSB
  let A := closedSubgroupAlgebraicGroup B
  let S' : ClosedSubgroup A.val := restrictSubgroup S B j hj
  let inclusion : A.val ⟶ G.val := B.inclusion
  letI : Smooth A.val.X.hom := hBs
  letI : ConnectedSpace A.val.X.left := hBc
  obtain ⟨E⟩ := existsLimitDecomposition A (c ≫ j)
  let s := identityLieStructure A
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : AddCommGroup (Lie k A.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k A.val) := s.lieAlgebra.toModule
  letI : Mono inclusion.hom.hom := mono_over _ B.isClosedImmersion
  let W (χ : Character S.group) := adjointWeightSpace S' χ s
  have htop : (⨆ χ : {χ : Character S.group // 0 ≤ pairing S.group χ c}, W χ.val) = ⊤ := by
    apply top_unique
    rw [← (adjointWeightsInternal A S' hS s).submodule_iSup_eq_top]
    apply iSup_le
    intro χ
    by_cases hχ : 0 ≤ pairing S.group χ c
    · exact le_iSup (fun χ : {χ : Character S.group // 0 ≤ pairing S.group χ c} ↦ W χ.val) ⟨χ, hχ⟩
    have hW : W χ = ⊥ := by
      by_contra hn
      obtain ⟨v, hv, hv0⟩ := (W χ).ne_bot_iff.mp hn
      have hv' : v ∈ adjointWeightVectors S' ((Iso.refl S.group).hom ≫ χ) := by
        change v ∈ (W χ : Set (Lie k A.val)) at hv
        rw [RootData.CharacterPairing.adjointWeightSpaceVectors A S' s χ] at hv
        have hχid : (Iso.refl S.group).hom ≫ χ = χ := Category.id_comp χ
        exact hχid.symm ▸ hv
      let w := mapPointKernel inclusion v
      have hS' : S'.inclusion ≫ inclusion = (Iso.refl S.group).hom ≫ S.inclusion :=
        hj.trans (Category.id_comp _).symm
      have hw : w ∈ adjointWeightVectors S χ :=
        map_weightVector inclusion (T := S') (S := S) (Iso.refl S.group) hS' hv'
      have hwD := hLie (show w ∈ lieImage B from ⟨v, rfl⟩)
      let t := identityLieStructure G
      letI := t.lieRing
      letI := t.lieAlgebra
      obtain ⟨U, hU, _, _⟩ := lieWeights G _ D t
      rw [hU] at hwD
      have hzero (i : ULift.{u} (Fin U.dimension)) : U.basis.equivFun w i = 0 := by
        by_cases hi : U.weight i = pairing S.group χ c
        · exact hwD i (hi.symm ▸ lt_of_not_ge hχ)
        · exact cocharacter_weight_coordinates S c t U hw i hi
      have hw0 := (U.basis.equivFun.injective
        ((funext hzero).trans U.basis.equivFun.map_zero.symm)).trans (canonicalZero_eq t).symm
      exact hv0 ((differential_injective inclusion
        (hw0.trans (map_zero (mapPointKernel inclusion)).symm)).trans (canonicalZero_eq s))
    change W χ ≤ _
    rw [hW]
    exact bot_le
  have hE : lieImage E.parabolic = Set.univ := by
    rw [(limitLie_weightSpans A S' hS c E s).1]
    change ((⨆ χ : {χ : Character S.group // 0 ≤ pairing S.group χ c}, W χ.val :
      Submodule k (Lie k A.val)) : Set (Lie k A.val)) = _
    rw [htop, Submodule.top_coe]
  let A' := closedSubgroupAlgebraicGroup (G := A) E.parabolic
  letI : IsIso E.parabolic.inclusion := isIso_of_closedImmersion_of_differential
    (A := A') (B := A) E.parabolic.inclusion E.parabolic.isClosedImmersion
    (limitSubgroupsSmooth A _ E).1
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups A _ E).1)
    hBs hBc (Set.range_eq_univ.mp hE)
  have he : (c ≫ j) ≫ B.inclusion = c ≫ S.inclusion := by rw [Category.assoc, hj]
  obtain ⟨f, hf⟩ := map_parabolic_of_comp A.property.1 B.inclusion he E D
  exact ⟨inv E.parabolic.inclusion ≫ f, by rw [Category.assoc, hf, IsIso.inv_hom_id_assoc]⟩

private theorem limitParabolics_le
    (G : AffineAlgebraicGroup k) [Smooth G.val.X.hom] [ConnectedSpace G.val.X.left]
    (S : ClosedSubgroup G.val) (hS : IsSplitTorus S.group)
    (c d : Cocharacter S.group)
    (C : LimitDecomposition (c ≫ S.inclusion)) (D : LimitDecomposition (d ≫ S.inclusion)) :
    IsSubgroupOf C.parabolic D.parabolic ↔ nonnegativeRoots S c ⊆ nonnegativeRoots S d := by
  constructor
  · intro h a ha
    apply (limitParabolic_root_iff G S d D a).mp
    exact Set.Subset.trans ((limitParabolic_root_iff G S c C a).mpr ha) (lieImage_mono h)
  · intro h
    apply limitContains_of_lieImage G S C.parabolic hS (limitSubgroupsSmooth G _ C).1
      (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ C).1)
      (subgroupOf_trans (torus_subgroupOf_centralizer hS c C) ⟨C.sectionMap, C.section_in_G⟩) d D
    let s := identityLieStructure G
    letI := s.lieRing
    letI := s.lieAlgebra
    rw [(limitLie_weightSpans G S hS c C s).1, (limitLie_weightSpans G S hS d D s).1]
    change (⨆ a : {a : Character S.group // 0 ≤ pairing S.group a c},
      adjointWeightSpace S a.val s) ≤ (⨆ a : {a : Character S.group // 0 ≤ pairing S.group a d},
      adjointWeightSpace S a.val s)
    apply iSup_le
    rintro ⟨a, ha⟩
    by_cases hna : 0 ≤ pairing S.group a d
    · exact le_iSup (fun x : {a : Character S.group // 0 ≤ pairing S.group a d} ↦
        adjointWeightSpace S x.val s) ⟨a, hna⟩
    have h₁ : a ≠ 1 := by
      rintro rfl
      exact hna (by rw [pairing_one _ hS])
    have hz : adjointWeightSpace S a s = ⊥ := by
      by_contra hw
      have hr := (RootData.CharacterPairing.absoluteRootWeights S s a).mpr ⟨h₁, hw⟩
      exact hna (h (a := (⟨a, hr⟩ : relativeRoots S)) ha)
    rw [hz]
    exact bot_le

theorem limitParabolicsEqual :
    Specs.Relative.RelativeChambers.LimitParabolicsEqual.{u} := by
  intro k _ G hG S hS c d C D
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  exact ⟨fun h ↦ Set.Subset.antisymm ((limitParabolics_le G S hS c d C D).mp h.1)
      ((limitParabolics_le G S hS d c D C).mp h.2),
    fun h ↦ ⟨(limitParabolics_le G S hS c d C D).mpr (le_of_eq h),
      (limitParabolics_le G S hS d c D C).mpr (le_of_eq h.symm)⟩⟩

open Specs.Relative.RelativeChambers
  (RealCocharacterSpace realCocharacterTopology regularRealCocharacters chamberRegion)

theorem chamberComponents : Specs.Relative.RelativeChambers.ChamberComponents.{u} := by
  intro k _ G S
  letI := realCocharacterTopology S
  intro f hf A
  let root (a : relativeRoots S) : Additive (Character S.group) := Additive.ofMul a.val
  let toFun : RealCocharacterSpace S →+ (Additive (Character S.group) → ℝ) :=
    ⟨⟨fun g ↦ g, rfl⟩, fun _ _ ↦ rfl⟩
  have hi : Topology.IsInducing toFun := ⟨rfl⟩
  letI : ContinuousAdd (RealCocharacterSpace S) := hi.continuousAdd
  letI : ContinuousSMul ℝ (RealCocharacterSpace S) := hi.continuousSMul continuous_id rfl
  have hEval (a : relativeRoots S) : Continuous (fun g : RealCocharacterSpace S ↦ g (root a)) :=
    (continuous_apply (root a)).comp hi.continuous
  have hSub : chamberRegion S A ⊆ regularRealCocharacters S := by
    intro g hg a
    by_cases h : a ∈ A
    · exact ne_of_gt (hg.1 a h)
    · exact ne_of_lt (hg.2 a h)
  constructor
  · intro hA
    have hfRegion : f ∈ chamberRegion S A := by
      refine ⟨fun a ha ↦ by rwa [hA] at ha, fun a ha ↦ ?_⟩
      have h : ¬ 0 < f (root a) := by rwa [hA] at ha
      exact lt_of_le_of_ne (le_of_not_gt h) (hf a)
    have hConv : Convex ℝ (chamberRegion S A) := by
      have hr : chamberRegion S A =
          (⋂ a ∈ A, {g : RealCocharacterSpace S | 0 < g (root a)}) ∩
          (⋂ a ∈ Aᶜ, {g : RealCocharacterSpace S | g (root a) < 0}) := by
        ext g
        simp [chamberRegion, root]
      rw [hr]
      exact (convex_iInter₂ fun a _ ↦
        convex_halfSpace_gt (LinearMap.applyₗ' ℝ (root a)).isLinear 0).inter
        (convex_iInter₂ fun a _ ↦
          convex_halfSpace_lt (LinearMap.applyₗ' ℝ (root a)).isLinear 0)
    apply (hConv.isPreconnected.subset_connectedComponentIn hfRegion hSub).antisymm
    intro g hg
    have hfComponent := mem_connectedComponentIn hf
    have hne (a : relativeRoots S) :
        ∀ q ∈ connectedComponentIn (regularRealCocharacters S) f, q (root a) ≠ 0 :=
      fun q hq ↦ connectedComponentIn_subset _ _ hq a
    exact ⟨fun a ha ↦ isPreconnected_connectedComponentIn.lt_of_ne
        (hEval a).continuousOn (hne a) ⟨f, hfComponent, hfRegion.1 a ha⟩ hg,
      fun a ha ↦ isPreconnected_connectedComponentIn.gt_of_ne
        (hEval a).continuousOn (hne a) ⟨f, hfComponent, hfRegion.2 a ha⟩ hg⟩
  · intro h
    have hfRegion : f ∈ chamberRegion S A := h.symm ▸ mem_connectedComponentIn hf
    refine Set.Subset.antisymm hfRegion.1 (fun a ha ↦ ?_)
    by_contra hn
    exact (not_lt_of_gt ha) (hfRegion.2 a hn)

theorem chamberCocharacters : Specs.Relative.RelativeChambers.ChamberCocharacters.{u} := by
  classical
  intro k _ G S hS A
  obtain ⟨hComm, hFree, hFinite, _, _, P, hP, hpair⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing S.group hS
  letI := hComm
  letI := hFree
  letI := hFinite
  letI := hP
  haveI : Finite ↥(relativeRoots S) := relativeRootsFinite G S hS
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hsign⟩ := preservesSignsOnFiniteSet
      (fun a : relativeRoots S ↦ Additive.ofMul a.val) f hf
    let c : Cocharacter S.group := (P.flip.toPerfPair.symm g).toMul
    have hc (a : Character S.group) : pairing S.group a c = g (Additive.ofMul a) := by
      rw [← hpair]
      exact P.apply_toPerfPair_flip g _
    refine ⟨c, fun a ↦ (hc a.val).symm ▸ hg a, Set.ext fun a ↦ ?_⟩
    change 0 ≤ pairing S.group a.val c ↔ 0 < f (Additive.ofMul a.val)
    rw [hc, le_iff_lt_or_eq]
    simp only [(Ne.symm (hg a)), or_false]
    exact hsign a
  · rintro ⟨c, hc, rfl⟩
    let f := (Int.castAddHom ℝ).toIntLinearMap.comp (P.flip (Additive.ofMul c))
    have hf (a : Character S.group) : f (Additive.ofMul a) = (pairing S.group a c : ℝ) :=
      congrArg (fun n : ℤ ↦ (n : ℝ)) (hpair a c)
    refine ⟨f, fun a ↦ ?_, Set.ext fun a ↦ ?_⟩
    · rw [hf]
      exact_mod_cast hc a
    · change 0 ≤ pairing S.group a.val c ↔ 0 < f (Additive.ofMul a.val)
      rw [hf, le_iff_lt_or_eq]
      simp only [Ne.symm (hc a), or_false]
      exact_mod_cast Iff.rfl

theorem regularLevi : Specs.Relative.RelativeChambers.RegularLevi.{u} := by
  classical
  intro k _ G hG S hS c D hc
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  obtain ⟨C, hC, hCs, hCc, _⟩ := CocharacterDynamics.torusCentralizer G S (isTorus_of_split hS)
  have hCD : IsSubgroupOf C D.centralizer :=
    subgroup_inclusion_of_represents hC D.centralizer_points (fun X x hx ↦ by
      apply (centralizes_iff _ _).mpr
      intro Y g t
      exact (centralizes_iff _ _).mp hx Y g (t ≫ c.hom.hom))
  have hL : lieImage D.centralizer ⊆ lieImage C := by
    let s := identityLieStructure G
    letI := s.lieRing
    letI := s.lieAlgebra
    have hAff := (closedSubgroupAlgebraicGroup (G := G) S).property.1
    have hLieC : lieImage C = adjointWeightVectors S 1 := by
      rw [CocharacterDynamics.centralizerLieInvariants S.inclusion C hC]
      ext v
      change IsFixedBy (conjugationAction S.inclusion).smul v.toMul.val ↔ _
      rw [isFixedBy_conjugation_iff, zeroWeightVectors_iff_centralizes S hAff]
    rw [hLieC, ← RootData.CharacterPairing.adjointWeightSpaceVectors G S s 1,
      (limitLie_weightSpans G S hS c D s).2]
    change (⨆ a : {a : Character S.group // pairing S.group a c = 0},
      adjointWeightSpace S a.val s) ≤ adjointWeightSpace S 1 s
    apply iSup_le
    rintro ⟨a, ha⟩
    change adjointWeightSpace S a s ≤ adjointWeightSpace S 1 s
    by_cases h : a = 1
    · rw [h]
    have hz : adjointWeightSpace S a s = ⊥ := by
      by_contra hn
      exact hc (⟨a, (RootData.CharacterPairing.absoluteRootWeights S s a).mpr ⟨h, hn⟩⟩) ha
    rw [hz]
    exact bot_le
  have hDC := subgroupOf_of_lieImage (A := G) hCD hCs (connected_of_geometricallyConnected hCc)
    (limitSubgroupsSmooth G _ D).2.2
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ D).2.2) hL
  intro X x
  refine (hC X x).trans ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨f, hf⟩ := hCD
    have hf' : f.hom.hom ≫ D.centralizer.inclusion.hom.hom = C.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map hf
    exact ⟨p ≫ f.hom.hom, by rw [Category.assoc, hf']⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨f, hf⟩ := hDC
    have hf' : f.hom.hom ≫ C.inclusion.hom.hom = D.centralizer.inclusion.hom.hom :=
      (Grp.forget (SchemeOver k)).congr_map hf
    exact ⟨p ≫ f.hom.hom, by rw [Category.assoc, hf']⟩

section RootRestriction

open Specs.AdjointRepresentation (GroupPoints dualMap constants scale dualRestriction)
open Specs.CharacterPairing (characterValue)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open CocharacterDynamics (unitPoint mapPoints_comp)
open private torusWeightBasis from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private gm_baseChange unitEquiv unitEquiv_unitPoint from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private relativePointRestrict relativePointRestrict_naturality relativePointRestrict_scale
  restriction_constants extension_dualMap baseInclusion
  from LinearAlgebraicGroups.Affine.AdjointRepresentation
open private characterValue_one from LinearAlgebraicGroups.RootData.CharacterPairing
open private characterUnit characterUnit_point characterValue_eq_unit
  from LinearAlgebraicGroups.RootData.RootGroups
open private extendSubgroup baseChange_map_injective from LinearAlgebraicGroups.RootData.RankOneFlag

private abbrev multiplicativeGroup (F : Type u) [Field F] :=
  specGroup (groupAlgebra F IntegerCharacters)

variable {K : Type u} [Field K] [Algebra k K]

local notation "ext" => groupBaseChange k K
local notation "res" => restrictTestAlgebra k K

private theorem characterValue_extend {S : GroupScheme k} (a : Character S)
    (e : multiplicativeGroup K ≅ (ext).obj (multiplicativeGroup k))
    (he : ∀ (R : TestAlgebra K) (t : Rˣ),
      baseChangePoint k K (multiplicativeGroup k).X R (unitPoint R t ≫ e.hom.hom.hom) =
        unitPoint ((res).obj R) t)
    (R : TestAlgebra K) (t : GroupPoints ((ext).obj S) R) :
    characterValue ((ext).map a ≫ e.inv) R t =
      characterValue a ((res).obj R) (baseChangePoint k K S.X R t) := by
  rw [characterValue_eq_unit, characterValue_eq_unit]
  apply congrArg (fun s : Rˣ ↦ (s : R))
  let s := characterUnit ((ext).map a ≫ e.inv) R t
  let r := characterUnit a ((res).obj R) (baseChangePoint k K S.X R t)
  have hs : unitPoint R s = t ≫ ((ext).map a ≫ e.inv).hom.hom :=
    characterUnit_point _ _ _
  have hr : unitPoint ((res).obj R) r =
      baseChangePoint k K S.X R t ≫ a.hom.hom := characterUnit_point _ _ _
  have h : unitPoint R s ≫ e.hom.hom.hom = t ≫ ((ext).map a).hom.hom := by
    rw [hs]
    change (t ≫ ((ext).map a).hom.hom ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = _
    have he' := (Grp.forget (SchemeOver K)).congr_map e.inv_hom_id
    change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ at he'
    simp only [Category.assoc, he', Category.comp_id]
  have hsr := (he R s).symm.trans
    ((congrArg (baseChangePoint k K (multiplicativeGroup k).X R) h).trans
      ((baseChangePointsSchemeNaturality k K a.hom.hom R t).trans hr.symm))
  change s = r
  simpa only [unitEquiv_unitPoint] using congrArg (unitEquiv ((res).obj R)) hsr

/-- Scalar extension preserves each character on an identity tangent vector. -/
private theorem weightVector_extend {G : GroupScheme k} (S : ClosedSubgroup G)
    (a : Character S.group) (v : Lie k G) (hv : v ∈ adjointWeightVectors S a)
    (vK : Lie K ((ext).obj G))
    (hbase : baseChangePoint k K G.X (CommAlgCat.of K (DualNumber K)) vK.toMul.val =
      mapPoints (extendDualNumber K) v.toMul.val)
    (e : multiplicativeGroup K ≅ (ext).obj (multiplicativeGroup k))
    (he : ∀ (R : TestAlgebra K) (t : Rˣ),
      baseChangePoint k K (multiplicativeGroup k).X R (unitPoint R t ≫ e.hom.hom.hom) =
        unitPoint ((res).obj R) t) :
    vK ∈ adjointWeightVectors (extendSubgroup K S) ((ext).map a ≫ e.inv) := by
  intro R t
  let R₀ := (res).obj R
  let dK : CommAlgCat.of K K ⟶ R := CommAlgCat.ofHom (Algebra.ofId K R)
  let d : CommAlgCat.of k k ⟶ R₀ :=
    ConcreteCategory.ofHom (C := CommAlgCat k) (Y := R₀) (@Algebra.ofId k R₀ _ _ R₀.algebra)
  let tr : GroupPoints S.group R₀ := baseChangePoint k K S.group.X R t
  let q : GroupPoints ((ext).obj G) R := t ≫ ((ext).map S.inclusion).hom.hom
  let p : GroupPoints ((ext).obj G) (CommAlgCat.of K (DualNumber R)) :=
    mapPoints (dualMap dK) vK.toMul.val
  let E := relativePointRestrict K G R
  have hp : E p = mapPoints (dualMap d) v.toMul.val := by
    let f : CommAlgCat.of k k ⟶ R₀ := baseInclusion (k := k) K ≫ (res).map dK
    have hcomp (x : k) :
        ((res).map dK).hom ((baseInclusion (k := k) K).hom x) = d.hom x := by
      change f.hom x = @algebraMap k R₀ _ _ R₀.algebra x
      simpa only [Algebra.algebraMap_self_apply] using f.hom.commutes x
    have hmap :
        dualMap (baseInclusion (k := k) K) ≫ dualMap ((res).map dK) = dualMap d := by
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro x
      exact TrivSqZeroExt.ext (hcomp x.fst) (hcomp x.snd)
    have hb : relativePointRestrict K G (CommAlgCat.of K K) vK.toMul.val =
        mapPoints (dualMap (baseInclusion (k := k) K)) v.toMul.val := by
      change mapPoints (dualRestriction (k := k) K (CommAlgCat.of K K)).hom
        (baseChangePoint k K G.X (CommAlgCat.of K (DualNumber K)) vK.toMul.val) = _
      rw [hbase, ← mapPoints_comp, extension_dualMap]
    change relativePointRestrict K G R (mapPoints (dualMap dK) vK.toMul.val) = _
    rw [relativePointRestrict_naturality, hb, ← mapPoints_comp, hmap]
  have hq : E (mapPoints (constants R) q) =
      mapPoints (constants R₀) (tr ≫ S.inclusion.hom.hom) := by
    change mapPoints (dualRestriction (k := k) K R).hom
      (baseChangePoint k K G.X (CommAlgCat.of K (DualNumber R))
        (mapPoints (constants R) q)) = _
    rw [baseChangePointsNaturality, ← mapPoints_comp, restriction_constants]
    congr 1
    exact baseChangePointsSchemeNaturality k K S.inclusion.hom.hom R t
  let g : GroupPoints ((ext).obj G) (CommAlgCat.of K (DualNumber R)) :=
    mapPoints (constants R) q
  change g * p * g⁻¹ = mapPoints (scale R (characterValue ((ext).map a ≫ e.inv) R t)) p
  apply E.injective
  rw [map_mul, map_mul, map_inv, show E g = _ from hq]
  change _ = relativePointRestrict K G R (mapPoints (scale R _) p)
  rw [relativePointRestrict_scale, ← show E p = relativePointRestrict K G R p from rfl,
    hp, characterValue_extend a e he R t]
  exact hv R₀ tr

private theorem weightVector_restrict {G : GroupScheme k} {S T : ClosedSubgroup G}
    (i : S.group ⟶ T.group) (hi : i ≫ T.inclusion = S.inclusion)
    (a : Character T.group) (v : Lie k G) (hv : v ∈ adjointWeightVectors T a) :
    v ∈ adjointWeightVectors S (i ≫ a) := by
  intro R t
  have h := hv R (t ≫ i.hom.hom)
  have hi' : i.hom.hom ≫ T.inclusion.hom.hom = S.inclusion.hom.hom :=
    (Grp.forget _).congr_map hi
  have ht : (t ≫ i.hom.hom) ≫ T.inclusion.hom.hom = t ≫ S.inclusion.hom.hom := by
    rw [Category.assoc, hi']
  have hc : characterValue a R (t ≫ i.hom.hom) = characterValue (i ≫ a) R t := by
    unfold characterValue
    dsimp only
    rw [Category.assoc]
    rfl
  simpa only [ht, hc] using h

/-- The set of characters of nonzero weight spaces is read from any
basis of homogeneous vectors. -/
private theorem roots_of_weight_basis (G : AffineAlgebraicGroup k)
    (S : ClosedSubgroup G.val) (hS : IsSplitTorus S.group) (s : IdentityLieStructure G.val)
    {I : Type u}
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis I k (Lie k G.val))
    (a : I → Character S.group) (ha : ∀ i, b i ∈ adjointWeightVectors S (a i)) :
    absoluteRoots S = Set.range a \ {1} := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  ext χ
  rw [RootData.CharacterPairing.absoluteRootWeights S s χ]
  have ht := adjointWeightsInternal G S hS s
  change (χ ≠ 1 ∧ adjointWeightSpace S χ s ≠ ⊥) ↔ (χ ∈ Set.range a ∧ χ ≠ 1)
  have hb (i : I) : b i ∈ adjointWeightSpace S (a i) s := by
    change b i ∈ (adjointWeightSpace S (a i) s : Set (Lie k G.val))
    rw [RootData.CharacterPairing.adjointWeightSpaceVectors G S s (a i)]
    exact ha i
  constructor
  · rintro ⟨hn, hχ⟩
    refine ⟨?_, hn⟩
    by_contra h
    have htop : (⨆ θ ∈ Set.range a, adjointWeightSpace S θ s) = ⊤ := by
      apply top_unique
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : adjointWeightSpace S (a i) s ≤ ⨆ θ ∈ Set.range a, adjointWeightSpace S θ s :=
        le_iSup₂ (f := fun θ (_ : θ ∈ Set.range a) ↦ adjointWeightSpace S θ s) (a i) ⟨i, rfl⟩
      exact hi (hb i)
    have hd := ht.submodule_iSupIndep.disjoint_biSup h
    rw [htop, disjoint_top] at hd
    exact hχ hd
  · rintro ⟨⟨j, rfl⟩, hn⟩
    exact ⟨hn, (adjointWeightSpace S (a j) s).ne_bot_iff.mpr ⟨b j, hb j, b.ne_zero j⟩⟩

theorem relativeRootsByRestriction :
    Specs.Relative.RelativeChambers.RelativeRootsByRestriction.{u} := by
  classical
  intro k K _ _ _ G S T i hi hS hT hsplit
  obtain ⟨e, he⟩ := gm_baseChange k K
  refine ⟨e, he, ?_⟩
  let H := baseChangedAlgebraicGroup K G
  let S' := extendSubgroup K S
  let T' := baseChangedSubgroup K T hT
  let extension := groupBaseChange k K
  let j : S'.group ⟶ T'.group := extension.map i
  have hj : j ≫ T'.inclusion = S'.inclusion := by
    change extension.map i ≫ extension.map T.inclusion = extension.map S.inclusion
    rw [← Functor.map_comp, hi]
  let E (a : Character S.group) : Character S'.group := extension.map a ≫ e.inv
  let F (a : Character T'.group) : Character S'.group := j ≫ a
  have hS' : IsSplitTorus S'.group := splitTorus_baseChange hS
  have hE : Function.Injective E := by
    intro a b hab
    have hc : extension.map a = extension.map b := (cancel_mono e.inv).mp hab
    exact Grp.hom_ext _ _ (baseChange_map_injective K ((Grp.forget _).congr_map hc))
  have hE₁ : E 1 = 1 := by
    apply RootData.CharacterPairing.characterValuesDetectCharacters hS'
    intro R t
    rw [characterValue_extend (1 : Character S.group) e he, characterValue_one, characterValue_one]
  have hF₁ : F 1 = 1 := by
    apply Grp.hom_ext
    exact MonObj.comp_one _
  let s := identityLieStructure G
  let t : IdentityLieStructure ((groupBaseChange k K).obj G.val) := identityLieStructure H
  letI := s.lieRing
  letI := s.lieAlgebra
  letI := t.lieRing
  letI := t.lieAlgebra
  obtain ⟨I, hI, b, a, ha, _⟩ := torusWeightBasis G S hS s
  letI := hI
  obtain ⟨J, hJ, d, w, hw, _⟩ := torusWeightBasis H T' hsplit t
  letI := hJ
  letI : AddCommGroup (Lie k G.val) := s.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := s.lieAlgebra.toModule
  letI : AddCommGroup (Lie K ((groupBaseChange k K).obj G.val)) := t.lieRing.toAddCommGroup
  letI : Module K (Lie K ((groupBaseChange k K).obj G.val)) := t.lieAlgebra.toModule
  obtain ⟨L, hL⟩ := (identityLieBracketBaseChange k K G).2 s t
  let bK := (b.baseChange K).map L.toLinearEquiv
  have hbK (i : I) : bK i ∈ adjointWeightVectors S' (E (a i)) := by
    have hv : bK i = L (1 ⊗ₜ[k] b i) := by
      rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
      rfl
    exact weightVector_extend S (a i) (b i) (ha i) (bK i) (by rw [hv, hL]) e he
  have hwr (i : J) : d i ∈ adjointWeightVectors S' (F (w i)) :=
    weightVector_restrict j hj (w i) (d i) (hw i)
  refine ⟨hE, ?_⟩
  change E '' absoluteRoots S = (F '' absoluteRoots T') \ {1}
  calc
    E '' absoluteRoots S = absoluteRoots S' := by
      rw [roots_of_weight_basis G S hS s b a ha,
        roots_of_weight_basis H S' hS' t bK (E ∘ a) hbK]
      ext x
      constructor
      · rintro ⟨y, ⟨⟨i, rfl⟩, hy⟩, rfl⟩
        exact ⟨⟨i, rfl⟩, fun h ↦ hy (Set.mem_singleton_iff.mpr (hE ((Set.mem_singleton_iff.mp h).trans hE₁.symm)))⟩
      · rintro ⟨⟨i, rfl⟩, hx⟩
        refine ⟨a i, ⟨⟨i, rfl⟩, ?_⟩, rfl⟩
        intro h
        exact hx (Set.mem_singleton_iff.mpr ((congrArg E (Set.mem_singleton_iff.mp h)).trans hE₁))
    _ = (F '' absoluteRoots T') \ {1} := by
      rw [roots_of_weight_basis H S' hS' t d (F ∘ w) hwr,
        roots_of_weight_basis H T' hsplit t d w hw]
      ext x
      constructor
      · rintro ⟨⟨i, rfl⟩, hx⟩
        refine ⟨⟨w i, ⟨⟨i, rfl⟩, ?_⟩, rfl⟩, hx⟩
        intro h
        exact hx (Set.mem_singleton_iff.mpr ((congrArg F (Set.mem_singleton_iff.mp h)).trans hF₁))
      · rintro ⟨⟨_, ⟨⟨i, rfl⟩, _⟩, rfl⟩, hx⟩
        exact ⟨⟨i, rfl⟩, hx⟩

end RootRestriction

section MinimalParabolics

open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.GeometricRadicals (GeometricGroup IsUnipotentRadical)
open Specs.StandardParabolicLevi (IsContractingRadical)
open CocharacterDynamics (contractingSubgroupUnipotent)
open Specs.DiagonalizableGroups (diagonalGroup IntegerCharacters)

open private splitTorusImage splitTorusUpperBound
  from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private multiplicative_group_iso
  from LinearAlgebraicGroups.Relative.LeviConjugacy
open private cocharacterCentralizerReductive
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private reductive_geometricGroup exists_regular_cocharacter
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extendSubgroup extend_subgroupOf subgroupOf_of_extend
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private geometricParabolic standardLevi splitQuotientIso limitKernelUnderIso
  from LinearAlgebraicGroups.Relative.ParabolicIntersection
open private pushSubgroup radical_transport from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private maximal_torus_in_borel from LinearAlgebraicGroups.RootData.BorelNormalizer
open private baseChanged_radical_transport from LinearAlgebraicGroups.RootData.BorelPositivity
open private contracting_is_radical from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private subgroup_of_intersection from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria

private theorem isIso_of_section {G : GroupScheme k} (P : ClosedSubgroup G)
    (f : G ⟶ P.group) (hf : f ≫ P.inclusion = 𝟙 G) : IsIso P.inclusion := by
  letI := inclusion_mono P
  have h' : P.inclusion ≫ f = 𝟙 _ :=
    (cancel_mono P.inclusion).mp (by rw [Category.assoc, hf, Category.comp_id, Category.id_comp])
  exact ⟨⟨f, h', hf⟩⟩

private theorem noProperParabolic_of_centralCocharacters
    (L : AffineAlgebraicGroup k)
    (h : ∀ (c : Cocharacter L.val) (X : SchemeOver k) (x : X ⟶ L.val.X), Centralizes c x)
    (P : ClosedSubgroup L.val) (hP : IsParabolic L P) : IsIso P.inclusion := by
  obtain ⟨c, D, hPD, _, _⟩ := RationalCocharacter.rationalParabolic L P hP
  obtain ⟨i, hi⟩ := (D.centralizer_points _ _).mp (h c L.val.X (𝟙 _))
  obtain ⟨j, hj⟩ := factor_group_through_subgroup D.centralizer (𝟙 L.val) i hi
  obtain ⟨f, hf⟩ := hPD.2
  apply isIso_of_section P (j ≫ D.sectionMap ≫ f)
  rw [Category.assoc, Category.assoc, hf, D.section_in_G, hj]

/-- A maximal split torus accounts for all cocharacters in its centralizer. -/
private theorem cocharactersOfCentralizer_are_central
    (G : AffineAlgebraicGroup k) (S C : ClosedSubgroup G.val)
    (hS : IsMaximalSplitTorus S)
    (hC : RepresentsSubgroup C (fun _ g ↦ Centralizes S.inclusion g))
    (c : Cocharacter C.group) (X : SchemeOver k) (x : X ⟶ C.group.X) : Centralizes c x := by
  let z : IntegerCharacters.{u} ≃* Multiplicative ℤ := MulEquiv.ulift
  letI : Group.FG IntegerCharacters.{u} :=
    Group.fg_of_surjective (f := z.symm.toMonoidHom) z.symm.surjective
  let M := diagonalGroup k IntegerCharacters.{u}
  have hM : IsSplitTorus M.val := ⟨1, multiplicative_group_iso⟩
  let L := closedSubgroupAlgebraicGroup C
  obtain ⟨R, p, hR, hp⟩ := splitTorusImage M L hM c
  let Rg := subgroupOfSubgroup C R
  obtain ⟨T, hT, hST, hRT⟩ := splitTorusUpperBound G S Rg hS.1 hR (fun Y a b ↦ by
    have hb : Centralizes S.inclusion ((b ≫ R.inclusion.hom.hom) ≫ C.inclusion.hom.hom) :=
      (hC Y _).mpr ⟨b ≫ R.inclusion.hom.hom, rfl⟩
    change Commute (a ≫ S.inclusion.hom.hom) (b ≫ R.inclusion.hom.hom ≫ C.inclusion.hom.hom)
    rw [← Category.assoc b]
    simpa only [Category.id_comp] using ((centralizes_iff _ _).mp hb Y (𝟙 _) a).symm)
  obtain ⟨f, hf⟩ := subgroupOf_trans hRT (hS.2 T hT hST)
  have he : (p ≫ f) ≫ S.inclusion = c ≫ C.inclusion := by
    rw [Category.assoc, hf]
    change p ≫ R.inclusion ≫ C.inclusion = c ≫ C.inclusion
    rw [← Category.assoc, hp.1]
  have hx := (hC X (x ≫ C.inclusion.hom.hom)).mpr ⟨x, rfl⟩
  letI := mono_over C.inclusion.hom.hom C.isClosedImmersion
  apply (centralizes_iff _ _).mpr
  intro Y a b
  apply (cancel_mono C.inclusion.hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  have hg := (centralizes_iff _ _).mp hx Y a (b ≫ (p ≫ f).hom.hom)
  simpa only [Category.assoc, ← show (p ≫ f).hom.hom ≫ S.inclusion.hom.hom =
      c.hom.hom ≫ C.inclusion.hom.hom from (Grp.forget _).congr_map he]
    using hg.eq

private theorem centralCocharacters_of_iso {L M : GroupScheme k} (e : L ≅ M)
    (h : ∀ (c : Cocharacter L) (X : SchemeOver k) (x : X ⟶ L.X), Centralizes c x)
    (c : Cocharacter M) (X : SchemeOver k) (x : X ⟶ M.X) : Centralizes c x := by
  apply (centralizes_iff _ _).mpr
  intro Y a b
  have hh := (centralizes_iff _ _).mp (h (c ≫ e.inv) X (x ≫ e.inv.hom.hom)) Y a b
  have hm := hh.map (IsMonHom.monoidHom e.hom.hom.hom Y)
  have he := (Grp.forget (SchemeOver k)).congr_map e.inv_hom_id
  change e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ at he
  have hc : (c ≫ e.inv).hom.hom = c.hom.hom ≫ e.inv.hom.hom := rfl
  simpa only [IsMonHom.monoidHom_apply, hc, Category.assoc, he, Category.comp_id] using hm

/-- Any parabolic inside a parabolic contains the latter's radical. -/
private theorem contracting_in_nestedParabolic
    {G : AffineAlgebraicGroup k} {P Q : ClosedSubgroup G.val}
    (hP : IsParabolic G P) (hQ : IsParabolic G Q) (hQP : IsSubgroupOf Q P)
    {c : Cocharacter G.val} (D : LimitDecomposition c) (hD : IsContractingRadical D)
    (e : P.group ≅ D.parabolic.group) (he : e.hom ≫ D.parabolic.inclusion = P.inclusion) :
    IsSubgroupOf D.contracting Q := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let A := GeometricGroup G
  let P' : ClosedSubgroup A.val := extendSubgroup K P
  let Q' : ClosedSubgroup A.val := extendSubgroup K Q
  obtain ⟨_, B, hB, hBQ⟩ := hQ.2.2
  change IsSubgroupOf B Q' at hBQ
  have hBP : IsSubgroupOf B P' := subgroupOf_trans hBQ (extend_subgroupOf (K := K) hQP)
  obtain ⟨T, _, hT⟩ := maximal_torus_in_borel A (reductive_geometricGroup G hP.1) B hB
  obtain ⟨_, _, E, _, _, _, hPE, _, hE, hEB⟩ := standardLevi A (geometricParabolic G hP)
    hB hBP hT ⟨T.inclusion, rfl⟩
  change SameSubgroup P' E.parabolic at hPE
  obtain ⟨f, hf⟩ := subgroupIso_of_same hPE
  let U := pushSubgroup e.symm (contractingSubgroup D)
  let V := pushSubgroup f.symm (contractingSubgroup E)
  have hV : IsUnipotentRadical (closedSubgroupAlgebraicGroup (G := A) P') V :=
    radical_transport (A := closedSubgroupAlgebraicGroup (G := A) E.parabolic)
      (B := closedSubgroupAlgebraicGroup (G := A) P') f.symm (contractingSubgroup E) hE.1
  obtain ⟨_, hUr⟩ := baseChanged_radical_transport
    (A := closedSubgroupAlgebraicGroup D.parabolic)
    (B := closedSubgroupAlgebraicGroup P) e.symm (contractingSubgroup D) hD.2.choose hD.2.choose_spec
  let U' : ClosedSubgroup P'.group := extendSubgroup K U
  obtain ⟨j, hj⟩ := hV.2.2 U' hUr.1 hUr.2.1
  have hUinc : U.inclusion ≫ P.inclusion = D.contracting.inclusion := by
    change (D.contractingToParabolic ≫ e.inv) ≫ P.inclusion = _
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, D.contracting_in_G]
  have hVinc : V.inclusion ≫ P'.inclusion = E.contracting.inclusion := by
    change (E.contractingToParabolic ≫ f.inv) ≫ P'.inclusion = _
    rw [Category.assoc, ← hf, f.inv_hom_id_assoc, E.contracting_in_G]
  obtain ⟨a, ha⟩ := subgroupOf_trans hEB hBQ
  apply subgroupOf_of_extend (K := K)
  refine ⟨j ≫ a, ?_⟩
  change (j ≫ a) ≫ Q'.inclusion = F.map D.contracting.inclusion
  rw [Category.assoc, ha, ← hVinc, ← Category.assoc, hj]
  change F.map U.inclusion ≫ F.map P.inclusion = F.map D.contracting.inclusion
  rw [← F.map_comp, hUinc]

private theorem regularParabolic_is_minimal
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion))
    (hc : IsRegular S c) : IsMinimalParabolic G D.parabolic := by
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  let P := D.parabolic
  have hP : IsParabolic G P := limitIsParabolic G hG _ D
  have hC := regularLevi G hG S hS.1 c D hc
  obtain ⟨T, hT, hTm, j, hj⟩ := maximalTorusOverSplitTorus G hG S hS
  have hcochar : (c ≫ j) ≫ T.inclusion = c ≫ S.inclusion := by rw [Category.assoc, hj]
  have hL : IsReductive (closedSubgroupAlgebraicGroup D.centralizer) := by
    suffices ∀ (x : Cocharacter G.val), (c ≫ j) ≫ T.inclusion = x →
        ∀ E : LimitDecomposition x, IsReductive (closedSubgroupAlgebraicGroup E.centralizer)
      from this _ hcochar D
    intro x hx E
    subst x
    exact cocharacterCentralizerReductive G hG T hT hTm (c ≫ j) E
  have hRad := contracting_is_radical D hL (limitSubgroupsSmooth G _ D).2.1
    (geometricallyConnectedLimitSubgroups G _ D).2.1 (contractingSubgroupUnipotent G _ D)
  refine ⟨hP, ?_⟩
  intro Q hQ hQP
  obtain ⟨H, a, _, E, e, hH, ha, he, hER, I, _, J, _, hI, _, _, hPb, _, U, m, hU, hm, hf⟩ :=
    Relative.ParabolicIntersection.intersectionProjection G P Q hP hQ
  let V := pushSubgroup e.symm (contractingSubgroup E)
  have hV : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) V :=
    radical_transport (A := closedSubgroupAlgebraicGroup E.parabolic)
      (B := closedSubgroupAlgebraicGroup P) e.symm (contractingSubgroup E) hER.1
  have hVU : SameSubgroup (contractingSubgroup D) V :=
    ⟨hV.2.2 _ hRad.1.1 hRad.1.2.1, hRad.1.2.2 V hV.1 hV.2.1⟩
  have hEs : (E.sectionMap ≫ e.inv) ≫ (e.hom ≫ E.limit) = 𝟙 E.centralizer.group := by
    simp only [Category.assoc, e.inv_hom_id_assoc, E.section_limit]
  have hKernel : IsSchemeKernel D.limit (contractingSubgroup D) := D.isKernel
  have hKernelE : IsSchemeKernel (e.hom ≫ E.limit) V := limitKernelUnderIso E e
  obtain ⟨l, _⟩ := splitQuotientIso D.section_limit hEs hKernel hKernelE hVU
  have hI' := noProperParabolic_of_centralCocharacters
    (closedSubgroupAlgebraicGroup E.centralizer)
    (centralCocharacters_of_iso l (cocharactersOfCentralizer_are_central G S D.centralizer hS hC)) I hI
  letI := hI'
  haveI : IsIso I.inclusion.hom.hom := (Grp.forget (SchemeOver k)).map_isIso _
  haveI : IsIso J.inclusion.hom.hom := hPb.isIso_fst_of_isIso
  haveI : IsIso J.inclusion.hom.hom.left := (Over.forget _).map_isIso _
  have hHV : IsSubgroupOf H Q := by
    have hh : IsSubgroupOf H H := ⟨𝟙 _, Category.id_comp _⟩
    exact (subgroup_of_intersection hH).mp hh Q (by simp)
  have hEc := contracting_in_nestedParabolic hP hQ hQP E hER e he
  let u := hKernelE.lift U.inclusion.hom.hom
    (SemiCartesianMonoidalCategory.toUnit U.group.X) hU.w
  have hu : u ≫ V.inclusion.hom.hom = U.inclusion.hom.hom := hKernelE.lift_fst _ _ _
  obtain ⟨f, hfU⟩ := factor_group_through_subgroup V U.inclusion u hu
  have hVinc : V.inclusion ≫ P.inclusion = E.contracting.inclusion := by
    change (E.contractingToParabolic ≫ e.inv) ≫ P.inclusion = _
    rw [Category.assoc, ← he, e.inv_hom_id_assoc, E.contracting_in_G]
  have hUQ : IsSubgroupOf (subgroupOfSubgroup P U) Q := by
    obtain ⟨v, hv⟩ := hEc
    refine ⟨f ≫ v, ?_⟩
    change (f ≫ v) ≫ Q.inclusion = U.inclusion ≫ P.inclusion
    rw [Category.assoc, hv, ← hVinc, ← Category.assoc, hfU]
  obtain ⟨g, hg⟩ := hQP
  obtain ⟨b, hb⟩ := hHV
  obtain ⟨v, hv⟩ := hUQ
  let n : H.group.X ⊗ U.group.X ⟶ Q.group.X := multiplyFactors b v
  have hn : n ≫ g.hom.hom = m ≫ J.inclusion.hom.hom := by
    letI := mono_over P.inclusion.hom.hom P.isClosedImmersion
    apply (cancel_mono P.inclusion.hom.hom).mp
    rw [hm]
    unfold n multiplyFactors
    simp only [MonObj.mul_comp, Category.assoc]
    have hb' := (Grp.forget _).congr_map (show b ≫ g ≫ P.inclusion = a ≫ P.inclusion by
      rw [hg, hb, ha])
    have hv' := (Grp.forget _).congr_map (show v ≫ g ≫ P.inclusion = U.inclusion ≫ P.inclusion by
      rw [hg, hv]; rfl)
    change b.hom.hom ≫ g.hom.hom ≫ P.inclusion.hom.hom =
      a.hom.hom ≫ P.inclusion.hom.hom at hb'
    change v.hom.hom ≫ g.hom.hom ≫ P.inclusion.hom.hom =
      U.inclusion.hom.hom ≫ P.inclusion.hom.hom at hv'
    rw [hb', hv']
  letI := hf.2.1
  haveI : Surjective (n.left ≫ g.hom.hom.left) := by
    change Surjective (n ≫ g.hom.hom).left
    rw [hn]
    change Surjective (m.left ≫ J.inclusion.hom.hom.left)
    infer_instance
  letI : Surjective g.hom.hom.left := .of_comp n.left _
  letI := factor_closed hg
  letI := hP.2.1
  letI : IsReduced P.group.X.left := isReduced_of_smooth_over_field P.group.X.hom
  letI : IsIso g.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  letI : IsIso g := isIso_of_schemeIso g
  exact ⟨inv g, by rw [← hg, IsIso.inv_hom_id_assoc]⟩

private theorem not_minimal_of_singular
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (S : ClosedSubgroup G.val)
    (hS : IsSplitTorus S.group) (c : Cocharacter S.group)
    (D : LimitDecomposition (c ≫ S.inclusion)) (hD : IsMinimalParabolic G D.parabolic) :
    IsRegular S c := by
  classical
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  intro a ha
  obtain ⟨r, hr⟩ := exists_regular_cocharacter G S hS
  obtain ⟨hComm, _, _, _, _, P, _, hpair⟩ := RootData.CharacterPairing.perfectCharacterPairing S.group hS
  letI := hComm
  letI : Finite ↥(relativeRoots S) := relativeRootsFinite G S hS
  letI := Fintype.ofFinite ↥(relativeRoots S)
  let f (b : relativeRoots S) := P (Additive.ofMul b.val)
  let y := if 0 < f a (Additive.ofMul r) then -Additive.ofMul r else Additive.ofMul r
  have hy : f a y < 0 := by
    have h : f a (Additive.ofMul r) ≠ 0 := by rw [hpair]; exact hr a
    by_cases hpos : 0 < f a (Additive.ofMul r)
    · simpa only [y, ite_eq_left hpos, map_neg] using neg_neg_of_pos hpos
    · simpa only [y, ite_eq_right hpos] using lt_of_le_of_ne (le_of_not_gt hpos) h
  let N := (∑ b : relativeRoots S, |f b y|) + 1
  have hN₀ : 0 ≤ N := by
    dsimp only [N]
    have := Finset.sum_nonneg (s := (Finset.univ : Finset (relativeRoots S)))
      (f := fun b ↦ |f b y|) (fun b _ ↦ abs_nonneg _)
    omega
  let d : Cocharacter S.group := (N • Additive.ofMul c + y).toMul
  obtain ⟨E⟩ := existsLimitDecomposition G (d ≫ S.inclusion)
  have hd (b : relativeRoots S) : pairing S.group b.val d = N * pairing S.group b.val c + f b y := by
    rw [← hpair, ← hpair]
    change f b (N • Additive.ofMul c + y) = N * f b (Additive.ofMul c) + f b y
    rw [map_add, map_smul, Int.zsmul_eq_mul]
  have hle : nonnegativeRoots S d ⊆ nonnegativeRoots S c := by
    intro b hb
    change 0 ≤ pairing S.group b.val d at hb
    change 0 ≤ pairing S.group b.val c
    by_contra! hn
    have hbound := Finset.single_le_sum (f := fun b : relativeRoots S ↦ |f b y|)
      (fun b _ ↦ abs_nonneg _) (Finset.mem_univ b)
    have hmul := mul_le_mul_of_nonneg_left (show pairing S.group b.val c ≤ -1 by omega) hN₀
    have habs := le_abs_self (f b y)
    rw [mul_neg_one] at hmul
    rw [hd] at hb
    dsimp only [N] at hmul hb
    omega
  have hED := (limitParabolics_le G S hS d c E D).mpr hle
  have hDE := hD.2 E.parabolic (limitIsParabolic G hG _ E) hED
  have hpa := (limitParabolics_le G S hS c d D E).mp hDE
    (show a ∈ nonnegativeRoots S c from by change 0 ≤ pairing S.group a.val c; rw [ha])
  change 0 ≤ pairing S.group a.val d at hpa
  rw [hd, ha, mul_zero, zero_add] at hpa
  exact (not_lt_of_ge hpa) hy

theorem minimalLimitParabolic : Specs.Relative.RelativeChambers.MinimalLimitParabolic.{u} := by
  intro k _ G hG S hS c D
  exact ⟨not_minimal_of_singular G hG S hS.1 c D, regularParabolic_is_minimal G hG S hS c D⟩

theorem chamberCorrespondence : Specs.Relative.RelativeChambers.ChamberCorrespondence.{u} := by
  intro k _ G hG S hS
  constructor
  · intro A hA
    obtain ⟨c, hreg, hc⟩ := (chamberCocharacters G S hS.1 A).mp hA
    obtain ⟨D⟩ := existsLimitDecomposition G (c ≫ S.inclusion)
    have hself : IsSubgroupOf D.parabolic D.parabolic := ⟨𝟙 _, Category.id_comp _⟩
    refine ⟨D.parabolic, (minimalLimitParabolic G hG S hS c D).mpr hreg,
      (limitParabolicThroughSplitTorus G hG S hS.1 c D).2, ⟨c, D, hreg, hc, hself, hself⟩, ?_⟩
    rintro Q ⟨d, E, _, hd, hQE⟩
    exact same_subgroup_trans ((limitParabolicsEqual G hG S hS.1 c d D E).mpr (hc.trans hd.symm))
      (same_subgroup_symm hQE)
  · intro P hP hSP
    obtain ⟨c, D, hPD⟩ := parabolicThroughSplitTorus G S hS P hP.1 hSP
    have hmin : IsMinimalParabolic G D.parabolic := by
      refine ⟨limitIsParabolic G hG _ D, ?_⟩
      intro Q hQ hQD
      exact subgroupOf_trans hPD.2 (hP.2 Q hQ (subgroupOf_trans hQD hPD.2))
    have hreg := (minimalLimitParabolic G hG S hS c D).mp hmin
    refine ⟨nonnegativeRoots S c, ⟨(chamberCocharacters G S hS.1 _).mpr ⟨c, hreg, rfl⟩,
      c, D, hreg, rfl, hPD⟩, ?_⟩
    rintro A ⟨_, d, E, _, hd, hPE⟩
    exact hd.symm.trans ((limitParabolicsEqual G hG S hS.1 d c E D).mp
      (same_subgroup_trans (same_subgroup_symm hPE) hPD))

theorem emptyRelativeRoots : Specs.Relative.RelativeChambers.EmptyRelativeRoots.{u} := by
  classical
  intro k _ G hG S hS hØ
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  letI : IsEmpty ↥(relativeRoots S) := by
    change IsEmpty ↥(Specs.Relative.RelativeChambers.relativeRoots S)
    rw [hØ]
    infer_instance
  have hEmptyChamber : IsChamber S ∅ :=
    ⟨0, fun a ↦ isEmptyElim a, Set.ext fun a ↦ isEmptyElim a⟩
  have hfull (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion)) :
      IsIso D.centralizer.inclusion := by
    apply isIso_of_closedImmersion_of_differential
      (A := closedSubgroupAlgebraicGroup D.centralizer) (B := G)
      D.centralizer.inclusion D.centralizer.isClosedImmersion
      (limitSubgroupsSmooth G _ D).2.2
      (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ D).2.2)
      hG.1 (connected_of_geometricallyConnected hG.2.1)
    apply Set.range_eq_univ.mp
    change lieImage D.centralizer = Set.univ
    let s := identityLieStructure G
    letI := s.lieRing
    letI := s.lieAlgebra
    rw [(limitLie_weightSpans G S hS.1 c D s).2]
    have htop : (⨆ a : {a : Character S.group // pairing S.group a c = 0},
        adjointWeightSpace S a.val s) = ⊤ := by
      apply top_unique
      rw [← (adjointWeightsInternal G S hS.1 s).submodule_iSup_eq_top]
      apply iSup_le
      intro a
      by_cases ha : a = 1
      · subst a
        exact le_iSup (fun a : {a : Character S.group // pairing S.group a c = 0} ↦
          adjointWeightSpace S a.val s) ⟨1, pairing_one _ hS.1 c⟩
      · have hz : adjointWeightSpace S a s = ⊥ := by
          by_contra h
          exact isEmptyElim (α := ↥(relativeRoots S))
            ⟨a, (RootData.CharacterPairing.absoluteRootWeights S s a).mpr ⟨ha, h⟩⟩
        rw [hz]
        exact bot_le
    rw [htop, Submodule.top_coe]
  refine ⟨⟨∅, hEmptyChamber,
    fun A _ ↦ Set.ext fun a ↦ isEmptyElim a⟩, ?_, ?_⟩
  · intro P hP hSP
    obtain ⟨c, D, hPD⟩ := parabolicThroughSplitTorus G S hS P hP hSP
    letI := hfull c D
    obtain ⟨f, hf⟩ := hPD.2
    apply isIso_of_section P (inv D.centralizer.inclusion ≫ D.sectionMap ≫ f)
    rw [Category.assoc, Category.assoc, hf, D.section_in_G, IsIso.inv_hom_id]
  · intro X x
    obtain ⟨c, hreg, _⟩ := (chamberCocharacters G S hS.1 ∅).mp hEmptyChamber
    obtain ⟨D⟩ := existsLimitDecomposition G (c ≫ S.inclusion)
    letI := hfull c D
    let i := (Grp.forget (SchemeOver k)).map D.centralizer.inclusion
    exact (regularLevi G hG S hS.1 c D hreg X x).mpr
      ⟨x ≫ inv i, by change (x ≫ inv i) ≫ i = x; simp⟩

end MinimalParabolics

end

end LinearAlgebraicGroups.Relative.RelativeChambers
