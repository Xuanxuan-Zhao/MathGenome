import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitApproximation
import LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
import LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Relative.SplitContractingRadical
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Arithmetic.QuasiSplitLocalGeneration
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitApproximation

open _root_.LinearAlgebraicGroups.Specs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

open Specs.QuasiSplitApproximation
open Specs.QuasiSplitPinnedPairModel (BorelPair)
open Specs.BorelProper (IsParabolic)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsUnipotentRadical)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)
open AdelicGroups ApproximationOfLocalWords

open private smooth_extend_iff from LinearAlgebraicGroups.RootData.BorelNormalizer
open private subgroupIso_of_same extendSubgroup extend_subgroupOf subgroupOf_of_extend from LinearAlgebraicGroups.RootData.RankOneFlag
open private transportSubgroup radical_transport unipotent_of_iso
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {K : Type u} [Field K] {G : AffineAlgebraicGroup K}

private theorem borelIsParabolic (hG : IsReductive G)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) : IsParabolic G B := by
  obtain ⟨hc, hBbar⟩ := hB
  exact ⟨hG, (smooth_extend_iff (AlgebraicClosure K) B.group.X).mp hBbar.1.1,
    hc, _, hBbar, ⟨𝟙 _, Category.id_comp _⟩⟩

private theorem radicalIsoForSameParabolic {P B : ClosedSubgroup G.val}
    (e : P.group ≅ B.group) (V : ClosedSubgroup P.group) (U : ClosedSubgroup B.group)
    (hV : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) V)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    ∃ d : V.group ≅ U.group, d.hom ≫ U.inclusion = V.inclusion ≫ e.hom := by
  let W := transportSubgroup e V
  have hW : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) W :=
    radical_transport
      (G := closedSubgroupAlgebraicGroup P) (G' := closedSubgroupAlgebraicGroup B)
      e IsUnipotent
      (fun {H J} d _ _ =>
        unipotent_of_iso (G := closedSubgroupAlgebraicGroup H)
          (H := closedSubgroupAlgebraicGroup J) d) V hV
  obtain ⟨d, hd, _⟩ := _root_.LinearAlgebraicGroups.GeometricRadicals.radicalUnique
    (closedSubgroupAlgebraicGroup B) IsUnipotent hW hU
  exact ⟨d, hd⟩

/-- A ground-field Borel is a parabolic, so its chosen radical has a
polynomial coordinate algebra by the contracting-cocharacter theorem. -/
private theorem borelRadicalCoordinates (hG : IsReductive G)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B)
    (U : ClosedSubgroup B.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    ∃ (n : ℕ) (A : HopfAlgebraCategory K), Nonempty (specGroup A ≅ U.group) ∧
      Nonempty (MvPolynomial (Fin n) K ≃ₐ[K] A) := by
  obtain ⟨c, L, hsame, _, hrad⟩ :=
    Relative.RationalCocharacter.rationalParabolic G B (borelIsParabolic hG B hB)
  obtain ⟨b, _⟩ := subgroupIso_of_same hsame
  obtain ⟨d, _⟩ := radicalIsoForSameParabolic b.symm (contractingSubgroup L) U hrad.1 hU
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation (closedSubgroupAlgebraicGroup L.contracting)
  obtain ⟨n, _, coordinates, _⟩ :=
    Relative.SplitContractingRadical.contractingPolynomialCoordinates G hG c L A e
  exact ⟨n, A, ⟨e ≪≫ d⟩, ⟨coordinates⟩⟩

/-- Polynomial coordinates on the marked radicals give the adelic approximation
once their local points generate at every outside place. -/
private theorem strongApproximation_of_radicalGeneration
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G)
    (S : Finset D.Place) (hS : S.Nonempty) (hG : IsReductive G) (M : BorelPair G)
    (hgen : ∀ w : Outside D S, generatedBySubgroups (oppositeRadicals M) D i w.1 = ⊤) :
    StrongApproximation D i S := by
  classical
  let H := oppositeRadicals M
  have hcoords (j : ULift.{u} Bool) :
      ∃ (n : ℕ) (A : HopfAlgebraCategory K), Nonempty (specGroup A ≅ (H j).group) ∧
        Nonempty (MvPolynomial (Fin n) K ≃ₐ[K] A) := by
    rcases j with ⟨_ | _⟩
    · exact borelRadicalCoordinates hG M.negative M.negativeBorel
        M.negativeRadical M.negativeUnipotentRadical
    · exact borelRadicalCoordinates hG M.positive M.positiveBorel
        M.positiveRadical M.positiveUnipotentRadical
  choose n A e coordinates using hcoords
  refine (subgroupsWithPolynomialCoordinates (n := n) D i S hS H A
    (fun j => Classical.choice (e j)) (fun j => Classical.choice (coordinates j))).2 ?_
  intro w
  rw [hgen w]
  simpa only [Subgroup.coe_top] using (dense_univ : Dense (Set.univ : Set (LocalPoints D i w.1)))

open Specs.QuasiSplitLocalGeneration (IsLocalField)

/-- The completions in the global-field interface meet the local-field
hypothesis of the local rational-generation statement. -/
theorem completionIsLocalField (D : GlobalFieldData.{u, v} K) (w : D.Place) :
    IsLocalField (D.Completion w) := by
  rcases w with w | w
  · exact Or.inl ⟨inferInstanceAs (ValuativeRel (D.FiniteCompletion w)),
      inferInstanceAs (TopologicalSpace (D.FiniteCompletion w)),
      GlobalFieldData.finiteCompletion_isLocalField D w⟩
  · cases D with
    | number h =>
      rcases w.isReal_or_isComplex with hw | hw
      · obtain ⟨e, _⟩ := numberRealCompletion w hw
        exact Or.inr (Or.inl ⟨e⟩)
      · obtain ⟨e, _⟩ := numberComplexCompletion w hw
        exact Or.inr (Or.inr ⟨e⟩)
    | function F t => exact w.elim

private theorem extendSubgroup_of_subgroup {F : Type u} [Field F] [Algebra K F]
    {M : GroupScheme K} (B : ClosedSubgroup M) (U : ClosedSubgroup B.group) :
    extendSubgroup F (subgroupOfSubgroup B U) =
      subgroupOfSubgroup (extendSubgroup F B) (extendSubgroup F U) := by
  change Specs.ClosedSubgroup.mk _ ((groupBaseChange K F).map (U.inclusion ≫ B.inclusion)) _ =
    Specs.ClosedSubgroup.mk _ ((groupBaseChange K F).map U.inclusion ≫
      (groupBaseChange K F).map B.inclusion) _
  congr 1
  exact (groupBaseChange K F).map_comp _ _

section RadicalBaseChange

open Specs.CharacterDescent (Cocharacter)
open Specs.RankOneFlag (SameSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open private limits_subgroups_extend
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private multiplicativeBaseChange multiplicativeBaseChange_unit extendCocharacter
  from LinearAlgebraicGroups.Relative.RationalCocharacter
open private inclusion_mono from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private smoothConnectedNormal_inclusionIso
  from LinearAlgebraicGroups.Reductive.RadicalBaseChange

private theorem radicalOfCompatibleIso {P B : ClosedSubgroup G.val}
    (e : P.group ≅ B.group) {V : ClosedSubgroup P.group} {U : ClosedSubgroup B.group}
    (d : V.group ≅ U.group) (hd : d.hom ≫ U.inclusion = V.inclusion ≫ e.hom)
    (hV : IsUnipotentRadical (closedSubgroupAlgebraicGroup P) V) :
    IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U := by
  let W := transportSubgroup e V
  have hW : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) W :=
    radical_transport
      (G := closedSubgroupAlgebraicGroup P) (G' := closedSubgroupAlgebraicGroup B)
      e IsUnipotent
      (fun {H J} a _ _ => unipotent_of_iso (G := closedSubgroupAlgebraicGroup H)
          (H := closedSubgroupAlgebraicGroup J) a) V hV
  let a : W.group ≅ U.group := d
  have ha : a.hom ≫ U.inclusion = W.inclusion := hd
  refine ⟨(smoothConnectedNormal_inclusionIso (G := closedSubgroupAlgebraicGroup B)
    a ha).mp hW.1, (unipotent_of_iso (G := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) W)
      (H := closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup B) U) a).mp hW.2.1, ?_⟩
  intro H hH hHu
  obtain ⟨j, hj⟩ := hW.2.2 H hH hHu
  exact ⟨j ≫ a.hom, by rw [Category.assoc, ha, hj]⟩

/-- The contracting subgroup comparison identifies the extension of the
specified radical with the radical of the extended Borel. -/
private theorem radicalFieldExtension_of_limit {F : Type u} [Field F] [Algebra K F]
    (hG : IsReductive G) (B : ClosedSubgroup G.val) (U : ClosedSubgroup B.group)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    {c : Cocharacter G.val} (L : LimitDecomposition c)
    (M : LimitDecomposition (extendCocharacter F c)) (hBL : SameSubgroup B L.parabolic) :
    IsUnipotentRadical (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup F G)
      (extendSubgroup F B)) (extendSubgroup F U) := by
  have hLrad := (Relative.SplitContractingRadical.contractingSubgroupIsRadical G hG c L).1
  obtain ⟨b, _⟩ := subgroupIso_of_same ⟨hBL.2, hBL.1⟩
  obtain ⟨d, hd⟩ := radicalIsoForSameParabolic b (contractingSubgroup L) U hLrad hU
  let G' := baseChangedAlgebraicGroup F G
  let E := groupBaseChange K F
  have hG' : IsReductive G' :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := F) G hG.1 hG.2.1).mpr hG
  obtain ⟨hP, hV, _⟩ :=
    limits_subgroups_extend G L (multiplicativeBaseChange K F) (multiplicativeBaseChange_unit F) M
  obtain ⟨p, hp⟩ := subgroupIso_of_same hP
  obtain ⟨q, hq⟩ := subgroupIso_of_same hV
  have hq' : q.hom ≫ E.map L.contractingToParabolic = M.contractingToParabolic ≫ p.hom := by
    letI := inclusion_mono (extendSubgroup F L.parabolic)
    apply (cancel_mono (extendSubgroup F L.parabolic).inclusion).mp
    change (q.hom ≫ E.map L.contractingToParabolic) ≫ E.map L.parabolic.inclusion =
      (M.contractingToParabolic ≫ p.hom) ≫ (extendSubgroup F L.parabolic).inclusion
    change q.hom ≫ E.map L.contracting.inclusion = M.contracting.inclusion at hq
    rw [Category.assoc, ← E.map_comp, L.contracting_in_G, hq,
      Category.assoc, hp, M.contracting_in_G]
  let b' : M.parabolic.group ≅ (extendSubgroup F B).group := p ≪≫ E.mapIso b
  let d' : M.contracting.group ≅ (extendSubgroup F U).group := q ≪≫ E.mapIso d
  have hd' : d'.hom ≫ (extendSubgroup F U).inclusion =
      (contractingSubgroup M).inclusion ≫ b'.hom := by
    change (q.hom ≫ E.map d.hom) ≫ E.map U.inclusion =
      M.contractingToParabolic ≫ p.hom ≫ E.map b.hom
    change d.hom ≫ U.inclusion = L.contractingToParabolic ≫ b.hom at hd
    rw [Category.assoc, ← E.map_comp, hd, E.map_comp, ← Category.assoc, hq', Category.assoc]
  exact radicalOfCompatibleIso (G := G') b' d' hd'
    (Relative.SplitContractingRadical.contractingSubgroupIsRadical G' hG' _ M).1

end RadicalBaseChange

section OppositeParabolics

open CategoryTheory.Limits
open Specs.CharacterDescent (Cocharacter)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter
  oppositeLimitIntersection)
open private centralizes_opposite_iff from LinearAlgebraicGroups.RootData.RankOneFlag
open private mem_limit_parabolic mem_sections_of_subgroupOf
  from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

/-- The common Levi is the scheme intersection of the two limit parabolics. -/
private theorem oppositeLimitParabolicsIntersection {c : Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c)) :
    IsSchemeIntersection {D.parabolic, E.parabolic} D.centralizer := by
  intro Y g
  have hcent (p : Y ⟶ G.val.X) :
      p ∈ SubgroupSections E.centralizer Y ↔ p ∈ SubgroupSections D.centralizer Y :=
    (E.centralizer_points Y p).symm.trans
      ((centralizes_opposite_iff c p).trans (D.centralizer_points Y p))
  have inD {p : Y ⟶ G.val.X} (hp : p ∈ SubgroupSections D.centralizer Y) :
      p ∈ SubgroupSections D.parabolic Y :=
    mem_sections_of_subgroupOf ⟨D.sectionMap, D.section_in_G⟩ hp
  have inE {p : Y ⟶ G.val.X} (hp : p ∈ SubgroupSections E.centralizer Y) :
      p ∈ SubgroupSections E.parabolic Y :=
    mem_sections_of_subgroupOf ⟨E.sectionMap, E.section_in_G⟩ hp
  constructor
  · intro hg P hP
    rcases Set.mem_insert_iff.mp hP with rfl | hP
    · exact inD hg
    · rcases Set.mem_singleton_iff.mp hP with rfl
      exact inE ((hcent g).mpr hg)
  · intro hg
    have hgD := hg D.parabolic (by simp)
    have hgE := hg E.parabolic (by simp)
    obtain ⟨t, a, ha⟩ := (mem_limit_parabolic E).mp hgE
    let x : Y ⟶ G.val.X := t ≫ E.centralizer.inclusion.hom.hom
    let y : Y ⟶ G.val.X := a ≫ E.contracting.inclusion.hom.hom
    have hx : x ∈ SubgroupSections D.centralizer Y :=
      (hcent x).mp ⟨t, rfl⟩
    have hy : y ∈ SubgroupSections D.parabolic Y := by
      have hm := (SubgroupSections D.parabolic Y).mul_mem
        ((SubgroupSections D.parabolic Y).inv_mem (inD hx)) hgD
      change x * y = g at ha
      rwa [← ha, inv_mul_cancel_left] at hm
    obtain ⟨b, hb⟩ := hy
    have hpb := oppositeLimitIntersection G c D E
    let p := hpb.lift a b hb.symm
    have hp : p ≫ η[E.contracting.group.X] = a := hpb.lift_fst _ _ _
    have hunit : y = 1 := by
      change a ≫ E.contracting.inclusion.hom.hom = 1
      rw [← hp, Category.assoc, IsMonHom.one_hom]
      exact MonObj.comp_one p
    change x * y = g at ha
    rw [hunit, mul_one] at ha
    exact ha ▸ hx

open Specs.BorelsAndChambers (IsRegular subgroupRoots)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.GeometricBorelConjugacy (IsBorel IsQuasiSplit)
open Specs.GeometricRadicals (GeometricGroup IsMaximalTorus IsSplitTorus IsTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)
open private borel_of_same limits_subgroups_extend opposite_baseChange
  same_subgroup_trans same_subgroup_symm
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private centralizer_of_regular centralizer_of_cast regular_isBorel maximalTorus_of_geometricallyMaximal
  reductive_geometricGroup root_and_opposite_not_in_borel pairing_inv kBorel_smooth_connected
  connected_of_geometricallyConnected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_maximal geometricMaximal_of_maximal
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private limitParabolic_root_iff limitParabolic_transport multiplicativeBaseChange multiplicativeBaseChange_unit
  extendCocharacter from LinearAlgebraicGroups.Relative.RationalCocharacter
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private opposite_regular from LinearAlgebraicGroups.Flag.StandardParabolics
open private section_mem_of_same from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

/-- A cocharacter in a split maximal torus whose limit parabolic is Borel is regular. -/
private theorem regular_of_limitBorel [IsAlgClosed K] (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (d : Cocharacter T.group) (L : LimitDecomposition (d ≫ T.inclusion))
    (hB : IsBorel L.parabolic) (hTL : IsSubgroupOf T L.parabolic) : IsRegular T d := by
  intro α hα
  have hroot := (RootData.RootGroups.rootSubgroups G hG T hT hTm).2 α.val α.property
  let β : ↥(absoluteRoots T) := ⟨α.val⁻¹, ((hroot.2.1 _).mpr (Or.inr rfl)).1⟩
  have hβ : pairing T.group β.val d = 0 := by
    change pairing T.group α.val⁻¹ d = 0
    rw [pairing_inv T.group hT, hα, neg_zero]
  exact root_and_opposite_not_in_borel G hG T L.parabolic hT hTm hB hTL α β rfl
    ((limitParabolic_root_iff G T d L α).mpr (le_of_eq hα.symm))
    ((limitParabolic_root_iff G T d L β).mpr (le_of_eq hβ.symm))

/-- The rational cocharacter defining a Borel has a Borel as its opposite
limit and has the given maximal torus as its centralizer. -/
private theorem oppositeLimitBorel (hG : IsReductive G)
    (T B : ClosedSubgroup G.val) (hT : IsGeometricallyMaximal T)
    (hB : IsKBorel B) (hTB : IsSubgroupOf T B)
    (d : Cocharacter T.group) (L : LimitDecomposition (d ≫ T.inclusion))
    (M : LimitDecomposition (oppositeCocharacter (d ≫ T.inclusion)))
    (hBL : SameSubgroup B L.parabolic) :
    IsKBorel M.parabolic ∧ SameSubgroup T L.centralizer := by
  let F := AlgebraicClosure K
  let G' := GeometricGroup G
  let T' := extendSubgroup F T
  let B' := extendSubgroup F B
  have hG' : IsReductive G' := reductive_geometricGroup G hG
  have hT' : IsMaximalTorus T' := hT.choose_spec
  have hTs := split_of_maximal (A := G') hT'
  have hTm := geometricMaximal_of_maximal G' T' hT'
  have hB' : IsBorel B' := hB.choose_spec
  let e := multiplicativeBaseChange K F
  let d' : Cocharacter T'.group := extendCocharacter F d
  have hd : d' ≫ T'.inclusion = extendCocharacter F (d ≫ T.inclusion) := by
    change (e.hom ≫ (groupBaseChange K F).map d) ≫ (groupBaseChange K F).map T.inclusion =
      e.hom ≫ (groupBaseChange K F).map (d ≫ T.inclusion)
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨L'⟩ := existsLimitDecomposition G' (d' ≫ T'.inclusion)
  let L'' : LimitDecomposition (extendCocharacter F (d ≫ T.inclusion)) := hd ▸ L'
  have hL := limits_subgroups_extend G L e (multiplicativeBaseChange_unit F) L''
  have hLL : SameSubgroup L'.parabolic (extendSubgroup F L.parabolic) := by
    rw [← limitParabolic_transport hd L']
    exact hL.1
  have hZZ : SameSubgroup L'.centralizer (extendSubgroup F L.centralizer) := by
    rw [← centralizer_of_cast hd L']
    exact hL.2.2
  have hBL' : SameSubgroup B' L'.parabolic :=
    same_subgroup_trans ⟨extend_subgroupOf hBL.1, extend_subgroupOf hBL.2⟩
      (same_subgroup_symm hLL)
  have hd' := regular_of_limitBorel hG' T' hTs hTm d' L'
    (borel_of_same (H := G') hB' hBL')
    (subgroupOf_trans (extend_subgroupOf hTB) hBL'.1)
  have hCent := centralizer_of_regular G' hG' T' hTs hTm d' hd' L'
  have hTL := same_subgroup_trans (same_subgroup_symm hCent) hZZ
  refine ⟨?_, subgroupOf_of_extend hTL.1, subgroupOf_of_extend hTL.2⟩
  have hdneg : oppositeCocharacter d' ≫ T'.inclusion =
      extendCocharacter F (oppositeCocharacter (d ≫ T.inclusion)) := by
    rw [show oppositeCocharacter d' ≫ T'.inclusion =
      oppositeCocharacter (d' ≫ T'.inclusion) by simp only [oppositeCocharacter, Category.assoc]]
    rw [hd]
    exact opposite_baseChange _ e (multiplicativeBaseChange_unit F)
  obtain ⟨M'⟩ := existsLimitDecomposition G' (oppositeCocharacter d' ≫ T'.inclusion)
  let M'' : LimitDecomposition (extendCocharacter F (oppositeCocharacter (d ≫ T.inclusion))) :=
    hdneg ▸ M'
  have hM := (limits_subgroups_extend G M e (multiplicativeBaseChange_unit F) M'').1
  have hreg : IsRegular T' (oppositeCocharacter d') :=
    @opposite_regular F _ G' T' d' hd'
  have hMB := regular_isBorel G' hG' T' hTs hTm (oppositeCocharacter d') hreg M'
    (centralizer_of_regular G' hG' T' hTs hTm (oppositeCocharacter d') hreg M')
  refine ⟨(extendSubgroup F M.parabolic).isClosedImmersion, ?_⟩
  apply borel_of_same (H := G') hMB
  rw [← limitParabolic_transport hdneg M']
  exact hM

/-- A quasi-split group has an opposite rational Borel pair with both radicals
defined over the ground field. -/
private theorem existsOppositeBorelPair (hG : IsQuasiSplit G) : Nonempty (BorelPair G) := by
  obtain ⟨hGr, B, hB⟩ := hG
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected G B hB
  obtain ⟨T₀, hT₀, hTm₀⟩ :=
    MaximalToriExist.geometricallyMaximalTorusExists (closedSubgroupAlgebraicGroup B) hs hc
  let T := subgroupOfSubgroup B T₀
  have hT : IsTorus T.group := hT₀
  have hTm : IsGeometricallyMaximal T := by
    let F := AlgebraicClosure K
    let G' := GeometricGroup G
    let B' := extendSubgroup F B
    have hG' := reductive_geometricGroup G hGr
    refine ⟨(extendSubgroup F T).isClosedImmersion, ?_⟩
    change IsMaximalTorus (extendSubgroup F T)
    rw [show extendSubgroup F T = subgroupOfSubgroup B' (extendSubgroup F T₀) from
      extendSubgroup_of_subgroup B T₀]
    exact (MaximalToriConjugate.borelMaximalTorusIff G' hG'.1
      (connected_of_geometricallyConnected hG'.2.1) B' hB.choose_spec
      (extendSubgroup F T₀)).mp hTm₀.choose_spec
  obtain ⟨d, L, hBL, _, hLrad⟩ := Relative.RationalCocharacter.rationalParabolicThroughTorus G B
    (borelIsParabolic hGr B hB) T₀
    (maximalTorus_of_geometricallyMaximal (closedSubgroupAlgebraicGroup B) T₀ hT₀ hTm₀)
  obtain ⟨M⟩ := existsLimitDecomposition G (oppositeCocharacter (d ≫ T.inclusion))
  have hTB : IsSubgroupOf T B := ⟨T₀.inclusion, rfl⟩
  obtain ⟨hM, hTL⟩ := oppositeLimitBorel hGr T B hTm hB hTB d L M hBL
  have hL : IsKBorel L.parabolic := by
    let F := AlgebraicClosure K
    exact ⟨(extendSubgroup F L.parabolic).isClosedImmersion,
      borel_of_same (H := GeometricGroup G) hB.choose_spec
        ⟨extend_subgroupOf hBL.1, extend_subgroupOf hBL.2⟩⟩
  have hI : IsSchemeIntersection {L.parabolic, M.parabolic} T := fun Y g =>
    (section_mem_of_same hTL).trans (oppositeLimitParabolicsIntersection L M Y g)
  exact ⟨{
    positive := L.parabolic
    negative := M.parabolic
    torus := T
    positiveRadical := contractingSubgroup L
    negativeRadical := contractingSubgroup M
    positiveBorel := hL
    negativeBorel := hM
    isTorus := hT
    maximal := hTm
    intersection := hI
    positiveUnipotentRadical := hLrad.1
    negativeUnipotentRadical :=
      (Relative.SplitContractingRadical.contractingSubgroupIsRadical G hGr _ M).1 }⟩

end OppositeParabolics

section SimplyConnectedBaseChange

open Specs.IntegralSemisimpleModel
open Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private connected_of_geometricallyConnected maximalTorus_of_geometricallyMaximal
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_maximal from LinearAlgebraicGroups.RootData.BorelNormalizer
open private splitBorelPair semisimple_iff_corootFullRank simplyConnectedDatum
  corootDatum_span restrictCharacters_injective liftFromCorootDatum realization_corootSpan
  of_fullCorootLattice fibreTowerIso noCentralCovers_of_span centralIsogeny_postIso
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange

/-- Geometric simple connectedness ascends to field extensions. The split
simply connected model over the first algebraic closure is obtained from an
integral model, whose fibres have the same full coroot lattice. -/
theorem simplyConnectedFieldExtension {F : Type u} [Field F] [Algebra K F]
    (hG : IsSemisimple G) (hsc : GeometricallySimplyConnected G) :
    GeometricallySimplyConnected (baseChangedAlgebraicGroup F G) := by
  let Kbar := AlgebraicClosure K
  let Fbar := AlgebraicClosure F
  let X := GeometricGroup G
  have hXs : IsSemisimple X :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := Kbar) G hG.1 hG.2.1).mpr hG
  have hXr := reductive_of_semisimple X hXs
  obtain ⟨T, hT, hTm⟩ := MaximalToriExist.geometricallyMaximalTorusExists X hXs.1
    (connected_of_geometricallyConnected hXs.2.1)
  let P := splitBorelPair X hXr T
    (split_of_maximal (A := X) (maximalTorus_of_geometricallyMaximal X T hT hTm)) hTm
  let D := Classification.Pinning.attachedDatum P
  letI := D.comm
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hfin := (Submodule.finiteQuotient_iff (corootLattice D)).mpr
    ((semisimple_iff_corootFullRank P D).mp hXs)
  let B := simplyConnectedDatum D.toBased hfin
  have hB : Submodule.span ℤ (Set.range B.datum.coroot) = ⊤ :=
    corootDatum_span D.datum.rootDatum (restrictCharacters_injective D.datum.rootDatum hfin)
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization B
  obtain ⟨A, Q, e, _, _, _, _, _, _⟩ := M.fieldFibre Kbar
  obtain ⟨U, ⟨pin⟩⟩ := Classification.Pinning.pinningsExist A P
  let P' : Specs.Pinning.PinnedGroup A := ⟨P, U, pin⟩
  obtain ⟨f, _, hf, _, _, _⟩ := liftFromCorootDatum P' D hfin Q
  letI : IsIso f := hsc Q.pinned.pair.G
    (of_fullCorootLattice _ _ (realization_corootSpan Q hB)) f hf
  let eX : (IntegralSemisimpleModel.fibre Kbar).obj M.group ≅ X.val := e ≪≫ asIso f
  let alg : Kbar →ₐ[K] Fbar := IsAlgClosed.lift
  letI : Algebra Kbar Fbar := alg.toRingHom.toAlgebra
  letI : IsScalarTower K Kbar Fbar := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (alg.commutes x).symm)
  let eY : (IntegralSemisimpleModel.fibre Fbar).obj M.group ≅
      (GeometricGroup (baseChangedAlgebraicGroup F G)).val :=
    (fibreTowerIso Kbar Fbar).app M.group ≪≫ (groupBaseChange Kbar Fbar).mapIso eX ≪≫
      ((groupBaseChangeTower (k := K) (K := Kbar) Fbar).app G.val).symm ≪≫
        (groupBaseChangeTower (k := K) (K := F) Fbar).app G.val
  obtain ⟨_, Q', d, _, _, _, _, _, _⟩ := M.fieldFibre Fbar
  let z := eY.symm ≪≫ d
  intro H hH g hg
  letI : IsIso (g ≫ z.hom) :=
    noCentralCovers_of_span Q'.pinned.pair Q'.attached (realization_corootSpan Q' hB)
      H hH (g ≫ z.hom) (centralIsogeny_postIso z hg)
  exact IsIso.of_isIso_comp_right g z.hom

end SimplyConnectedBaseChange

section OppositeBorelBaseChange

open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricRadicals (GeometricGroup IsTorus IsSplitTorus IsMaximalTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition existsLimitDecomposition
  oppositeCocharacter)
open private borel_baseChange intersection_baseChange maximal_of_selfCentralizing
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
open private same_opposite from LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
open private extendCocharacter multiplicativeBaseChange multiplicativeBaseChange_unit
  limitParabolic_transport from LinearAlgebraicGroups.Relative.RationalCocharacter
open private opposite_baseChange from LinearAlgebraicGroups.RootData.RankOneFlag
open private splitTorus_baseChange maximalTorus_of_geometricallyMaximal reductive_geometricGroup
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_maximal geometricMaximal_of_maximal
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private groupBaseChangeTower from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private restrictSubgroup compose_restrict local_maximal_of_ambient
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private subgroup_of_intersection from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private section_mem_of_same from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

private theorem torusFieldExtension (F : Type u) [Field F] [Algebra K F]
    (T : GroupScheme K) (hT : IsTorus T) : IsTorus ((groupBaseChange K F).obj T) := by
  obtain ⟨E, _, _, _, hE⟩ := hT
  let L := SeparableClosure F
  let a : E →ₐ[K] L := IsSepClosed.lift
  let : Algebra E L := a.toRingHom.toAlgebra
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let e := ((groupBaseChangeTower (K := F) L).app T).symm ≪≫
    (groupBaseChangeTower (K := E) L).app T
  obtain ⟨r, ⟨d⟩⟩ := splitTorus_baseChange (K := L) hE
  exact ⟨L, inferInstance, inferInstance, inferInstance, r, ⟨e ≪≫ d⟩⟩

private theorem maximalTorusFieldExtension (F : Type u) [Field F] [Algebra K F]
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsTorus T.group)
    (hmax : IsGeometricallyMaximal T) : IsGeometricallyMaximal (extendSubgroup F T) := by
  let L := AlgebraicClosure F
  let T' := extendSubgroup F T
  let T'' := extendSubgroup L T'
  have h := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT hmax
  obtain ⟨_, hF⟩ := centralizerSchemeBaseChange K F T.inclusion T h
  obtain ⟨_, hL⟩ := centralizerSchemeBaseChange F L T'.inclusion T' hF
  exact ⟨T''.isClosedImmersion,
    maximal_of_selfCentralizing (G := GeometricGroup (baseChangedAlgebraicGroup F G)) T''
      (torusFieldExtension L T'.group (torusFieldExtension F T.group hT)) hL⟩

/-- A regular cocharacter in the common torus cuts out the specified Borels
with opposite signs. Both contracting subgroups extend with those signs. -/
private theorem oppositeRadicalsFieldExtension (F : Type u) [Field F] [Algebra K F]
    (hG : IsReductive G) (M : BorelPair G) :
    let G' := baseChangedAlgebraicGroup F G
    IsUnipotentRadical (closedSubgroupAlgebraicGroup (G := G')
      (extendSubgroup F M.positive)) (extendSubgroup F M.positiveRadical) ∧
    IsUnipotentRadical (closedSubgroupAlgebraicGroup (G := G')
      (extendSubgroup F M.negative)) (extendSubgroup F M.negativeRadical) := by
  have hTB : IsSubgroupOf M.torus M.positive :=
    (subgroup_of_intersection M.intersection).mp ⟨𝟙 _, Category.id_comp _⟩ _ (by simp)
  obtain ⟨j, hj⟩ := hTB
  let T₀ := restrictSubgroup M.torus M.positive j hj
  have hT₀ : IsMaximalTorus T₀ :=
    local_maximal_of_ambient M.positive T₀ (by
      rw [compose_restrict]
      exact maximalTorus_of_geometricallyMaximal G M.torus M.isTorus M.maximal)
  obtain ⟨d, L₀, hL₀, _, _⟩ := Relative.RationalCocharacter.rationalParabolicThroughTorus G
    M.positive (borelIsParabolic hG M.positive M.positiveBorel) T₀ hT₀
  let c : Cocharacter G.val := d ≫ M.torus.inclusion
  have hc : d ≫ (subgroupOfSubgroup M.positive T₀).inclusion = c := by
    change d ≫ (j ≫ M.positive.inclusion) = d ≫ M.torus.inclusion
    rw [hj]
  let L : LimitDecomposition c := hc ▸ L₀
  have hL : SameSubgroup M.positive L.parabolic := by
    rw [show L.parabolic = L₀.parabolic from limitParabolic_transport hc L₀]
    exact hL₀
  obtain ⟨N⟩ := existsLimitDecomposition G (oppositeCocharacter c)
  obtain ⟨hN, hcenter⟩ := oppositeLimitBorel hG M.torus M.positive M.maximal
    M.positiveBorel ⟨j, hj⟩ d L N hL
  have hinter : IsSchemeIntersection {M.positive, N.parabolic} M.torus := by
    intro Y g
    refine (section_mem_of_same hcenter).trans
      ((oppositeLimitParabolicsIntersection L N Y g).trans ?_)
    simp only [Set.forall_mem_insert, Set.forall_mem_singleton, section_mem_of_same hL]
  let A := AlgebraicClosure K
  let T := extendSubgroup A M.torus
  have hmax : IsMaximalTorus T := M.maximal.choose_spec
  have hnegative : SameSubgroup (extendSubgroup A M.negative) (extendSubgroup A N.parabolic) :=
    same_opposite (GeometricGroup G) (reductive_geometricGroup G hG) T
      (extendSubgroup A M.positive) (extendSubgroup A M.negative) (extendSubgroup A N.parabolic)
      (split_of_maximal (A := GeometricGroup G) hmax)
      (geometricMaximal_of_maximal (GeometricGroup G) T hmax)
      (borel_baseChange G hG M.positive M.positiveBorel)
      (borel_baseChange G hG M.negative M.negativeBorel)
      (borel_baseChange G hG N.parabolic hN)
      (intersection_baseChange _ _ _ M.intersection) (intersection_baseChange _ _ _ hinter)
  have hneg : SameSubgroup M.negative N.parabolic :=
    ⟨subgroupOf_of_extend hnegative.1, subgroupOf_of_extend hnegative.2⟩
  let G' := baseChangedAlgebraicGroup F G
  obtain ⟨L'⟩ := existsLimitDecomposition G' (extendCocharacter F c)
  obtain ⟨N'⟩ := existsLimitDecomposition G' (oppositeCocharacter (extendCocharacter F c))
  have hsign : oppositeCocharacter (extendCocharacter F c) =
      extendCocharacter F (oppositeCocharacter c) :=
    opposite_baseChange c (multiplicativeBaseChange K F) (multiplicativeBaseChange_unit F)
  exact ⟨radicalFieldExtension_of_limit hG M.positive M.positiveRadical
      M.positiveUnipotentRadical L L' hL,
    radicalFieldExtension_of_limit hG M.negative M.negativeRadical
      M.negativeUnipotentRadical N (hsign ▸ N') hneg⟩

/-- Extend the specified Borels, the common torus, and both radicals as
closed subgroup schemes with their original inclusions base changed. -/
private def borelPairFieldExtension (F : Type u) [Field F] [Algebra K F]
    (hG : IsReductive G) (M : BorelPair G) : BorelPair (baseChangedAlgebraicGroup F G) where
  positive := extendSubgroup F M.positive
  negative := extendSubgroup F M.negative
  torus := extendSubgroup F M.torus
  positiveRadical := extendSubgroup F M.positiveRadical
  negativeRadical := extendSubgroup F M.negativeRadical
  positiveBorel := borel_baseChange G hG M.positive M.positiveBorel
  negativeBorel := borel_baseChange G hG M.negative M.negativeBorel
  isTorus := torusFieldExtension F M.torus.group M.isTorus
  maximal := maximalTorusFieldExtension F hG M.torus M.isTorus M.maximal
  intersection := intersection_baseChange _ _ _ M.intersection
  positiveUnipotentRadical := (oppositeRadicalsFieldExtension F hG M).1
  negativeUnipotentRadical := (oppositeRadicalsFieldExtension F hG M).2

private theorem oppositeRadicals_extend (F : Type u) [Field F] [Algebra K F]
    (hG : IsReductive G) (M : BorelPair G) (b : Bool) :
    oppositeRadicals (borelPairFieldExtension F hG M) ⟨b⟩ =
      extendSubgroup F (oppositeRadicals M ⟨b⟩) := by
  cases b
  · exact (extendSubgroup_of_subgroup M.negative M.negativeRadical).symm
  · exact (extendSubgroup_of_subgroup M.positive M.positiveRadical).symm

end OppositeBorelBaseChange

open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.QuasiSplitLocalGeneration (generatedByBorelRadicals)
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

/-- The rational-point isomorphism sends the two scalar-extended radical
images to their images on the same completion as a ground-field algebra. -/
private theorem localGeneration_of_baseChangeGeneration
    (D : GlobalFieldData.{u, v} K) (i : MatrixRealization G) (w : D.Place)
    (hG : IsReductive G) (M : BorelPair G)
    (hgen : generatedByBorelRadicals (borelPairFieldExtension (D.Completion w) hG M) = ⊤) :
    generatedBySubgroups (oppositeRadicals M) D i w = ⊤ := by
  let F := D.Completion w
  let R := CommAlgCat.of F F
  let N := borelPairFieldExtension F hG M
  let J := generatedBySubgroups (oppositeRadicals M) D i w
  let e : AdjointRepresentation.GroupPoints (baseChangedAlgebraicGroup F G).val R ≃*
      LocalPoints D i w := baseChangePointGroupEquiv F G.val R
  have hmark (b : Bool) :
      (((groupPointsFunctor F).map (oppositeRadicals N ⟨b⟩).inclusion).app R).hom.range ≤
        J.comap e.toMonoidHom := by
    rw [oppositeRadicals_extend F hG M b]
    rintro _ ⟨p, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨⟨b⟩, baseChangePointGroupEquiv F (oppositeRadicals M ⟨b⟩).group R p, ?_⟩
    exact (baseChangePointsSchemeNaturality K F
      (oppositeRadicals M ⟨b⟩).inclusion.hom.hom R p).symm
  have hle : generatedByBorelRadicals N ≤ J.comap e.toMonoidHom :=
    sup_le (hmark true) (hmark false)
  change generatedByBorelRadicals N = ⊤ at hgen
  rw [hgen] at hle
  apply top_unique
  intro g _
  obtain ⟨p, rfl⟩ := e.surjective g
  exact hle (Subgroup.mem_top p)

theorem generationAtCompletions_conditional
    (hlocal : Specs.QuasiSplitLocalGeneration.Statement.{u}) :
    GenerationAtCompletions.{u, v} := by
  intro K _ D G i hss hsc M w
  let F := D.Completion w
  have hG := reductive_of_semisimple G hss
  have hssF : IsSemisimple (baseChangedAlgebraicGroup F G) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G hss.1 hss.2.1).mpr hss
  exact localGeneration_of_baseChangeGeneration D i w hG M
    (hlocal (completionIsLocalField D w) (baseChangedAlgebraicGroup F G) hssF
      (simplyConnectedFieldExtension (F := F) hss hsc) (borelPairFieldExtension F hG M))

theorem strongApproximationForQuasiSplitGroups_conditional
    (hlocal : Specs.QuasiSplitLocalGeneration.Statement.{u}) :
    StrongApproximationForQuasiSplitGroups.{u, v} := by
  intro K _ D G i hss hsc hG S hS
  obtain ⟨M⟩ := existsOppositeBorelPair hG
  exact strongApproximation_of_radicalGeneration D i S hS hG.1 M
    (fun w => generationAtCompletions_conditional hlocal D G i hss hsc M w.1)

end LinearAlgebraicGroups.Arithmetic.QuasiSplitApproximation

universe v8_closure_b021f1f184e3aa8f_u0 v8_closure_b021f1f184e3aa8f_u1
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuasiSplitApproximation».«generationAtCompletions» : _root_.«LinearAlgebraicGroups».«Specs».«QuasiSplitApproximation».«GenerationAtCompletions».{v8_closure_b021f1f184e3aa8f_u0, v8_closure_b021f1f184e3aa8f_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuasiSplitApproximation».«generationAtCompletions_conditional».{v8_closure_b021f1f184e3aa8f_u0, v8_closure_b021f1f184e3aa8f_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«QuasiSplitLocalGeneration».«quasiSplitLocalGeneration».{v8_closure_b021f1f184e3aa8f_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«QuasiSplitApproximation».«strongApproximationForQuasiSplitGroups» : _root_.«LinearAlgebraicGroups».«Specs».«QuasiSplitApproximation».«StrongApproximationForQuasiSplitGroups».{v8_closure_b021f1f184e3aa8f_u0, v8_closure_b021f1f184e3aa8f_u1} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«QuasiSplitApproximation».«strongApproximationForQuasiSplitGroups_conditional».{v8_closure_b021f1f184e3aa8f_u0, v8_closure_b021f1f184e3aa8f_u1} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«QuasiSplitLocalGeneration».«quasiSplitLocalGeneration».{v8_closure_b021f1f184e3aa8f_u0})
