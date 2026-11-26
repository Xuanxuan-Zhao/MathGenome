import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.GenericCocharacterMinimalParabolic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Relative.GenericCocharacterMinimalParabolic

open LinearAlgebraicGroups.Specs
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots pairing adjointWeightSpace adjointWeightVectors)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf IsSplitSolvable)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.BorelsAndChambers (contractingSubgroup)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open CocharacterDynamics (LimitDecomposition lieImage existsLimitDecomposition
  limitSubgroupsSmooth geometricallyConnectedLimitSubgroups)

open private subgroupOf_trans
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff prodComparison_inv_fst prodComparison_inv_snd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private subgroupOf_of_sections sections_of_subgroupOf
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private weight_in_centralizer from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private connected_of_geometricallyConnected limitLie_weightSpans subgroupOf_of_lieImage
  splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private extendSubgroup baseChange_map_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private restrictSubgroup compose_restrict from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private pushSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private limitIsParabolic minimalParabolicExists splitSolvableConjugateInto
  transportSubgroupOf transportSubgroupCancel minimalParabolicTransport
  maximalSplitInParabolic limitSectionMemIff splitUnipotentSplitSolvable
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private innerIso transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.BorelProper
open private preimageSubgroup preimageSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private splitSolvable_of_splitTorusQuotient from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.BorelFixedPoint
open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_commutative unipotent_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private centralizes_precomposeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private HasSplitSeries.of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.SplitContractingRadical

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem centralizes_precomp {A B H : GroupScheme k} (a : A ⟶ B) (b : B ⟶ H)
    {X : SchemeOver k} {x : X ⟶ H.X} (hx : Centralizes b x) :
    Centralizes (a ≫ b) x := by
  apply (centralizes_iff _ _).2
  intro Y y t
  change Commute (y ≫ x) (t ≫ a.hom.hom ≫ b.hom.hom)
  simpa only [Category.assoc] using
    (centralizes_iff _ _).1 hx Y y (t ≫ a.hom.hom)

private theorem subgroup_le_centralizer {A H : GroupScheme k} {C : ClosedSubgroup H}
    {i : A ⟶ H} {S : ClosedSubgroup H}
    (hC : RepresentsSubgroup C (fun _ x ↦ Centralizes i x))
    (h : Centralizes i S.inclusion.hom.hom) : IsSubgroupOf S C :=
  subgroupOf_of_sections ((hC _ _).1 h)

private theorem centralizer_self {A H : GroupScheme k} {C : ClosedSubgroup H}
    {i : A ⟶ H} (hC : RepresentsSubgroup C (fun _ x ↦ Centralizes i x)) :
    Centralizes i C.inclusion.hom.hom :=
  (hC _ _).2 ⟨𝟙 _, Category.id_comp _⟩

/-- Over a split maximal torus, the zero Lie weights of the cocharacter
are fixed by the subgroup if every zero absolute root restricts trivially. -/
private theorem centralizer_le_of_root_restriction
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (S : ClosedSubgroup T.group) (hS : IsSplitTorus S.group)
    (c : Cocharacter T.group) (d : Cocharacter S.group) (hd : d ≫ S.inclusion = c)
    (D : LimitDecomposition (c ≫ T.inclusion))
    (hroot : ∀ χ ∈ absoluteRoots T, pairing T.group χ c = 0 → S.inclusion ≫ χ = 1) :
    Centralizes (subgroupOfSubgroup T S).inclusion D.centralizer.inclusion.hom.hom := by
  let S' := subgroupOfSubgroup T S
  letI := hG.1
  letI := connected_of_geometricallyConnected hG.2.1
  obtain ⟨C, hC, hCr⟩ := Reductive.SubtorusCentralizer.centralizerReductive G hG T S'
    (isTorus_of_split hT) (isTorus_of_split hS) ⟨S.inclusion, rfl⟩ hTm
  have hcomp : d ≫ S'.inclusion = c ≫ T.inclusion := by
    change d ≫ S.inclusion ≫ T.inclusion = _
    rw [← Category.assoc, hd]
  have hCD : IsSubgroupOf C D.centralizer := by
    apply subgroup_le_centralizer D.centralizer_points
    rw [← hcomp]
    exact centralizes_precomp d _ (centralizer_self hC)
  let A := closedSubgroupAlgebraicGroup C
  let vG := identityLieStructure G
  let vC := identityLieStructure A
  letI := vG.lieRing
  letI := vG.lieAlgebra
  letI := vC.lieRing
  letI := vC.lieAlgebra
  letI : AddCommGroup (Lie k G.val) := vG.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := vG.lieAlgebra.toModule
  letI : AddCommGroup (Lie k A.val) := vC.lieRing.toAddCommGroup
  letI : Module k (Lie k A.val) := vC.lieAlgebra.toModule
  letI := G.property.1
  letI := A.property.1
  obtain ⟨j, hj⟩ := identityDifferentialLieHom k A.val G.val C.inclusion vC vG
  have himage : lieImage C = (LinearMap.range j.toLinearMap : Set (Lie k G.val)) := by
    ext v
    change (∃ w, mapPointKernel C.inclusion w = v) ↔ ∃ w, j w = v
    exact exists_congr (fun w ↦ by rw [hj w]; rfl)
  have hLie : lieImage D.centralizer ⊆ lieImage C := by
    rw [(limitLie_weightSpans G T hT c D vG).2, himage]
    change (⨆ χ : {χ : Character T.group // pairing T.group χ c = 0},
      adjointWeightSpace T χ.val vG) ≤ LinearMap.range j.toLinearMap
    apply iSup_le
    intro χ v hv
    by_cases hv0 : v = 0
    · simpa only [hv0] using (LinearMap.range j.toLinearMap).zero_mem
    have hv' : v ∈ adjointWeightVectors T χ.val :=
      (RootData.CharacterPairing.adjointWeightSpaceVectors G T vG χ.val) ▸ hv
    change v ∈ (LinearMap.range j.toLinearMap : Set (Lie k G.val))
    rw [← himage]
    apply weight_in_centralizer hC _ hv'
    by_cases hχ : χ.val = 1
    · rw [hχ]
      apply Grp.hom_ext
      exact MonObj.comp_one _
    · exact hroot χ.val ⟨hχ, v, hv', (canonicalZero_eq vG).symm ▸ hv0⟩ χ.property
  have hDC := subgroupOf_of_lieImage (A := G) hCD hCr.1
    (connected_of_geometricallyConnected hCr.2.1) (limitSubgroupsSmooth G _ D).2.2
    (connected_of_geometricallyConnected (geometricallyConnectedLimitSubgroups G _ D).2.2) hLie
  exact (hC _ _).2 (sections_of_subgroupOf hDC (show
    D.centralizer.inclusion.hom.hom ∈ SubgroupSections D.centralizer D.centralizer.group.X from
    ⟨𝟙 _, by change 𝟙 _ ≫ D.centralizer.inclusion.hom.hom = _; exact Category.id_comp _⟩))

private theorem centralizes_change_family {A H : GroupScheme k} {i : A ⟶ H}
    {X Y : SchemeOver k} {x : X ⟶ H.X} (y : Y ⟶ X) (h : Centralizes i x) :
    Centralizes i (y ≫ x) := by
  apply (centralizes_iff _ _).2
  intro Z a b
  rw [← Category.assoc]
  exact (centralizes_iff _ _).1 h Z (a ≫ y) b

private theorem centralizes_postcomp {A H L : GroupScheme k} {i : A ⟶ H}
    {X : SchemeOver k} {x : X ⟶ H.X} (f : H ⟶ L) (h : Centralizes i x) :
    Centralizes (i ≫ f) (x ≫ f.hom.hom) := by
  apply (centralizes_iff _ _).2
  intro Y a b
  change Commute (a ≫ x ≫ f.hom.hom) (b ≫ i.hom.hom ≫ f.hom.hom)
  have hh := ((centralizes_iff _ _).1 h Y a b).map (IsMonHom.monoidHom f.hom.hom Y)
  change Commute ((a ≫ x) ≫ f.hom.hom) ((b ≫ i.hom.hom) ≫ f.hom.hom) at hh
  simpa only [Category.assoc] using hh

private theorem centralizes_of_baseChange {K : Type u} [Field K] [Algebra k K]
    {A H : GroupScheme k} (i : A ⟶ H) {X : SchemeOver k} (x : X ⟶ H.X)
    (h : Centralizes ((groupBaseChange k K).map i) ((baseChange k K).map x)) :
    Centralizes i x := by
  let F := baseChange k K
  let e := prodComparisonIso F A.X X
  let : GrpObj (F.obj H.X) := ((groupBaseChange k K).obj H).grp
  apply baseChange_map_injective K
  apply (cancel_epi e.inv).1
  change e.inv ≫ F.map (conjugateFamily i x) = e.inv ≫ F.map (fst A.X X ≫ i.hom.hom)
  have he : e.inv ≫ F.map (conjugateFamily i x) =
      conjugateFamily ((groupBaseChange k K).map i) (F.map x) := by
    unfold conjugateFamily
    simp only [F.map_mul, F.map_inv', F.map_comp, MonObj.comp_mul, GrpObj.comp_inv,
      ← Category.assoc]
    rw [prodComparison_inv_fst, prodComparison_inv_snd]
    rfl
  rw [he, F.map_comp, ← Category.assoc, prodComparison_inv_fst]
  exact h

/-- The transported zero-weight calculation determines centralization over the
ground field by faithful scalar extension. -/
private theorem centralizes_split_torus_of_root_restriction
    {K : Type u} [Field K] [Algebra k K] (S : ClosedSubgroup G.val) (hS : IsSplitTorus S.group)
    (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion))
    (G₀ : AffineAlgebraicGroup K) (hG₀ : IsReductive G₀)
    (T : ClosedSubgroup G₀.val) (hT : IsSplitTorus T.group) (hTm : IsGeometricallyMaximal T)
    (f : G₀.val ≅ (groupBaseChange k K).obj G.val)
    (s : (groupBaseChange k K).obj S.group ⟶ T.group)
    (hs : s ≫ T.inclusion ≫ f.hom = (groupBaseChange k K).map S.inclusion)
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange k K).obj (specGroup (groupAlgebra k IntegerCharacters)))
    (hroot : ∀ χ ∈ absoluteRoots T,
      pairing T.group χ (e.hom ≫ (groupBaseChange k K).map c ≫ s) = 0 →
      s ≫ χ = 1) :
    Centralizes S.inclusion D.centralizer.inclusion.hom.hom := by
  let B := groupBaseChange k K
  let S₀ := pushSubgroup f.symm (extendSubgroup K S)
  have hs₀ : s ≫ T.inclusion = S₀.inclusion := by
    change s ≫ T.inclusion = B.map S.inclusion ≫ f.inv
    rw [← hs, Category.assoc, Category.assoc, f.hom_inv_id, Category.comp_id]
  let S₁ := restrictSubgroup S₀ T s hs₀
  let d : Cocharacter (B.obj S.group) := e.hom ≫ B.map c
  let θ : Cocharacter T.group := d ≫ s
  obtain ⟨E⟩ := existsLimitDecomposition G₀ (θ ≫ T.inclusion)
  have hz₀ := centralizer_le_of_root_restriction G₀ hG₀ T hT hTm S₁
    (splitTorus_baseChange hS) θ d rfl E hroot
  change Centralizes (s ≫ T.inclusion) E.centralizer.inclusion.hom.hom at hz₀
  have hθ : θ ≫ T.inclusion ≫ f.hom = e.hom ≫ B.map (c ≫ S.inclusion) := by
    simp only [θ, d, Category.assoc, hs, B.map_comp]
    rfl
  obtain ⟨hclosed, hBase⟩ :=
    centralizerSchemeBaseChange k K (c ≫ S.inclusion) D.centralizer D.centralizer_points
  let x := (B.map D.centralizer.inclusion).hom.hom ≫ f.inv.hom.hom
  have hx : Centralizes (θ ≫ T.inclusion) x := by
    have h := centralizes_postcomp f.inv
      ((centralizes_precomposeIso e (B.map (c ≫ S.inclusion)) _).2 (centralizer_self hBase))
    have hcomp : (e.hom ≫ B.map (c ≫ S.inclusion)) ≫ f.inv = θ ≫ T.inclusion := by
      rw [← hθ]
      simp only [Category.assoc, f.hom_inv_id, Category.comp_id]
    exact hcomp ▸ h
  obtain ⟨y, hy⟩ := (E.centralizer_points _ _).1 hx
  have hSx : Centralizes (s ≫ T.inclusion) x := hy ▸ centralizes_change_family y hz₀
  have hh := centralizes_postcomp f.hom hSx
  rw [Category.assoc, hs] at hh
  have hxf : x ≫ f.hom.hom.hom = (B.map D.centralizer.inclusion).hom.hom := by
    change (B.map D.centralizer.inclusion).hom.hom ≫ f.inv.hom.hom ≫ f.hom.hom.hom = _
    rw [show f.inv.hom.hom ≫ f.hom.hom.hom = 𝟙 _ from
      (Grp.forget (SchemeOver K)).congr_map f.inv_hom_id, Category.comp_id]
  rw [hxf] at hh
  exact centralizes_of_baseChange S.inclusion D.centralizer.inclusion.hom.hom hh

/-- The inverse image of a split torus in the limit Levi is split solvable.
It contains the torus itself and the entire contracting subgroup. -/
private theorem split_solvable_over_torus (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (S : ClosedSubgroup G.val) (hS : IsSplitTorus S.group)
    {c : Cocharacter G.val} (D : LimitDecomposition c)
    (j : S.group ⟶ D.centralizer.group) (hj : j ≫ D.centralizer.inclusion = S.inclusion) :
    ∃ H : ClosedSubgroup G.val, IsSplitSolvable H.group ∧
      IsSubgroupOf S H ∧ IsSubgroupOf D.contracting H := by
  let SC := restrictSubgroup S D.centralizer j hj
  let W := preimageSubgroup D.limit SC
  let p : W.group ⟶ S.group := pullback.snd D.limit j
  let a : S.group ⟶ W.group := pullback.lift (j ≫ D.sectionMap) (𝟙 _) (by
    rw [Category.assoc, D.section_limit, Category.comp_id, Category.id_comp]
    rfl)
  have ha : a ≫ W.inclusion = j ≫ D.sectionMap := pullback.lift_fst _ _ _
  have hap : a ≫ p = 𝟙 S.group := pullback.lift_snd _ _ _
  let F := Grp.forget (SchemeOver k)
  let b : D.contracting.group ⟶ W.group := pullback.lift D.contractingToParabolic (0 : D.contracting.group ⟶ S.group) (by
    apply Grp.hom_ext
    change D.contractingToParabolic.hom.hom ≫ D.limit.hom.hom =
      (1 : D.contracting.group.X ⟶ S.group.X) ≫ j.hom.hom
    rw [D.isKernel.w, MonObj.one_comp]
    rfl)
  have hb : b ≫ W.inclusion = D.contractingToParabolic := pullback.lift_fst _ _ _
  have hbp : b ≫ p = 0 := pullback.lift_snd _ _ _
  let N := restrictSubgroup (contractingSubgroup D) W b hb
  have hker : IsSchemeKernel p N := by
    change IsPullback b.hom.hom (toUnit D.contracting.group.X) p.hom.hom η[S.group.X]
    have hw : b.hom.hom ≫ p.hom.hom = toUnit D.contracting.group.X ≫ η[S.group.X] :=
      F.congr_map hbp
    apply IsPullback.of_right _ hw (preimageSquare D.limit SC)
    have hb' : b.hom.hom ≫ W.inclusion.hom.hom = D.contractingToParabolic.hom.hom :=
      F.congr_map hb
    rw [hb', IsMonHom.one_hom]
    exact D.isKernel
  let Wg := subgroupOfSubgroup D.parabolic W
  have hW : IsSplitSolvable Wg.group := by
    apply splitSolvable_of_splitTorusQuotient (G := closedSubgroupAlgebraicGroup Wg)
      (D := closedSubgroupAlgebraicGroup S) N p hker hS a hap
    intro A e
    have hU := SplitContractingRadical.splitContractingSubgroup G hG c D
    exact splitUnipotentSplitSolvable A ⟨unipotent_iso e.symm hU.1, HasSplitSeries.of_iso e.symm hU.2⟩
  refine ⟨Wg, hW, ⟨a, ?_⟩, ⟨b, ?_⟩⟩
  · change a ≫ W.inclusion ≫ D.parabolic.inclusion = S.inclusion
    rw [← Category.assoc, ha, Category.assoc, D.section_in_G, hj]
  · change b ≫ W.inclusion ≫ D.parabolic.inclusion = D.contracting.inclusion
    rw [← Category.assoc, hb, D.contracting_in_G]

/-- A limit parabolic whose Levi centralizes the original maximal split
torus is minimal over the ground field. -/
private theorem minimal_of_centralizes_split_torus (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (S : ClosedSubgroup G.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (D : LimitDecomposition (c ≫ S.inclusion))
    (hC : Centralizes S.inclusion D.centralizer.inclusion.hom.hom) :
    IsMinimalParabolic G D.parabolic := by
  have hSS : Centralizes S.inclusion S.inclusion.hom.hom := by
    letI : IsCommMonObj S.group.X :=
      torus_commutative (closedSubgroupAlgebraicGroup S) (isTorus_of_split hS.1)
    apply (centralizes_iff _ _).2
    intro X x y
    letI : CommMonoid (X ⟶ S.group.X) := Hom.commMonoid
    exact (Commute.all x y).map (IsMonHom.monoidHom S.inclusion.hom.hom X)
  obtain ⟨j, hj⟩ := subgroup_le_centralizer D.centralizer_points
    (centralizes_precomp c S.inclusion hSS)
  obtain ⟨H, hH, hSH, hUH⟩ := split_solvable_over_torus G hG S hS.1 D j hj
  obtain ⟨Q, hQ⟩ := minimalParabolicExists G hG
  obtain ⟨g, hHQ⟩ := splitSolvableConjugateInto Q hQ.1 H hH
  let E := innerIso g
  let P := transportSubgroup Q E.symm
  have hP := minimalParabolicTransport hQ E.symm
  have hHP : IsSubgroupOf H P := by
    have h := transportSubgroupOf hHQ E.symm
    rwa [transportSubgroupCancel] at h
  obtain ⟨i, hi⟩ := subgroupOf_trans hSH hHP
  let SP := restrictSubgroup S P i hi
  have hSP : (subgroupOfSubgroup P SP) = S := compose_restrict S P i hi
  have hmax : IsMaximalSplitTorus SP :=
    maximalSplitInParabolic (hSP.symm ▸ hS)
  obtain ⟨d, L, hPL, _, _, _, hZ⟩ := MaximalSplitTori.minimalParabolicLevi G P hP SP hmax
  have hCL : IsSubgroupOf D.centralizer L.centralizer := by
    apply subgroup_le_centralizer hZ
    rw [hSP]
    exact hC
  have hCP : IsSubgroupOf D.centralizer P :=
    subgroupOf_trans hCL (subgroupOf_trans ⟨L.sectionMap, L.section_in_G⟩ hPL.2)
  have hDP : IsSubgroupOf D.parabolic P := by
    apply subgroupOf_of_sections
    have hx := (limitSectionMemIff D (subgroupOf_trans hUH hHP) (𝟙 _)).2
    have hlim : (𝟙 _ ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom) ∈
        SubgroupSections P D.parabolic.group.X := by
      obtain ⟨v, hv⟩ := hCP
      refine ⟨(D.limit ≫ v).hom.hom, ?_⟩
      change ((D.limit ≫ v) ≫ P.inclusion).hom.hom = 𝟙 _ ≫ (D.limit ≫ D.centralizer.inclusion).hom.hom
      rw [Category.assoc, hv, Category.id_comp]
    simpa only [Category.id_comp] using hx hlim
  have hD := limitIsParabolic G hG _ D
  exact ⟨hD, fun R hR hRD ↦ subgroupOf_trans hDP (hP.2 R hR (subgroupOf_trans hRD hDP))⟩

theorem genericCocharacterMinimality :
    Specs.Relative.GenericCocharacterMinimalParabolic.GenericCocharacterMinimality.{u} := by
  intro F K _ _ _ G hG S hS c D G₀ hG₀ T hT hTm
  dsimp only
  intro f s hs e _he hroot
  -- A source isomorphism already suffices for the centralizer comparison.
  exact minimal_of_centralizes_split_torus G hG S hS c D
    (centralizes_split_torus_of_root_restriction S hS.1 c D G₀ hG₀ T hT hTm f s hs e hroot)

end

end LinearAlgebraicGroups.Relative.GenericCocharacterMinimalParabolic
