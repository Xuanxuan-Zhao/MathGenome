import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomologyOverAlgClosure
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.FlagCohomologyOverAlgClosure

open _root_.LinearAlgebraicGroups.Specs
open Specs.FlagCohomologyOverAlgClosure
open Specs.FlagCohomology
open Specs.FlagLineBundle (OppositeBorelPair BorelProjection)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.BorelsAndChambers
open Specs.GeometricRadicals
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup baseChangedAlgebraicGroup IsUnipotent)
open Specs.QuotientEmbedding (Presentation)
open CocharacterDynamics (LimitDecomposition oppositeCocharacter unitPoint existsLimitDecomposition)
open Specs.AbstractPairing (Datum)

open private splitTorus_baseChange geometricallyMaximal_of_maximal_split regular_of_centralizer
  centralizer_of_cast lieImage_eq_of_same radical_of_torus_kernel smooth_baseChangedGroup
  connected_baseChangedGroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extend_subgroupOf limits_subgroups_extend same_subgroup_trans borel_of_same
  opposite_baseChange parabolic_of_cast baseChangeQuotientPresentation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private oppositeCocharacter_eq_inv
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.OpenCell
open private gm_baseChange pointHom
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 450000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem multiplicativeComparison (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Nonempty (MultiplicativeComparison k K) := by
  obtain ⟨e, he⟩ := gm_baseChange k K
  exact ⟨⟨e, he⟩⟩

private theorem oppositeSigns {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) {c : Cocharacter T.group} (hc : IsRegular T c) :
    IsRegular T (oppositeCocharacter c) ∧
      positiveRoots T (oppositeCocharacter c) = (positiveRoots T c)ᶜ := by
  have hn (α : ↥(Specs.CharacterPairing.absoluteRoots T)) :
      pairing T.group α.val (oppositeCocharacter c) = -pairing T.group α.val c := by
    rw [oppositeCocharacter_eq_inv, ← D.pairing_eq, ← D.pairing_eq]
    exact map_neg _ _
  refine ⟨fun α => by rw [hn]; exact neg_ne_zero.mpr (hc α), ?_⟩
  ext α
  change 0 < pairing T.group α.val (oppositeCocharacter c) ↔ ¬ 0 < pairing T.group α.val c
  rw [hn]
  have := hc α
  omega

private theorem sameBorelOfRoots (hG : IsReductive G) {T B C : ClosedSubgroup G.val}
    (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (hB : IsKBorel B) (hC : IsKBorel C) (htB : IsSubgroupOf T B)
    (htC : IsSubgroupOf T C) (h : subgroupRoots T B = subgroupRoots T C) :
    SameSubgroup B C := by
  have classified := (RootData.BorelsAndChambers.borelsThroughT G hG T hT hm).2
    (subgroupRoots T B)
  obtain ⟨c, _, hc, _, hroots⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G hG T hT hm).1 B hB htB
  have hs := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters G hG T hT hm _).mpr
    ⟨c, hc, hroots.symm⟩
  obtain ⟨D, _, _, _, hD⟩ := classified.mp hs
  have dB := hD B hB htB rfl
  have dC := hD C hC htC h.symm
  exact same_subgroup_trans ⟨dB.2, dB.1⟩ dC

private theorem geometricBorelOfRegular
    {T B : ClosedSubgroup G.val} (hG : IsReductive G)
    (hT : IsSplitTorus T.group) (hm : IsGeometricallyMaximal T)
    (hG' : IsReductive (GeometricGroup G))
    (hT' : IsSplitTorus (geometricSubgroup T).group)
    (hm' : IsGeometricallyMaximal (geometricSubgroup T))
    (e : MultiplicativeComparison k (AlgebraicClosure k))
    (c : Cocharacter T.group) (hc : IsRegular T c)
    (D : LimitDecomposition (c ≫ T.inclusion)) (hBD : SameSubgroup B D.parabolic) :
    let c' := e.iso.hom ≫ (groupBaseChange k (AlgebraicClosure k)).map c
    IsRegular (geometricSubgroup T) c' ∧ IsKBorel (geometricSubgroup B) ∧
      subgroupRoots (geometricSubgroup T) (geometricSubgroup B) =
        positiveRoots (geometricSubgroup T) c' := by
  intro c'
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let S := geometricSubgroup T
  let J := GeometricGroup G
  have hZ := (RootData.BorelsAndChambers.regularCocharacterBorel G hG T hT hm c hc D).1
  let d := e.iso.hom ≫ F.map (c ≫ T.inclusion)
  have hd : d = c' ≫ S.inclusion := by
    change e.iso.hom ≫ F.map (c ≫ T.inclusion) = (e.iso.hom ≫ F.map c) ≫ F.map T.inclusion
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨E₀⟩ := existsLimitDecomposition J d
  obtain ⟨hP, _, hZ'⟩ := limits_subgroups_extend G D e.iso e.units E₀
  let E := hd ▸ E₀
  have hES : SameSubgroup E.centralizer S := by
    change SameSubgroup (hd ▸ E₀ : LimitDecomposition (c' ≫ S.inclusion)).centralizer S
    rw [centralizer_of_cast hd E₀]
    exact same_subgroup_trans hZ' ⟨extend_subgroupOf hZ.1, extend_subgroupOf hZ.2⟩
  have hEB : SameSubgroup E.parabolic (geometricSubgroup B) := by
    change SameSubgroup (hd ▸ E₀ : LimitDecomposition (c' ≫ S.inclusion)).parabolic _
    rw [parabolic_of_cast hd E₀]
    exact same_subgroup_trans hP ⟨extend_subgroupOf hBD.2, extend_subgroupOf hBD.1⟩
  have hcreg := regular_of_centralizer J hG' S hT' hm' c' E hES
  obtain ⟨_, hBE, _, hroots, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel J hG' S hT' hm' c' hcreg E
  refine ⟨hcreg, ?_, ?_⟩
  · obtain ⟨_, hBorel⟩ := hBE
    exact ⟨(geometricSubgroup (geometricSubgroup B)).isClosedImmersion,
      borel_of_same (H := GeometricGroup J) hBorel
        ⟨extend_subgroupOf hEB.1, extend_subgroupOf hEB.2⟩⟩
  · unfold subgroupRoots at hroots ⊢
    rw [← lieImage_eq_of_same hEB]
    exact hroots

/-- The three actual base-changed subgroups give the marked opposite Borel pair. -/
theorem oppositeBorelBaseChange : OppositeBorelBaseChange.{u} := by
  intro k _ G P
  let K := AlgebraicClosure k
  let J := GeometricGroup G
  let T := P.torus
  let S := geometricSubgroup T
  have hJ : IsReductive J := (LinearAlgebraicGroups.Reductive.RadicalBaseChange.reductiveFieldExtension
    (K := K) G P.reductive.1 P.reductive.2.1).mpr P.reductive
  have hS : IsSplitTorus S.group := splitTorus_baseChange P.split
  have hm : IsGeometricallyMaximal S :=
    geometricallyMaximal_of_maximal_split J S P.maximal.choose_spec hS
  obtain ⟨e⟩ := multiplicativeComparison k K
  obtain ⟨c, D, hc, hD, hroots⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT G P.reductive T P.split P.maximal).1
      P.positive P.positiveBorel P.inPositive
  obtain ⟨ht, ⟨A⟩⟩ := RootData.AbstractPairing.abstractPairing G P.reductive T P.split P.maximal
  letI := ht
  let cn := oppositeCocharacter c
  obtain ⟨hcn, hsign⟩ := oppositeSigns A hc
  obtain ⟨Dn⟩ := existsLimitDecomposition G (cn ≫ T.inclusion)
  obtain ⟨_, hBn, htBn, hnRoots, _, _⟩ :=
    RootData.BorelsAndChambers.regularCocharacterBorel G P.reductive T P.split P.maximal cn hcn Dn
  have hnegative : subgroupRoots T P.negative = subgroupRoots T Dn.parabolic := by
    rw [hnRoots, hsign, ← hroots]
    exact P.opposite
  have hDn := sameBorelOfRoots P.reductive P.split P.maximal P.negativeBorel hBn
    P.inNegative htBn hnegative
  obtain ⟨hc', hp', hpRoots⟩ := geometricBorelOfRegular P.reductive P.split P.maximal
    hJ hS hm e c hc D hD
  obtain ⟨_, hn', hnRoots'⟩ := geometricBorelOfRegular P.reductive P.split P.maximal
    hJ hS hm e cn hcn Dn hDn
  refine ⟨hJ, hS, hm, hp', hn', extend_subgroupOf P.inPositive,
    extend_subgroupOf P.inNegative, ?_⟩
  have halign : oppositeCocharacter (e.iso.hom ≫ (groupBaseChange k K).map c) =
      e.iso.hom ≫ (groupBaseChange k K).map cn := opposite_baseChange c e.iso e.units
  obtain ⟨hsComm, ⟨A'⟩⟩ := RootData.AbstractPairing.abstractPairing J hJ S hS hm
  letI := hsComm
  have hsign' := (oppositeSigns A' hc').2
  unfold Specs.OpenCell.AreOpposite
  rw [hpRoots, hnRoots', ← halign, hsign']

private def geometricProjection {P : OppositeBorelPair G} (E : GeometricBorelPair P)
    (b : BorelProjection P) : BorelProjection E.pair := by
  let K := AlgebraicClosure k
  let F := groupBaseChange k K
  let U := geometricSubgroup b.radical
  have hker : IsSchemeKernel (F.map b.projection) U :=
    baseChangeKernelSquare b.projection b.radical.inclusion b.isKernel
  refine ⟨F.map b.inclusion, ?_, F.map b.projection, ?_, U, ?_, hker⟩
  · change F.map b.inclusion ≫ F.map P.negative.inclusion = F.map P.torus.inclusion
    rw [← F.map_comp, b.inclusion_comp]
  · change F.map b.inclusion ≫ F.map b.projection = 𝟙 (F.obj P.torus.group)
    rw [← F.map_comp, b.section_projection, F.map_id]
  · let B := closedSubgroupAlgebraicGroup (G := G) P.negative
    let B' := closedSubgroupAlgebraicGroup (G := GeometricGroup G) E.pair.negative
    let T' := closedSubgroupAlgebraicGroup (G := GeometricGroup G) E.pair.torus
    let U₀ := closedSubgroupAlgebraicGroup (G := B) b.radical
    have hu : IsUnipotent U₀ := b.isRadical.2.1
    have hconn : ConnectedSpace U₀.val.X.left := b.isRadical.1.2.1
    have hU : IsUnipotent
        (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup E.pair.negative) U) := by
      obtain ⟨M, f, hf⟩ := (LinearAlgebraicGroups.Unipotent.unipotenceFieldExtension
        (K := K) U₀).mpr hu
      exact ⟨M, f, hf⟩
    exact radical_of_torus_kernel (A := B') (L := T') U (F.map b.projection) hker E.split
      (smooth_baseChangedGroup b.isRadical.1.1) (connected_baseChangedGroup U₀ hconn) hU

private def geometricQuotient {B : ClosedSubgroup G.val} (Q : Presentation B) :
    GeometricQuotient Q :=
  let Q' := baseChangeQuotientPresentation (AlgebraicClosure k) Q
  ⟨Q'.quasiProjective, Q'.flat, Q'.surjective, Q'.finitePresentation, Q'.quotientIso,
    Q'.quotientProjection⟩

section TransitionFunction

open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open CocharacterDynamics (unitCoordinates)
open private unitEquiv unitPointHom_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private def unitCoordinate (F : Type u) [Field F] : Γ((multiplicativeGroup F).X.left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MonoidAlgebra F IntegerCharacters))).inv
    (MonoidAlgebra.single integerGenerator 1)

private theorem unitPoint_coordinate (R : TestAlgebra k) (s : Rˣ) :
    (unitPoint R s).left.appTop (unitCoordinate k) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv (s : R) := by
  let f := CommRingCat.ofHom (unitCoordinates R s).toRingHom
  have hw := Scheme.ΓSpecIso_inv_naturality f
  have he := congrArg
    (fun p : CommRingCat.of (MonoidAlgebra k IntegerCharacters) ⟶ Γ(Spec (CommRingCat.of R), ⊤) =>
      p (MonoidAlgebra.single integerGenerator 1)) hw.symm
  change (unitPoint R s).left.appTop (unitCoordinate k) =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv (unitCoordinates R s
      (MonoidAlgebra.single integerGenerator 1)) at he
  rw [he]
  congr 1
  rw [unitCoordinates, MonoidAlgebra.lift_single, one_smul]
  change ((s ^ (1 : ℤ) : Rˣ) : R) = (s : R)
  rw [zpow_one]

private theorem multiplicativeCoordinate_baseChange {K : Type u} [Field K] [Algebra k K]
    (e : MultiplicativeComparison k K) :
    (e.iso.hom.hom.hom.left ≫
      pullback.fst (multiplicativeGroup k).X.hom (fieldSpecMap k K)).appTop (unitCoordinate k) =
        unitCoordinate K := by
  let R := CommAlgCat.of K (MonoidAlgebra K IntegerCharacters)
  let p : Points (multiplicativeGroup K).X R := 𝟙 _
  let s := unitEquiv R p
  have hpt : unitPoint R s = p :=
    (unitPointHom_apply R s).symm.trans ((unitEquiv R).symm_apply_apply p)
  have hp : (unitPoint R s).left = 𝟙 (multiplicativeGroup K).X.left :=
    congrArg Over.Hom.left hpt
  have hpcomp : p ≫ e.iso.hom.hom.hom = e.iso.hom.hom.hom :=
    Category.id_comp _
  have he : baseChangePoint k K (multiplicativeGroup k).X R e.iso.hom.hom.hom =
      unitPoint ((restrictTestAlgebra k K).obj R) s := by
    calc
      _ = baseChangePoint k K (multiplicativeGroup k).X R (p ≫ e.iso.hom.hom.hom) :=
        (congrArg (baseChangePoint k K (multiplicativeGroup k).X R) hpcomp).symm
      _ = _ := hpt ▸ e.units R s
  have h : e.iso.hom.hom.hom.left ≫
      pullback.fst (multiplicativeGroup k).X.hom (fieldSpecMap k K) =
      (unitPoint ((restrictTestAlgebra k K).obj R) s).left :=
    congrArg Over.Hom.left he
  have hK : unitCoordinate K = (Scheme.ΓSpecIso (CommRingCat.of R)).inv (s : R) := by
    have hq := congrArg (fun f : (multiplicativeGroup K).X.left ⟶ (multiplicativeGroup K).X.left =>
      f.appTop (unitCoordinate K)) hp
    exact hq.symm.trans (unitPoint_coordinate (k := K) R s)
  rw [h]
  exact (unitPoint_coordinate ((restrictTestAlgebra k K).obj R) s).trans hK.symm

variable {P : OppositeBorelPair G}

private theorem overlap_first (P : OppositeBorelPair G) :
    (overlapComparison P).hom ≫ (baseChange k (AlgebraicClosure k)).map
      (prod.fst : G.val.X ⨯ P.negative.group.X ⟶ G.val.X) = prod.fst :=
  PreservesLimitPair.iso_inv_fst _ _ _

private theorem overlap_secondProjection (P : OppositeBorelPair G) :
    (overlapComparison P).hom ≫ (baseChange k (AlgebraicClosure k)).map
      (prod.snd : G.val.X ⨯ P.negative.group.X ⟶ P.negative.group.X) = prod.snd :=
  PreservesLimitPair.iso_inv_snd _ _ _

private theorem overlap_multiplication (P : OppositeBorelPair G) :
    (overlapComparison P).hom ≫ (baseChange k (AlgebraicClosure k)).map
      (Specs.HomogeneousQuotient.rightMultiplication P.negative) =
        Specs.HomogeneousQuotient.rightMultiplication (geometricSubgroup P.negative) := by
  let F := baseChange k (AlgebraicClosure k)
  change (overlapComparison P).hom ≫
    F.map (prod.fst * (prod.snd ≫ P.negative.inclusion.hom.hom)) = _
  simp only [F.map_mul, F.map_comp, MonObj.comp_mul, ← Category.assoc]
  rw [show (overlapComparison P).hom ≫ F.map prod.fst = _ from overlap_first P,
      show (overlapComparison P).hom ≫ F.map prod.snd = _ from overlap_secondProjection P]
  rfl

private theorem flagTransition_baseChange (E : GeometricBorelPair P) (b : BorelProjection P)
    (χ : Character P.torus.group) (e : MultiplicativeComparison k (AlgebraicClosure k)) :
    (overlapComparison P).hom.left.appTop
        ((extensionProjection (closureAlgebra k) (G.val.X ⨯ P.negative.group.X)).appTop
          (flagTransition b χ)) =
      flagTransition (geometricProjection E b) (e.character χ) := by
  let K := AlgebraicClosure k
  let R := closureAlgebra k
  let X := G.val.X ⨯ P.negative.group.X
  let M := (multiplicativeGroup k).X
  let M' := (multiplicativeGroup K).X
  let r : X ⟶ M :=
    (prod.snd : X ⟶ P.negative.group.X)⁻¹ ≫ (b.projection ≫ χ).hom.hom
  let t : (baseChange k K).obj G.val.X ⨯ (geometricSubgroup P.negative).group.X ⟶ M' :=
    (prod.snd : (baseChange k K).obj G.val.X ⨯ (geometricSubgroup P.negative).group.X ⟶ _)⁻¹ ≫
      ((geometricProjection E b).projection ≫ e.character χ).hom.hom
  letI : GrpObj ((baseChange k K).obj P.negative.group.X) :=
    inferInstanceAs (GrpObj ((groupBaseChange k K).obj P.negative.group).X)
  have hr : (overlapComparison P).hom ≫ (baseChange k K).map r = t ≫ e.iso.hom.hom.hom := by
    change (overlapComparison P).hom ≫ (baseChange k K).map
      ((prod.snd : X ⟶ P.negative.group.X)⁻¹ ≫ (b.projection ≫ χ).hom.hom) =
      ((prod.snd : (baseChange k K).obj G.val.X ⨯ (geometricSubgroup P.negative).group.X ⟶ _)⁻¹ ≫
        ((baseChange k K).map b.projection.hom.hom ≫ (baseChange k K).map χ.hom.hom ≫ e.iso.inv.hom.hom)) ≫
        e.iso.hom.hom.hom
    rw [(baseChange k K).map_comp, (baseChange k K).map_inv', ← Category.assoc, GrpObj.comp_inv,
      show (overlapComparison P).hom ≫ (baseChange k K).map prod.snd = _ from overlap_secondProjection P]
    simp only [Category.assoc]
    have he : e.iso.inv.hom.hom ≫ e.iso.hom.hom.hom = 𝟙 ((baseChange k K).obj M) :=
      (Grp.forget (SchemeOver K)).congr_map e.iso.inv_hom_id
    rw [he, Category.comp_id, show (b.projection ≫ χ).hom.hom =
      b.projection.hom.hom ≫ χ.hom.hom from rfl, Functor.map_comp]
    rfl
  have hw : ((overlapComparison P).hom.left ≫ extensionProjection R X) ≫ r.left =
      t.left ≫ (e.iso.hom.hom.hom.left ≫ extensionProjection R M) := by
    rw [Category.assoc, ← extensionProjection_natural R r, ← Category.assoc]
    change ((overlapComparison P).hom ≫ (baseChange k K).map r).left ≫ extensionProjection R M = _
    rw [hr, Over.comp_left, Category.assoc]
  change (overlapComparison P).hom.left.appTop
      ((extensionProjection R X).appTop (r.left.appTop (unitCoordinate k))) =
      t.left.appTop (unitCoordinate K)
  have hcoord : (e.iso.hom.hom.hom.left ≫ extensionProjection R M).appTop (unitCoordinate k) =
      unitCoordinate K := multiplicativeCoordinate_baseChange e
  exact (congrArg (fun f => f.appTop (unitCoordinate k)) hw).trans
    (congrArg (fun z => t.left.appTop z) hcoord)

end TransitionFunction

section CovarianceKernel

open private overPullbackRegular from MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FlagCohomology
open private overPullbackRegular_app pullbackOnOpen pullbackOnOpen_comp pullbackOnOpen_congr
  pullbackOnOpen_restrict_global from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

private theorem overlapRegular_comp {Y Z W V : Scheme.{u}}
    (q : Z ⟶ Y) (r : W ⟶ Y) (s : V ⟶ Y)
    (b : W ⟶ Z) (c : V ⟶ W) (hb : b ≫ q = r) (hc : c ≫ r = s) :
    overPullbackRegular q r b hb ≫ overPullbackRegular r s c hc =
      overPullbackRegular q s (c ≫ b) (by rw [Category.assoc, hb, hc]) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, overPullbackRegular_app]
  exact congrArg (fun f => f x) (pullbackOnOpen_comp q r s b c hb hc U)

private theorem overlapRegular_id {Y Z : Scheme.{u}} (q : Z ⟶ Y) :
    overPullbackRegular q q (𝟙 Z) (Category.id_comp q) = 𝟙 _ := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  change (Γ(Z, q ⁻¹ᵁ U) : Type u) at x
  rw [overPullbackRegular_app]
  change ((𝟙 Z : Z ⟶ Z).appLE (q ⁻¹ᵁ U) ((𝟙 Z : Z ⟶ Z) ⁻¹ᵁ (q ⁻¹ᵁ U)) le_rfl) x = x
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.id_app]
  rfl

private def overlapRegularIso {Y Z W : Scheme.{u}} {r : Z ⟶ Y} {s : W ⟶ Y}
    (j : W ≅ Z) (hj : j.hom ≫ r = s) :
    (Scheme.Modules.pushforward r).obj (structureModule Z) ≅
      (Scheme.Modules.pushforward s).obj (structureModule W) where
  hom := overPullbackRegular r s j.hom hj
  inv := overPullbackRegular s r j.inv (by rw [← hj, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [overlapRegular_comp]
    simpa only [Iso.inv_hom_id] using overlapRegular_id r
  inv_hom_id := by
    rw [overlapRegular_comp]
    simpa only [Iso.hom_inv_id] using overlapRegular_id s

/-- Pullback along an isomorphism of overlaps identifies the two kernel
sheaves as subobjects of the same sheaf of regular functions. -/
private theorem covarianceKernelIso {X Y Z W : Scheme.{u}} (q : X ⟶ Y)
    (r : Z ⟶ Y) (s : W ⟶ Y)
    (b₀ b₁ : Z ⟶ X) (d₀ d₁ : W ⟶ X)
    (hb₀ : b₀ ≫ q = r) (hb₁ : b₁ ≫ q = r) (hd₀ : d₀ ≫ q = s) (hd₁ : d₁ ≫ q = s)
    (c : Γ(Z, ⊤)) (c' : Γ(W, ⊤)) (j : W ≅ Z)
    (h₀ : j.hom ≫ b₀ = d₀) (h₁ : j.hom ≫ b₁ = d₁) (hc : j.hom.appTop c = c') :
    ∃ e : covarianceSheaf q r b₀ b₁ hb₀ hb₁ c ≅ covarianceSheaf q s d₀ d₁ hd₀ hd₁ c',
      e.hom ≫ kernel.ι (covarianceMap q s d₀ d₁ hd₀ hd₁ c') =
        kernel.ι (covarianceMap q r b₀ b₁ hb₀ hb₁ c) := by
  have hj : j.hom ≫ r = s := by rw [← hb₀, ← Category.assoc, h₀, hd₀]
  let E := overlapRegularIso j hj
  let f := covarianceMap q r b₀ b₁ hb₀ hb₁ c
  let g := covarianceMap q s d₀ d₁ hd₀ hd₁ c'
  have hw : f ≫ E.hom = g := by
    apply Scheme.Modules.hom_ext
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    have ha₀ : pullbackOnOpen q r b₀ hb₀ U ≫ pullbackOnOpen r s j.hom hj U =
        pullbackOnOpen q s d₀ hd₀ U := by
      rw [pullbackOnOpen_comp]
      exact pullbackOnOpen_congr q s h₀ _ _ U
    have ha₁ : pullbackOnOpen q r b₁ hb₁ U ≫ pullbackOnOpen r s j.hom hj U =
        pullbackOnOpen q s d₁ hd₁ U := by
      rw [pullbackOnOpen_comp]
      exact pullbackOnOpen_congr q s h₁ _ _ U
    have hcU := pullbackOnOpen_restrict_global r s j.hom hj U c
    rw [hc] at hcU
    simp only [f, g, E, overlapRegularIso, Scheme.Modules.Hom.comp_app,
      ConcreteCategory.comp_apply, overPullbackRegular_app, FlagCohomology.covarianceMap_app]
    change pullbackOnOpen r s j.hom hj U
        (pullbackOnOpen q r b₁ hb₁ U x -
          pullbackOnOpen q r b₀ hb₀ U x * Z.presheaf.map (r ⁻¹ᵁ U).leTop.op c) =
      pullbackOnOpen q s d₁ hd₁ U x -
        pullbackOnOpen q s d₀ hd₀ U x * W.presheaf.map (s ⁻¹ᵁ U).leTop.op c'
    rw [map_sub, map_mul, hcU]
    exact congrArg₂ (fun a b => a - b * W.presheaf.map (s ⁻¹ᵁ U).leTop.op c')
      (congrArg (fun m : Γ(X, q ⁻¹ᵁ U) ⟶ Γ(W, s ⁻¹ᵁ U) => m x) ha₁)
      (congrArg (fun m : Γ(X, q ⁻¹ᵁ U) ⟶ Γ(W, s ⁻¹ᵁ U) => m x) ha₀)
  refine ⟨kernel.mapIso f g (Iso.refl _) E (by simpa only [Iso.refl_hom, Category.id_comp]
    using hw), ?_⟩
  change kernel.lift g (kernel.ι f ≫ 𝟙 _) _ ≫ kernel.ι g = kernel.ι f
  rw [kernel.lift_ι, Category.comp_id]

end CovarianceKernel

section Comparison

open private firstLeft_w secondLeft_w from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Representation.FlagCohomology

/-- Scalar extension identifies every degree of cohomology with the cohomology
of the actual flag and extended character over the algebraic closure. -/
theorem flagCohomologyOverAlgClosure : Statement.{u} := by
  intro k _ G P Q b χ h
  let K := AlgebraicClosure k
  let R := closureAlgebra k
  let E := oppositeBorelBaseChange P
  obtain ⟨e⟩ := multiplicativeComparison k K
  let Q' := geometricQuotient Q
  let b' := geometricProjection E b
  let χ' := e.character χ
  let h' : FlagKernelPair (P := E.pair) Q'.presentation :=
    HomogeneousQuotient.quotientPullback Q'.presentation
  let D := (flagLineData Q b χ h).extend R
  let D' := flagLineData (P := E.pair) Q'.presentation b' χ' h'
  let j := (Over.forget _).mapIso (overlapComparison P)
  have h₀ : (overlapComparison P).hom ≫ D.first = D'.first := overlap_first P
  have h₁ : (overlapComparison P).hom ≫ D.second = D'.second := overlap_multiplication P
  have hc : j.hom.appTop D.multiplier = D'.multiplier := flagTransition_baseChange E b χ e
  have hf : j.hom ≫ D.first.left = D'.first.left := congrArg Over.Hom.left h₀
  have hs : j.hom ≫ D.second.left = D'.second.left := congrArg Over.Hom.left h₁
  obtain ⟨i, hi⟩ := covarianceKernelIso D.projection.left D.overlapProjection.left
    D'.overlapProjection.left D.first.left D.second.left D'.first.left D'.second.left
    (firstLeft_w D) (secondLeft_w D) (firstLeft_w D') (secondLeft_w D')
    D.multiplier D'.multiplier j hf hs hc
  obtain ⟨C⟩ := FlagCohomology.flagCohomologyBaseChange Q b χ h R
  exact ⟨⟨E, e, Q', b', rfl, h', h₀, h₁, hc, i, hi, C⟩⟩

end Comparison

end

end LinearAlgebraicGroups.Representation.FlagCohomologyOverAlgClosure
