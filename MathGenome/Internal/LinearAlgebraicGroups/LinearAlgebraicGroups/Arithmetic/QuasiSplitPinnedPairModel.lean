import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.QuasiSplitOppositeBorelUniqueness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel

open _root_.LinearAlgebraicGroups.Specs
open Specs.QuasiSplitPinnedPairModel
private noncomputable abbrev pairCoordinateHopf := @Specs.AdjointCocharacters.coordinateHopf
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Descent.Forms (spectrumIso)

open private extendedCoordinateIso extendedCoordinateIso_comm
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private extendedGroupIso extendedSpecIso_hom_fst
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

noncomputable section

private def scalarExtensionComparison {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G H : AffineAlgebraicGroup k)
    (i : extendedHopf K (pairCoordinateHopf G) ≅ extendedHopf K (pairCoordinateHopf H)) :
    (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val :=
  (extendedCoordinateIso (K := K) G).symm ≪≫ spectrumIso i ≪≫ extendedCoordinateIso (K := K) H

set_option backward.isDefEq.respectTransparency false in
private theorem scalarExtensionComparison_comm {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H X Y : AffineAlgebraicGroup k}
    (f : X.val ⟶ G.val) (g : Y.val ⟶ H.val)
    (i : extendedHopf K (pairCoordinateHopf G) ≅ extendedHopf K (pairCoordinateHopf H))
    (d : extendedHopf K (pairCoordinateHopf X) ≅ extendedHopf K (pairCoordinateHopf Y))
    (h : i.hom ≫ extendedHopfMap K (Specs.AdjointCocharacters.coordinateHopfMap g) =
      extendedHopfMap K (Specs.AdjointCocharacters.coordinateHopfMap f) ≫ d.hom) :
    (groupBaseChange k K).map f ≫ (scalarExtensionComparison G H i).hom =
      (scalarExtensionComparison X Y d).hom ≫ (groupBaseChange k K).map g := by
  have hinv : i.inv ≫ extendedHopfMap K (Specs.AdjointCocharacters.coordinateHopfMap f) =
      extendedHopfMap K (Specs.AdjointCocharacters.coordinateHopfMap g) ≫ d.inv := by
    apply (cancel_epi i.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact (extendedCoordinateIso_comm f g d.symm i.symm hinv).symm

set_option backward.isDefEq.respectTransparency false in
private theorem matches_scalarExtensionComparison {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : AffineAlgebraicGroup k} {M : BorelPair G} {N : BorelPair H}
    (cmp : MarkedComparison (K := K) M N)
    (i : extendedHopf K (pairCoordinateHopf G) ≅ extendedHopf K (pairCoordinateHopf H))
    (h : cmp.groupIso = scalarExtensionComparison G H i) : MatchesCoordinateComparison cmp i := by
  refine ⟨extendedGroupIso K, extendedSpecIso_hom_fst K, ?_⟩
  rw [h]
  simp only [scalarExtensionComparison, extendedCoordinateIso, Iso.trans_symm, Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
theorem markedComparisonOfHopf : MarkedComparisonOfHopf.{u} := by
  intro k K _ _ _ G H M N i d hd
  let cmp : MarkedComparison (K := K) M N :=
    ⟨scalarExtensionComparison G H i,
      fun m => scalarExtensionComparison (closedSubgroupAlgebraicGroup (M.subgroup m))
        (closedSubgroupAlgebraicGroup (N.subgroup m)) (d m),
      fun m => scalarExtensionComparison_comm
        (X := closedSubgroupAlgebraicGroup (M.subgroup m))
        (Y := closedSubgroupAlgebraicGroup (N.subgroup m))
        (M.subgroup m).inclusion (N.subgroup m).inclusion i (d m) (hd m)⟩
  exact ⟨cmp, matches_scalarExtensionComparison cmp i rfl⟩

open private fibreTowerIso realization_corootSpan of_fullCorootLattice exists_coroot_cover
  centralIsogeny_baseChange centralIsogeny_postIso isIso_of_scalarExtension torusIso_of_isIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTower smooth_baseChange_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

set_option backward.isDefEq.respectTransparency false in
theorem groundFieldModel : GroundFieldModel.{u} := by
  intro k K _ _ _ Q E hE
  letI := E.comm
  have hspan : Submodule.span ℤ (Set.range E.toBased.datum.coroot) = ⊤ := hE
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization E.toBased
  obtain ⟨A, R, e, _, _, _, _, _, _⟩ := M.fieldFibre k
  obtain ⟨B, S, f, _, _, _, _, _, _⟩ := M.fieldFibre K
  have hR := realization_corootSpan R hspan
  have hS := realization_corootSpan S hspan
  have h := (Classification.PinnedEquivalence.pinnedEquivalence.2 K).2.1
    S.pinned.pair Q S.attached E
  obtain ⟨j⟩ := h.mpr ⟨S.datumIso.val.symm _ _⟩
  refine ⟨A, R.pinned, R.attached, of_fullCorootLattice _ _ hR, hR, ⟨?_⟩⟩
  exact ((groupBaseChange k K).mapIso e).symm ≪≫
    ((fibreTowerIso k K).app M.group).symm ≪≫ f ≪≫ j

open Specs.GeometricRadicals (GeometricGroup IsSemisimple)
open Specs.SimplyConnectedLattice (corootLattice)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private transportSubgroup radical_transport solvable_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

private theorem semisimple_of_iso {k : Type u} [Field k]
    {G H : AffineAlgebraicGroup k} (e : G.val ≅ H.val) (hG : IsSemisimple G)
    (hs : Smooth H.val.X.hom) (hc : GeometricallyConnected H.val.X.hom) :
    IsSemisimple H := by
  let q := (groupBaseChange k (AlgebraicClosure k)).mapIso e
  let N := Specs.GeometricRadicals.geometricSolvableRadical G
  have hN := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hM := radical_transport (G := GeometricGroup G) (G' := GeometricGroup H) q
    (fun X => Specs.SchemeDerivedGroup.IsSolvable X.val)
    (fun d hX hY => solvable_of_iso d hX.1 hX.2.1 hY.1 hY.2.1) N hN
  obtain ⟨d, _, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique (GeometricGroup H)
    (fun X => Specs.SchemeDerivedGroup.IsSolvable X.val)
    (LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest H) hM
  obtain ⟨t⟩ := hG.2.2
  exact ⟨hs, hc, ⟨d ≪≫ t⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
theorem corootLatticeAfterSplitting : CorootLatticeAfterSplitting.{u} := by
  intro k K _ _ _ _ G hG hsc Q D ⟨e⟩
  letI := D.comm
  have hGK : IsSemisimple (baseChangedAlgebraicGroup K G) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension G hG.1 hG.2.1).mpr hG
  have hQ : IsSemisimple Q.G :=
    semisimple_of_iso (G := baseChangedAlgebraicGroup K G) e hGK Q.reductive.1 Q.reductive.2.1
  let L := AlgebraicClosure k
  let a : K →ₐ[k] L := IsAlgClosed.lift
  letI : Algebra K L := a.toRingHom.toAlgebra
  letI : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  let q : (GeometricGroup G).val ≅ (baseChangedAlgebraicGroup L Q.G).val :=
    (groupBaseChangeTower (K := K) L).app G.val ≪≫ (groupBaseChange K L).mapIso e
  obtain ⟨R, E, f, τ, hR, _, hf, ht, _, _, eY, heY⟩ :=
    exists_coroot_cover Classification.IntegralRealization.integralRealization Q D hQ
  letI := E.comm
  have hRL : IsSemisimple (baseChangedAlgebraicGroup L R.G) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension R.G hR.1 hR.2.1).mpr hR
  letI : IsIso ((groupBaseChange K L).map f ≫ q.inv) :=
    hsc (baseChangedAlgebraicGroup L R.G) hRL _
      (centralIsogeny_postIso q.symm (centralIsogeny_baseChange L R f hf))
  have hIso : IsIso ((groupBaseChange K L).map f) :=
    IsIso.of_isIso_comp_right _ q.inv
  letI := isIso_of_scalarExtension L f hIso
  letI := torusIso_of_isIso R Q f τ ht
  apply eq_top_iff.mpr
  intro y _
  have hy := (eY (Additive.ofMul (y.toMul ≫ inv τ))).property
  rwa [heY, Category.assoc, IsIso.inv_hom_id, Category.comp_id] at hy


open Specs.CharacterDescent (StandardLattice)
open Specs.DiagonalizableGroups (groupAlgebra)

private theorem torusSplitOverSep {k S : Type u} [Field k] [Field S] [Algebra k S]
    [IsSepClosure k S] (A : HopfAlgebraCategory k)
    (hA : Specs.CharacterDescent.IsTorus A) :
    ∃ r, Nonempty (groupAlgebra S (StandardLattice.{u} r) ≅ extendedHopf S A) := by
  obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := hA
  letI := IsSepClosure.sep_closed k (K := S)
  let a : E →ₐ[k] S := IsSepClosed.lift
  letI : Algebra E S := a.toRingHom.toAlgebra
  letI : IsScalarTower k E S := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  exact ⟨r, ⟨(CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange E S _)).symm ≪≫
    (CharacterDescent.extendedHopfFunctor S).mapIso e ≪≫ CharacterDescent.extendedHopfTower S A⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
theorem finiteTorusSplitting : FiniteTorusSplitting.{u} := by
  intro k S _ _ _ _ T hT
  let A := pairCoordinateHopf T
  let q : specGroup A ≅ T.val := Specs.AdjointCocharacters.coordinateHopfIso T
  have hA : Specs.CharacterDescent.IsTorus A :=
    (CharacterDescent.torusOnSchemes A).mpr (by
      obtain ⟨E, _, _, _, r, ⟨e⟩⟩ := hT
      exact ⟨E, inferInstance, inferInstance, inferInstance, r,
        ⟨(groupBaseChange k E).mapIso q ≪≫ e⟩⟩)
  obtain ⟨r, ⟨e⟩⟩ := torusSplitOverSep (S := S) A hA
  let B := groupAlgebra k (StandardLattice.{u} r)
  let f : extendedHopf S B ≅ extendedHopf S A :=
    CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k S _) ≪≫ e
  have hfinA := (CharacterDescent.multiplicativeTypeProperties A
    (CharacterDescent.torusIsMultiplicativeType A hA)).1
  have hB : Specs.CharacterDescent.IsTorus B :=
    ⟨k, inferInstance, inferInstance, inferInstance, r,
      ⟨(CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k k _)).symm⟩⟩
  have hfinB := (CharacterDescent.multiplicativeTypeProperties B
    (CharacterDescent.torusIsMultiplicativeType B hB)).1
  obtain ⟨L, j, _, _⟩ := Descent.Forms.finiteLevelIsomorphisms B A hfinB hfinA ⊥ f
  let l : groupAlgebra L (StandardLattice.{u} r) ≅ extendedHopf L A :=
    (CommHopfAlgCat.isoMk (CharacterDescent.groupAlgebraBaseChange k L _)).symm ≪≫ j
  obtain ⟨i⟩ := CharacterDescent.standardSplitTorus (k := L) r
  exact ⟨L, r, ⟨(extendedCoordinateIso (K := L) T).symm ≪≫
    (hopfSpec (CommRingCat.of L)).mapIso l.op ≪≫ i⟩⟩

open Specs.GeometricRadicals
  (IsReductive IsSplitTorus IsTorus IsMaximalTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory
open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private lattice_torus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isMonHom_of_factor from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.FiniteWordClosure

private theorem maximal_of_selfCentralizing {k : Type u} [Field k] [IsAlgClosed k]
    {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val) (ht : IsTorus T.group)
    (hc : Specs.SubtorusCentralizer.IsCentralizer T T) : IsMaximalTorus T := by
  refine ⟨ht, ?_⟩
  intro S hs hTS
  obtain ⟨j, hj⟩ := hTS
  have hj' : j.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  let hcomm : IsCommMonObj S.group.X := CentralFrobeniusDescent.torus_commutative
    (closedSubgroupAlgebraicGroup S) hs
  have h := (centralizes_iff T.inclusion S.inclusion.hom.hom).mpr (by
    intro U a b
    rw [← hj', ← Category.assoc b]
    letI := (isCommMonObj_iff_isMulCommutative S.group.X).mp hcomm U
    exact (commute_iff_eq _ _).mpr (by simp only [← MonObj.mul_comp, mul_comm']))
  obtain ⟨f, hf⟩ := (hc _ _).mp h
  letI := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  letI := isMonHom_of_factor S.inclusion T.inclusion f hf
  exact ⟨Grp.homMk f, Grp.hom_ext _ _ hf⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
theorem splitPairOverField : SplitPairOverField.{u} := by
  intro k K _ _ _ G hG T hT hm hsplit
  let G' := baseChangedAlgebraicGroup K G
  have hG' : IsReductive G' :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension G hG.1 hG.2.1).mpr hG
  have h := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T hT hm
  obtain ⟨hcl, hK⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K T.inclusion T h
  let TK := baseChangedSubgroup K T hcl
  let L := AlgebraicClosure K
  obtain ⟨hclL, hL⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange K L TK.inclusion TK hK
  let TL := baseChangedSubgroup L TK hclL
  have hsL : IsSplitTorus TL.group := splitTorus_baseChange (K := L) hsplit
  have hmK : IsGeometricallyMaximal TK :=
    ⟨hclL, maximal_of_selfCentralizing (G := GeometricGroup G') TL
      (lattice_torus_of_split hsL) hL⟩
  exact ⟨splitBorelPair G' hG' TK hsplit hmK, rfl⟩

open Specs.Pinning (AttachedDatum PinnedGroup transportCharacter)
open Specs.RootGroups (AdditiveLine)
open Specs.AutomorphismSequence (SplitSequence AdjointQuotient scalarAut forgetPinning)
open private pinnedScalarAligned from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem basedLift_of_splitSequence {k : Type u} [Field k] {A : AdditiveLine k}
    {P : PinnedGroup A} {D : AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {Q : AdjointQuotient P.pair.G} (E : SplitSequence P D l Q) : IsBasedLift D l := by
  intro a
  let S := P.pair.T.group.X
  let d : (Specs.AutomorphismSequence.constantGroup (Aut D.toBased)).obj (op S) :=
    ⟨LocallyConstant.const _ a⟩
  let e := (l a).asIso.hom.torus
  let f := scalarAut (Functor.mapAut P (forgetPinning (A := A)) (l a)) S
  have h : E.toExactSequence.outer.app (op S) f = d := by
    have hsection : E.sectionMap.app (op S) d = f := E.sectionOnConstants S a
    have h := ConcreteCategory.congr_hom
      (congrArg (fun n => n.app (op S)) E.rightInverse) d
    calc
      _ = E.toExactSequence.outer.app (op S) (E.sectionMap.app (op S) d) :=
        congrArg (fun x => E.toExactSequence.outer.app (op S) x) hsection.symm
      _ = d := h
  have hact := E.latticeAction S f (pinnedScalarAligned (l a) S) a h
  constructor
  · intro χ
    have hχ := hact.1 χ (Over.mk (𝟙 S)) (𝟙 S)
    let χ' := Additive.toMul (a.asIso.hom.val.weightEquiv (Additive.ofMul χ))
    change ((𝟙 S) ≫ e.inv.hom.hom) ≫ χ.hom.hom = (𝟙 S) ≫ χ'.hom.hom at hχ
    simp only [Category.id_comp] at hχ
    exact congrArg Additive.ofMul (Grp.hom_ext χ' (transportCharacter e χ) hχ.symm)
  · intro c
    have hc := hact.2 c (Over.mk c.hom.hom) (𝟙 _)
    let c' := Additive.toMul (a.asIso.hom.val.coweightEquiv (Additive.ofMul c))
    change ((𝟙 _) ≫ c.hom.hom) ≫ e.inv.hom.hom = (𝟙 _) ≫ c'.hom.hom at hc
    simp only [Category.id_comp] at hc
    exact congrArg Additive.ofMul (Grp.hom_ext c' (c ≫ e.inv) hc.symm)

open Specs.QuasiSplitInnerForms (mapCocycle mapH1 outerHom pinnedSection)
open Descent.NonabelianCohomology (classOf)
open private relativeTrivialization pinnedClass from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

local instance (D : Pinning.BasedRootDatum.{u}) : TopologicalSpace (Aut D) := ⊥
local instance (D : Pinning.BasedRootDatum.{u}) : DiscreteTopology (Aut D) := ⟨rfl⟩

local instance {k S : Type u} [Field k] [Field S] [Algebra k S] :
    TopologicalSpace (Gal(S/k)) := krullTopology k S

local instance {k S : Type u} [Field k] [Field S] [Algebra k S] (G : GroupScheme k) :
    TopologicalSpace (Specs.AutomorphismSequence.RelativeAut G
      (Specs.RelativeFormComparison.fieldTest k S)) := ⊥

local instance {k S : Type u} [Field k] [Field S] [Algebra k S] (G : GroupScheme k) :
    DiscreteTopology (Specs.AutomorphismSequence.RelativeAut G
      (Specs.RelativeFormComparison.fieldTest k S)) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
theorem pinnedModelOfForm : PinnedModelOfForm.{u} := by
  intro k S _ _ _ _ A P H hH
  obtain ⟨D, l, Q, E, _, C, hm, _, _, hd, hu⟩ :=
    Descent.QuasiSplitInnerForms.quasiSplitInnerForms (S := S) P
  obtain ⟨a, _, ha⟩ := C.computes H (relativeTrivialization H)
  let ω := mapCocycle (outerHom (S := S) E) continuous_of_discreteTopology hm.1 a
  obtain ⟨W⟩ := hd ω
  have hω : mapH1 (outerHom (S := S) E) continuous_of_discreteTopology hm.1
      (C.equiv (Quotient.mk _ H)) = classOf ω := by
    rw [ha]
    rfl
  have hHclass := (hu (classOf ω) (Quotient.mk _ H)).mp ⟨hω, H, rfl, hH⟩
  have hWclass := pinnedClass E C hm ω W
  have hHW := C.equiv.injective (hWclass.trans hHclass.symm)
  exact ⟨D, l, Q, E, ω, W, basedLift_of_splitSequence E, Quotient.exact hHW⟩

open Specs.SimplyConnectedLattice (GeometricallySimplyConnected)
open private latticeCriterion_pair
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
theorem unmarkedModel : UnmarkedModel.{u} := by
  intro k _ G hG hsc M
  let S := SeparableClosure k
  have hGred := reductive_of_semisimple G hG
  obtain ⟨L, hs⟩ := finiteTorusSplitting (S := S)
    (closedSubgroupAlgebraicGroup M.torus) M.isTorus
  obtain ⟨Q, hQ⟩ := splitPairOverField G hGred M.torus M.isTorus M.maximal hs
  let D := Classification.Pinning.attachedDatum Q
  let e : (groupBaseChange k L).obj G.val ≅ Q.G.val :=
    eqToIso (congrArg Subtype.val hQ.symm)
  have hD := corootLatticeAfterSplitting G hG hsc Q D ⟨e⟩
  obtain ⟨A, P, D₀, hP, hD₀, ⟨j⟩⟩ := groundFieldModel (k := k) (K := (L : Type u)) Q D hD
  let jL : (groupBaseChange k L).obj P.pair.G.val ≅ (groupBaseChange k L).obj G.val :=
    j ≪≫ e.symm
  let q := groupBaseChangeTower (k := k) (K := L) S
  let jS : (groupBaseChange k S).obj P.pair.G.val ≅ (groupBaseChange k S).obj G.val :=
    q.app P.pair.G.val ≪≫ (groupBaseChange L S).mapIso jL ≪≫ q.symm.app G.val
  let H : Descent.Forms.SchemeModels S P.pair.G := ⟨G, ⟨jS⟩⟩
  obtain ⟨D₁, l, J, E, ω, W, hl, hw⟩ :=
    pinnedModelOfForm P H ⟨hGred, M.positive, M.positiveBorel⟩
  let realize := Classification.IntegralRealization.integralRealization
  have hPsc : GeometricallySimplyConnected P.pair.G :=
    (latticeCriterion_pair realize _ D₀ hP).mpr hD₀
  exact ⟨A, P, D₁, l, J, E, ω, W, hP,
    (latticeCriterion_pair realize _ D₁ hP).mp hPsc, hl, hw⟩

open Specs.GeometricBorelConjugacy (IsKBorel ConjugatesSubgroups subgroupOfSubgroup)
open Specs.Relative.MaximalSplitTori (IsMinimalParabolic)
open private borelParabolic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment
open private extendSubgroup subgroup_baseChange_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

private theorem minimal_of_borel {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (B : ClosedSubgroup G.val) (hB : IsKBorel B) :
    IsMinimalParabolic G B := by
  refine ⟨borelParabolic G hG B hB, ?_⟩
  intro P hP hPB
  let L := AlgebraicClosure k
  obtain ⟨_, hBgeom⟩ := hB
  obtain ⟨_, C, hC, hCP⟩ := hP.2.2
  have hPB' := (subgroup_baseChange_iff (K := L) P B).mpr hPB
  have hCB : IsSubgroupOf C (extendSubgroup L B) := by
    obtain ⟨i, hi⟩ := (show IsSubgroupOf C (extendSubgroup L P) from hCP)
    obtain ⟨j, hj⟩ := hPB'
    exact ⟨i ≫ j, by rw [Category.assoc, hj, hi]⟩
  obtain ⟨i, hi⟩ := hC.2 (extendSubgroup L B) hBgeom.1 hCB
  obtain ⟨j, hj⟩ := (show IsSubgroupOf C (extendSubgroup L P) from hCP)
  exact (subgroup_baseChange_iff (K := L) B P).mp
    ⟨i ≫ j, by rw [Category.assoc, hj, hi]⟩

private theorem rationalBorelsConjugate {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (B C : ClosedSubgroup G.val) (hB : IsKBorel B) (hC : IsKBorel C) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ G.val.X, ConjugatesSubgroups g B C :=
  Relative.MaximalSplitTori.minimalParabolicsConjugate G B C
    (minimal_of_borel G hG B hB) (minimal_of_borel G hG C hC)

open CategoryTheory.CartesianMonoidalCategory
open Specs.LeviConjugacy (Transports)
open private conjugationIso conjugate comp_conjugate conjugate_inv_cancel conjugate_comp
  restrictSubgroup compose_restrict
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private isIso_torus_to_limit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private subgroupOf_mutual_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

set_option backward.isDefEq.respectTransparency false in
private theorem conjugates_of_transports {k : Type u} [Field k] {G : GroupScheme k}
    {T T' : ClosedSubgroup G} (g : 𝟙_ (SchemeOver k) ⟶ G.X)
    (h : Transports T T' g) : ConjugatesSubgroups g T T' := by
  let j := conjugationIso g
  let U := transportSubgroup j T
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h
  have step {H J : ClosedSubgroup G} (a : 𝟙_ (SchemeOver k) ⟶ G.X)
      (f : H.group.X ⊗ (𝟙_ (SchemeOver k)) ⟶ J.group.X)
      (hf : f ≫ J.inclusion.hom.hom = conjugateFamily H.inclusion a) :
      (lift (𝟙 _) (toUnit _) ≫ f) ≫ J.inclusion.hom.hom =
        conjugate a H.inclusion.hom.hom := by
    rw [Category.assoc, hf, comp_conjugateFamily]
    simp only [lift_fst_assoc, lift_snd_assoc, Category.id_comp, conjugate]
  let a := lift (𝟙 _) (toUnit _) ≫ p
  let b := lift (𝟙 _) (toUnit _) ≫ q
  have ha : a ≫ T'.inclusion.hom.hom = U.inclusion.hom.hom := by
    rw [step g p hp]
    change _ = T.inclusion.hom.hom ≫ conjugate g (𝟙 _)
    rw [comp_conjugate, Category.comp_id]
  have hb : b ≫ U.inclusion.hom.hom = T'.inclusion.hom.hom := by
    change b ≫ T.inclusion.hom.hom ≫ conjugate g (𝟙 _) = _
    rw [← Category.assoc, step g⁻¹ q hq, comp_conjugate, Category.comp_id]
    simpa only [inv_inv] using conjugate_inv_cancel g⁻¹ T'.inclusion.hom.hom
  letI := U.isClosedImmersion
  letI := T'.isClosedImmersion
  letI : Mono U.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono T'.inclusion.hom.hom := Over.mono_of_mono_left _
  letI := isMonHom_of_factor U.inclusion T'.inclusion a ha
  letI := isMonHom_of_factor T'.inclusion U.inclusion b hb
  obtain ⟨d, hd⟩ := subgroupOf_mutual_iso
    (A := U) (B := T') ⟨Grp.homMk a, Grp.hom_ext _ _ ha⟩ ⟨Grp.homMk b, Grp.hom_ext _ _ hb⟩
  refine ⟨d, ?_⟩
  rw [hd]
  change T.inclusion.hom.hom ≫ conjugate g (𝟙 _) = _
  rw [comp_conjugate, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
private theorem rationalBorelToriConjugate {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G) (B : ClosedSubgroup G.val)
    (hB : IsKBorel B) (T T' : ClosedSubgroup B.group)
    (hT : IsGeometricallyMaximal (subgroupOfSubgroup B T))
    (hT' : IsGeometricallyMaximal (subgroupOfSubgroup B T')) :
    ∃ a : 𝟙_ (SchemeOver k) ⟶ B.group.X, ConjugatesSubgroups a T T' := by
  have hP := borelParabolic G hG B hB
  obtain ⟨c, D, e, U, _, L, _, _, _, _, hker, _, _, hD, hU, _⟩ :=
    Relative.Parabolics.rationalParabolics.1 G B hP
  have h₁ : IsIso (T.inclusion ≫ (e.hom ≫ D.limit)) := by
    rw [← Category.assoc]
    exact isIso_torus_to_limit D e hG hB hT hD
  have h₂ : IsIso (T'.inclusion ≫ (e.hom ≫ D.limit)) := by
    rw [← Category.assoc]
    exact isIso_torus_to_limit D e hG hB hT' hD
  obtain ⟨a, ha, _⟩ := Relative.Parabolics.rationalParabolics.2.1 G B hP U hU
    (closedSubgroupAlgebraicGroup D.centralizer) (e.hom ≫ D.limit) hker T T' h₁ h₂
  exact ⟨a ≫ U.inclusion.hom.hom, conjugates_of_transports _ ha⟩

open private pushKBorel maximalTransport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private conjugatesSubgroups_square conjugates_by_subgroup_point
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem alignBorelAndTorus {k : Type u} [Field k]
    {G H : AffineAlgebraicGroup k} (hH : IsReductive H)
    (B T : ClosedSubgroup G.val) (B' T' : ClosedSubgroup H.val)
    (hB : IsKBorel B) (hB' : IsKBorel B')
    (hT : IsGeometricallyMaximal T) (hT' : IsGeometricallyMaximal T')
    (hTB : IsSubgroupOf T B) (hT'B' : IsSubgroupOf T' B') (i : G.val ≅ H.val) :
    ∃ (e : G.val ≅ H.val) (b : B.group ≅ B'.group) (t : T.group ≅ T'.group),
      B.inclusion ≫ e.hom = b.hom ≫ B'.inclusion ∧
      T.inclusion ≫ e.hom = t.hom ≫ T'.inclusion := by
  obtain ⟨g, b, hb⟩ := rationalBorelsConjugate H hH (transportSubgroup i B) B'
    (pushKBorel i hB) hB'
  let j := i ≪≫ conjugationIso g
  have hj : B.inclusion ≫ j.hom = b.hom ≫ B'.inclusion := by
    rw [Iso.trans_hom, ← Category.assoc]
    exact conjugatesSubgroups_square g b hb
  let V := transportSubgroup j T
  have hV := maximalTransport j T hT
  obtain ⟨u, hu⟩ := hTB
  obtain ⟨u', hu'⟩ := hT'B'
  have hU : (u ≫ b.hom) ≫ B'.inclusion = V.inclusion := by
    change _ = T.inclusion ≫ j.hom
    rw [Category.assoc, ← hj, ← Category.assoc, hu]
  let L := restrictSubgroup V B' (u ≫ b.hom) hU
  let L' := restrictSubgroup T' B' u' hu'
  have hL : IsGeometricallyMaximal (subgroupOfSubgroup B' L) :=
    (compose_restrict V B' (u ≫ b.hom) hU).symm ▸ hV
  have hL' : IsGeometricallyMaximal (subgroupOfSubgroup B' L') :=
    (compose_restrict T' B' u' hu').symm ▸ hT'
  obtain ⟨a, t, ht⟩ := rationalBorelToriConjugate H hH B' hB' L L' hL hL'
  let v := a ≫ B'.inclusion.hom.hom
  obtain ⟨aB, haB⟩ := conjugates_by_subgroup_point B' a
  have hTv : V.inclusion ≫ (conjugationIso v).hom = t.hom ≫ T'.inclusion := by
    apply Grp.hom_ext
    change V.inclusion.hom.hom ≫ conjugate v (𝟙 _) =
      (t.hom ≫ T'.inclusion).hom.hom
    rw [comp_conjugate, Category.comp_id]
    change (t.hom ≫ L'.inclusion).hom.hom = conjugate a L.inclusion.hom.hom at ht
    have hs := congrArg (fun x => x ≫ B'.inclusion.hom.hom) ht
    rw [conjugate_comp, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, Category.assoc] at hs
    change (t.hom ≫ u' ≫ B'.inclusion).hom.hom =
      conjugate v (((u ≫ b.hom) ≫ B'.inclusion).hom.hom) at hs
    rw [hu', hU] at hs
    exact hs.symm
  refine ⟨j ≪≫ conjugationIso v, b ≪≫ aB, t, ?_, ?_⟩
  · simp only [Iso.trans_hom, ← Category.assoc B.inclusion, hj, Category.assoc,
      conjugatesSubgroups_square v aB haB]
  · change T.inclusion ≫ (j.hom ≫ (conjugationIso v).hom) = _
    rw [← Category.assoc]
    exact hTv

open Specs.AdjointBorelCohomology (PinnedTwist)
open Descent (SemilinearAction)
open private coordinateHopfMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private coordinateMap_id from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.PinnedPairDescent
open private extendedHopfMap_equivariant from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent

private noncomputable abbrev pairCoordinateMap := @Specs.AdjointCocharacters.coordinateHopfMap

private def inverseCoordinateIso {k : Type u} [Field k] {G H : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) : pairCoordinateHopf G ≅ pairCoordinateHopf H where
  hom := pairCoordinateMap (G := H) (H := G) e.inv
  inv := pairCoordinateMap (G := G) (H := H) e.hom
  hom_inv_id := by rw [← coordinateHopfMap_comp, e.hom_inv_id, coordinateMap_id]
  inv_hom_id := by rw [← coordinateHopfMap_comp, e.inv_hom_id, coordinateMap_id]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem coordinateIso_square {k : Type u} [Field k] {G H X Y : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) (d : X.val ≅ Y.val) (i : X.val ⟶ G.val) (j : Y.val ⟶ H.val)
    (h : i ≫ e.hom = d.hom ≫ j) :
    (inverseCoordinateIso (G := G) (H := H) e).hom ≫ pairCoordinateMap (G := Y) (H := H) j =
      pairCoordinateMap (G := X) (H := G) i ≫ (inverseCoordinateIso (G := X) (H := Y) d).hom := by
  have hh : j ≫ e.inv = d.inv ≫ i := by
    apply (cancel_epi d.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  change pairCoordinateMap e.inv ≫ pairCoordinateMap j =
    pairCoordinateMap i ≫ pairCoordinateMap d.inv
  rw [← coordinateHopfMap_comp, ← coordinateHopfMap_comp, hh]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1300000 in
private def transportPinnedTwist {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G H : AffineAlgebraicGroup k}
    {B T : ClosedSubgroup G.val} {B' T' : ClosedSubgroup H.val}
    (w : PinnedTwist K D l B T) (e : G.val ≅ H.val) (b : B.group ≅ B'.group)
    (t : T.group ≅ T'.group)
    (hb : B.inclusion ≫ e.hom = b.hom ≫ B'.inclusion)
    (ht : T.inclusion ≫ e.hom = t.hom ≫ T'.inclusion) : PinnedTwist K D l B' T' := by
  let F := CharacterDescent.extendedHopfFunctor (k := k) K
  let eg := inverseCoordinateIso (G := G) (H := H) e
  let bg := closedSubgroupAlgebraicGroup B
  let bh := closedSubgroupAlgebraicGroup B'
  let tg := closedSubgroupAlgebraicGroup T
  let th := closedSubgroupAlgebraicGroup T'
  refine ⟨w.outer, w.groupIso ≪≫ F.mapIso eg,
    w.borelIso ≪≫ F.mapIso (inverseCoordinateIso (G := bg) (H := bh) b),
    w.torusIso ≪≫ F.mapIso (inverseCoordinateIso (G := tg) (H := th) t), ?_, ?_, ?_⟩
  · have h := congrArg F.map (coordinateIso_square (G := G) (H := H)
      (X := bg) (Y := bh) e b B.inclusion B'.inclusion hb)
    simp only [F.map_comp] at h
    let X := closedSubgroupAlgebraicGroup P.pair.B
    let p := F.map (pairCoordinateMap (G := X) (H := P.pair.G) P.pair.B.inclusion)
    let f := F.map (pairCoordinateMap (G := bg) (H := G) B.inclusion)
    let g := F.map (pairCoordinateMap (G := bh) (H := H) B'.inclusion)
    let d := F.map (inverseCoordinateIso (G := bg) (H := bh) b).hom
    have hw : w.groupIso.hom ≫ f = p ≫ w.borelIso.hom := w.borelComm
    change (w.groupIso.hom ≫ F.map eg.hom) ≫ g = p ≫ (w.borelIso.hom ≫ d)
    change F.map eg.hom ≫ g = f ≫ d at h
    rw [Category.assoc, h, ← Category.assoc, hw, Category.assoc]
  · have h := congrArg F.map (coordinateIso_square (G := G) (H := H)
      (X := tg) (Y := th) e t T.inclusion T'.inclusion ht)
    simp only [F.map_comp] at h
    let X := closedSubgroupAlgebraicGroup P.pair.T
    let p := F.map (pairCoordinateMap (G := X) (H := P.pair.G) P.pair.T.inclusion)
    let f := F.map (pairCoordinateMap (G := tg) (H := G) T.inclusion)
    let g := F.map (pairCoordinateMap (G := th) (H := H) T'.inclusion)
    let d := F.map (inverseCoordinateIso (G := tg) (H := th) t).hom
    have hw : w.groupIso.hom ≫ f = p ≫ w.torusIso.hom := w.torusComm
    change (w.groupIso.hom ≫ F.map eg.hom) ≫ g = p ≫ (w.torusIso.hom ≫ d)
    change F.map eg.hom ≫ g = f ≫ d at h
    rw [Category.assoc, h, ← Category.assoc, hw, Category.assoc]
  · intro σ x
    let a := (Functor.mapAut P (forgetPinning (A := A)) (l (w.outer σ))).asIso.inv
    let sG := SemilinearAction.scalarExtension (k := k) (K := K) (pairCoordinateHopf G)
    let sH := SemilinearAction.scalarExtension (k := k) (K := K) (pairCoordinateHopf H)
    let sP := SemilinearAction.scalarExtension (k := k) (K := K) (pairCoordinateHopf P.pair.G)
    change sH.act σ ((F.map eg.hom).hom (w.groupIso.hom.hom x)) =
      (F.map eg.hom).hom (w.groupIso.hom.hom ((F.map (pairCoordinateMap (G := P.pair.G) (H := P.pair.G) a)).hom (sP.act σ x)))
    have h : (F.map eg.hom).hom (sG.act σ (w.groupIso.hom.hom x)) =
        sH.act σ ((F.map eg.hom).hom (w.groupIso.hom.hom x)) :=
      extendedHopfMap_equivariant (K := K) eg.hom σ (w.groupIso.hom.hom x)
    rw [← h, w.twistedAction]
    rfl

open private subgroup_of_intersection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

private theorem commonTorus_le_borel {k : Type u} [Field k]
    {G : AffineAlgebraicGroup k} (M : BorelPair G) {B : ClosedSubgroup G.val}
    (hB : B ∈ ({M.positive, M.negative} : Set (ClosedSubgroup G.val))) :
    IsSubgroupOf M.torus B :=
  (subgroup_of_intersection M.intersection).mp ⟨𝟙 _, Category.id_comp _⟩ B hB

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem positivePinnedComparison : PositivePinnedComparison.{u} := by
  intro k _ G hG hsc M
  obtain ⟨A, P, D, l, Q, E, ω, W, hP, hD, hl, ⟨i⟩⟩ := unmarkedModel G hG hsc M
  obtain ⟨e, b, t, hb, ht⟩ := alignBorelAndTorus (reductive_of_semisimple G hG)
    W.B W.T M.positive M.torus W.borel M.positiveBorel W.maximal M.maximal
    ⟨W.j, W.j_comm⟩ (commonTorus_le_borel M (by simp)) i
  exact ⟨W.layer, inferInstance, inferInstance, inferInstance, inferInstance, A, P, D, l,
    transportPinnedTwist W.data e b t hb ht, hP, hD, hl⟩

open CocharacterDynamics (LimitDecomposition multiplyFactors oppositeCocharacter)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open Specs.RankOneFlag (SameSubgroup)
open Specs.BorelsAndChambers (contractingSubgroup)
open private opposite_regular from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolics

private theorem subgroupSections_mono {k : Type u} [Field k] {G : GroupScheme k}
    {H J : ClosedSubgroup G} (h : IsSubgroupOf H J) (Y : SchemeOver k) :
    SubgroupSections H Y ≤ SubgroupSections J Y := by
  rintro x ⟨y, rfl⟩
  change Y ⟶ H.group.X at y
  obtain ⟨i, hi⟩ := h
  refine ⟨y ≫ i.hom.hom, ?_⟩
  change (y ≫ i.hom.hom) ≫ J.inclusion.hom.hom = y ≫ H.inclusion.hom.hom
  rw [Category.assoc, ← Grp.comp_hom_hom, hi]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
private theorem limitBorelIntersection {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (T B : ClosedSubgroup G.val)
    {c : Specs.CharacterDescent.Cocharacter G.val}
    (D : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hB : SameSubgroup B D.parabolic) (hT : SameSubgroup E.centralizer T)
    (hTB : IsSubgroupOf T B) (hTE : IsSubgroupOf T E.parabolic) :
    IsSchemeIntersection {B, E.parabolic} T := by
  intro Y y
  constructor
  · intro hy H hH
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hH
    rcases hH with rfl | rfl
    · exact subgroupSections_mono hTB Y hy
    · exact subgroupSections_mono hTE Y hy
  · intro h
    have hyB := h B (by simp)
    obtain ⟨z, hz⟩ := h E.parabolic (by simp)
    let m := multiplyFactors E.sectionMap E.contractingToParabolic
    letI : IsIso m := E.product_iso
    let w := z ≫ inv m
    let a := w ≫ fst E.centralizer.group.X E.contracting.group.X
    let b := w ≫ snd E.centralizer.group.X E.contracting.group.X
    let x := a ≫ E.centralizer.inclusion.hom.hom
    let u := b ≫ E.contracting.inclusion.hom.hom
    have hw : w ≫ m = z := by simp [w]
    have hxu : y = x * u := by
      change z ≫ E.parabolic.inclusion.hom.hom = y at hz
      rw [← hz, ← hw, Category.assoc]
      change w ≫ m ≫ E.parabolic.inclusion.hom.hom = _
      simp only [m, multiplyFactors, MonObj.mul_comp, MonObj.comp_mul, Category.assoc,
        ← Grp.comp_hom_hom, E.section_in_G, E.contracting_in_G, x, u, a, b]
    have hxT : x ∈ SubgroupSections T Y := subgroupSections_mono hT.1 Y ⟨a, rfl⟩
    have hxB := subgroupSections_mono hTB Y hxT
    have huB : u ∈ SubgroupSections B Y := by
      have he : u = x⁻¹ * y := by rw [hxu, inv_mul_cancel_left]
      rw [he]
      exact (SubgroupSections B Y).mul_mem ((SubgroupSections B Y).inv_mem hxB) hyB
    obtain ⟨d, hd⟩ := subgroupSections_mono hB.1 Y huB
    change d ≫ D.parabolic.inclusion.hom.hom = u at hd
    have hp := CocharacterDynamics.oppositeLimitIntersection G c D E
    let f := hp.lift b d hd.symm
    have hf : f ≫ η[E.contracting.group.X] = b := hp.lift_fst _ _ _
    have hu : u = 1 := by
      change b ≫ E.contracting.inclusion.hom.hom = 1
      rw [← hf, Category.assoc, IsMonHom.one_hom,
        toUnit_unique f (toUnit Y)]
      rfl
    rw [hxu, hu, mul_one]
    exact hxT

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
theorem splitOppositePair : SplitOppositePair.{u} := by
  intro k _ A P
  let Q := P.pair
  obtain ⟨c, D, hc, hB, _⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT Q.G Q.reductive Q.T Q.split Q.maximal).1
      Q.B Q.borel Q.containsTorus
  let c' := oppositeCocharacter c
  have hc' := opposite_regular hc
  obtain ⟨E⟩ := CocharacterDynamics.existsLimitDecomposition Q.G (c' ≫ Q.T.inclusion)
  have hE := RootData.BorelsAndChambers.regularCocharacterBorel Q.G Q.reductive Q.T
    Q.split Q.maximal c' hc' E
  obtain ⟨_, _, _, _, _, _, dec⟩ :=
    RootData.BorelPositivity.borelPositivity Q.G Q.reductive Q.T Q.split Q.maximal
  obtain ⟨U, _, _, hu, _⟩ := dec Q.B Q.borel Q.containsTorus
  let M : BorelPair Q.G :=
    ⟨Q.B, E.parabolic, Q.T, U, contractingSubgroup E, Q.borel, hE.2.1,
      lattice_torus_of_split Q.split, Q.maximal,
      limitBorelIntersection Q.G Q.T Q.B D E hB hE.1 Q.containsTorus hE.2.2.1,
      hu, hE.2.2.2.2.1⟩
  exact ⟨M, rfl, rfl⟩

open private radical_of_torus_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private baseChangeKernelSquare from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components
open private eligible_baseChange_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private transported_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.LeviConjugacy

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
theorem borelRadicalBaseChange : BorelRadicalBaseChange.{u} := by
  intro k K _ _ _ G hG B hB T hT hs U hU
  let A := closedSubgroupAlgebraicGroup B
  let L := closedSubgroupAlgebraicGroup (G := A) T
  let F := groupBaseChange k K
  obtain ⟨R, q, hR, _, hq, _⟩ := Descent.AdjointBorelCohomology.borelTorusQuotient G B hG hB T hT
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso (hR.2.2 U hU.1 hU.2.1) (hU.2.2 R hR.1 hR.2.1)
  have hk : IsSchemeKernel q U := by
    have h : IsSchemeKernel ((𝟙 A.val) ≫ q) U :=
      transported_kernel (Iso.refl A.val) e (by simpa only [Iso.refl_hom, Category.comp_id] using he) hq.1
    simpa only [Category.id_comp] using h
  let UK := extendSubgroup K U
  have hkK : IsSchemeKernel (F.map q) UK := baseChangeKernelSquare (K := K) q U.inclusion hk
  have hn := (eligible_baseChange_iff (K := K) (G := A) U).mpr hU.1
  have hu := (Unipotent.unipotenceFieldExtension (K := K) (closedSubgroupAlgebraicGroup (G := A) U)).mpr
    hU.2.1
  exact ⟨UK.isClosedImmersion, radical_of_torus_kernel (A := baseChangedAlgebraicGroup K A)
    (L := baseChangedAlgebraicGroup K L) UK (F.map q) hkK hs hn.1 hn.2.1 hu⟩

open Specs.GeometricRadicals (IsUnipotentRadical)
open Specs.Unipotent (IsUnipotent)
open private unipotent_of_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange

set_option backward.isDefEq.respectTransparency false in
private theorem borelRadicalAfterSplitting {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : AffineAlgebraicGroup k} (hG : IsReductive G) {B T : ClosedSubgroup G.val}
    (hB : IsKBorel B) (hm : IsGeometricallyMaximal T) (ht : IsSubgroupOf T B)
    (hs : IsSplitTorus ((groupBaseChange k K).obj T.group))
    {U : ClosedSubgroup B.group} (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    IsUnipotentRadical (baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup B))
      (extendSubgroup K U) := by
  obtain ⟨j, hj⟩ := ht
  let L := restrictSubgroup T B j hj
  have hmL : IsGeometricallyMaximal (subgroupOfSubgroup B L) :=
    (compose_restrict T B j hj).symm ▸ hm
  obtain ⟨_, hr⟩ := borelRadicalBaseChange G hG B hB L hmL hs U hU
  exact hr

set_option backward.isDefEq.respectTransparency false in
private theorem compareUnipotentRadicals {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (e : G.val ≅ H.val) {U : ClosedSubgroup G.val} {V : ClosedSubgroup H.val}
    (hU : IsUnipotentRadical G U) (hV : IsUnipotentRadical H V) :
    ∃ d : U.group ≅ V.group, U.inclusion ≫ e.hom = d.hom ≫ V.inclusion := by
  have ht := radical_transport e IsUnipotent
    (fun {_ _} d _ _ => unipotent_of_iso d) U hU
  obtain ⟨d, hd, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique H IsUnipotent ht hV
  exact ⟨d, hd.symm⟩

open QuasiSplitBorelPairBaseChange (extendBorelPair)
open QuasiSplitOppositeBorelUniqueness (oppositeUniqueness)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
private theorem compareMarkedBorelPairs {k K : Type u} [Field k] [Field K] [Algebra k K]
    {P G : AffineAlgebraicGroup k} (S : BorelPair P) (M : BorelPair G)
    (hPr : IsReductive P) (hGr : IsReductive G)
    (e : (groupBaseChange k K).obj P.val ≅ (groupBaseChange k K).obj G.val)
    (b : (groupBaseChange k K).obj S.positive.group ≅ (groupBaseChange k K).obj M.positive.group)
    (t : (groupBaseChange k K).obj S.torus.group ≅ (groupBaseChange k K).obj M.torus.group)
    (hb : (groupBaseChange k K).map S.positive.inclusion ≫ e.hom =
      b.hom ≫ (groupBaseChange k K).map M.positive.inclusion)
    (ht : (groupBaseChange k K).map S.torus.inclusion ≫ e.hom =
      t.hom ≫ (groupBaseChange k K).map M.torus.inclusion)
    (hs : IsSplitTorus ((groupBaseChange k K).obj S.torus.group)) :
    IsSplitTorus ((groupBaseChange k K).obj M.torus.group) ∧
      ∃ cmp : MarkedComparison (K := K) S M, cmp.groupIso = e := by
  let F := groupBaseChange k K
  have hm : IsSplitTorus (F.obj M.torus.group) := by
    obtain ⟨r, ⟨s⟩⟩ := hs
    exact ⟨r, ⟨t.symm ≪≫ s⟩⟩
  obtain ⟨_, _, _, hPK, hSBK, hSCK, hSTK, hSinter⟩ :=
    extendBorelPair (K := K) P hPr S.positive S.negative S.torus S.positiveBorel S.negativeBorel
      S.isTorus S.maximal S.intersection hs
  obtain ⟨_, _, _, hGK, hMBK, hMCK, hMTK, hMinter⟩ :=
    extendBorelPair (K := K) G hGr M.positive M.negative M.torus M.positiveBorel M.negativeBorel
      M.isTorus M.maximal M.intersection hm
  obtain ⟨c, hc, _⟩ := oppositeUniqueness hPK hGK
    (extendSubgroup K S.torus) (extendSubgroup K S.positive) (extendSubgroup K S.negative)
    (extendSubgroup K M.torus) (extendSubgroup K M.positive) (extendSubgroup K M.negative)
    hs hm hSTK hMTK hSBK hSCK hMBK hMCK hSinter hMinter e t b ht hb
  obtain ⟨u, hu⟩ := compareUnipotentRadicals
    (G := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup S.positive))
    (H := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup M.positive))
    (U := extendSubgroup K S.positiveRadical) (V := extendSubgroup K M.positiveRadical) b
    (borelRadicalAfterSplitting hPr S.positiveBorel S.maximal (commonTorus_le_borel S (by simp))
      hs S.positiveUnipotentRadical)
    (borelRadicalAfterSplitting hGr M.positiveBorel M.maximal (commonTorus_le_borel M (by simp))
      hm M.positiveUnipotentRadical)
  obtain ⟨v, hv⟩ := compareUnipotentRadicals
    (G := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup S.negative))
    (H := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup M.negative))
    (U := extendSubgroup K S.negativeRadical) (V := extendSubgroup K M.negativeRadical) c
    (borelRadicalAfterSplitting hPr S.negativeBorel S.maximal (commonTorus_le_borel S (by simp))
      hs S.negativeUnipotentRadical)
    (borelRadicalAfterSplitting hGr M.negativeBorel M.maximal (commonTorus_le_borel M (by simp))
      hm M.negativeUnipotentRadical)
  have compose_marked {B : ClosedSubgroup P.val} {B' : ClosedSubgroup G.val}
      {U : ClosedSubgroup B.group} {U' : ClosedSubgroup B'.group}
      (a : F.obj B.group ≅ F.obj B'.group) (z : F.obj U.group ≅ F.obj U'.group)
      (ha : F.map B.inclusion ≫ e.hom = a.hom ≫ F.map B'.inclusion)
      (hz : F.map U.inclusion ≫ a.hom = z.hom ≫ F.map U'.inclusion) :
      F.map (subgroupOfSubgroup B U).inclusion ≫ e.hom =
        z.hom ≫ F.map (subgroupOfSubgroup B' U').inclusion := by
    change F.map (U.inclusion ≫ B.inclusion) ≫ e.hom =
      z.hom ≫ F.map (U'.inclusion ≫ B'.inclusion)
    simp only [Functor.map_comp]
    rw [Category.assoc, ha, ← Category.assoc, hz, Category.assoc]
  let marks : ∀ m, F.obj (S.subgroup m).group ≅ F.obj (M.subgroup m).group
    | .positive => b
    | .negative => c
    | .torus => t
    | .positiveRadical => u
    | .negativeRadical => v
  let cmp : MarkedComparison (K := K) S M := ⟨e, marks, by
    intro m
    cases m
    · exact hb
    · exact hc
    · exact ht
    · exact compose_marked b u hb hu
    · exact compose_marked c v hc hv⟩
  exact ⟨hm, cmp, rfl⟩

open Specs.AdjointBorelCohomology (extendedCharacterValue)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open private characterCoordinates characterCoordinates_spec extendedCharacterValue_twist
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private splitPresentation charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private groupLikeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private specGroupMap_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
private theorem splitTorusCoordinateHopf {k : Type u} [Field k]
    (T : AffineAlgebraicGroup k) (hT : IsSplitTorus T.val) :
    Specs.CharacterDescent.IsDiagonalizable (pairCoordinateHopf T) := by
  obtain ⟨r, ⟨s⟩⟩ := splitPresentation hT
  let a : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  have : Group.FG IntegerCharacters.{u} := Group.fg_of_surjective (f := a.toMonoidHom) a.surjective
  have hfg : Group.FG (StandardLattice.{u} r) := inferInstance
  let e := coordinateHopfIso T ≪≫ s.symm
  exact ⟨⟨CommGrpCat.of (StandardLattice.{u} r), hfg⟩,
    ⟨((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso e).unop⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem transportedBasedAction {k K : Type u} [Field k] [Field K] [Algebra k K]
    {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (w : PinnedTwist K D l B T) (hl : IsBasedLift D l) : IsTransportedBasedAction w := by
  let T₀ := closedSubgroupAlgebraicGroup P.pair.T
  let C := pairCoordinateHopf T₀
  obtain ⟨d, _, hd⟩ := CharacterDescent.characterInterpretation (k := k)
  let q := charactersOfIso (coordinateHopfIso T₀)
  let r := ((d C).trans q).symm
  let b := MulEquiv.ofBijective (CharacterDescent.baseChangeCharacterMap K C)
    (CharacterDescent.baseChangeCharacterMap_bijective K C (splitTorusCoordinateHopf T₀ P.pair.split))
  let e := (r.trans b).trans (groupLikeIso w.torusIso)
  have he (χ : Specs.CharacterDescent.Character T₀.val) :
      (e χ).val = w.torusIso.hom.hom (extendedCharacterValue K T₀ χ) := by
    let x := r χ
    obtain ⟨f, hf, hspec⟩ := hd C x
    have h : (d C) x = (coordinateHopfIso T₀).hom ≫ χ := (d C).apply_symm_apply (q.symm χ)
    have hh : f = characterCoordinates (G := T₀) χ :=
      specGroupMap_injective (hspec.symm.trans (h.trans (characterCoordinates_spec χ).symm))
    rw [hh] at hf
    change w.torusIso.hom.hom ((1 : K) ⊗ₜ[k] x.val) = _
    rw [← hf]
    rfl
  refine ⟨e, he, fun σ χ => ?_⟩
  let ψ := transportCharacter (l (w.outer σ)).asIso.hom.torus χ
  have hweight : Additive.toMul ((w.outer σ).asIso.hom.val.weightEquiv (Additive.ofMul χ)) =
      ψ :=
    congrArg Additive.toMul ((hl (w.outer σ)).1 χ)
  let act := (SemilinearAction.scalarExtension (K := K)
    (pairCoordinateHopf (closedSubgroupAlgebraicGroup T))).act σ
  calc
    act (e χ).val = act (w.torusIso.hom.hom (extendedCharacterValue K T₀ χ)) :=
      congrArg (fun x => act x) (he χ)
    _ = w.torusIso.hom.hom (extendedCharacterValue K T₀ ψ) :=
      extendedCharacterValue_twist w σ χ
    _ = (e ψ).val := (he ψ).symm
    _ = _ := congrArg (fun c => (e c).val) hweight.symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The finite pinned model compares the prescribed opposite Borels, their
common maximal torus, and both radicals using the same ambient descent map. -/
theorem initialPinnedComparison : Statement.{u} := by
  intro k _ G hG hsc M
  obtain ⟨K, _, _, _, _, A, P, D, l, w, hP, hD, hl⟩ := positivePinnedComparison G hG hsc M
  obtain ⟨S, hSB, hST⟩ := splitOppositePair P
  let F := groupBaseChange k K
  let e := scalarExtensionComparison P.pair.G G w.groupIso
  have hb' : ∃ b : F.obj S.positive.group ≅ F.obj M.positive.group,
      F.map S.positive.inclusion ≫ e.hom = b.hom ≫ F.map M.positive.inclusion := by
    rw [hSB]
    let X := closedSubgroupAlgebraicGroup P.pair.B
    let Y := closedSubgroupAlgebraicGroup M.positive
    exact ⟨scalarExtensionComparison X Y w.borelIso, scalarExtensionComparison_comm
      (G := P.pair.G) (H := G) (X := X) (Y := Y)
      P.pair.B.inclusion M.positive.inclusion w.groupIso w.borelIso w.borelComm⟩
  have ht' : ∃ t : F.obj S.torus.group ≅ F.obj M.torus.group,
      F.map S.torus.inclusion ≫ e.hom = t.hom ≫ F.map M.torus.inclusion := by
    rw [hST]
    let X := closedSubgroupAlgebraicGroup P.pair.T
    let Y := closedSubgroupAlgebraicGroup M.torus
    exact ⟨scalarExtensionComparison X Y w.torusIso, scalarExtensionComparison_comm
      (G := P.pair.G) (H := G) (X := X) (Y := Y)
      P.pair.T.inclusion M.torus.inclusion w.groupIso w.torusIso w.torusComm⟩
  obtain ⟨b, hb⟩ := hb'
  obtain ⟨t, ht⟩ := ht'
  have hs : IsSplitTorus (F.obj S.torus.group) := by
    rw [hST]
    exact splitTorus_baseChange P.pair.split
  obtain ⟨hm, cmp, hcmp⟩ := compareMarkedBorelPairs S M P.pair.reductive
    (reductive_of_semisimple G hG) e b t hb ht hs
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, A, P, D, l, w, S,
    hSB, hST, hP, hD, hl, hm, transportedBasedAction w hl, cmp,
    matches_scalarExtensionComparison cmp w.groupIso hcmp⟩

end

end LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
