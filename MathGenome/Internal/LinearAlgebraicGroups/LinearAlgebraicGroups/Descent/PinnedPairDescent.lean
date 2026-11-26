import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.PinnedPairDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Descent.PinnedPairDescent

open LinearAlgebraicGroups.Specs
open Specs.PinnedPairDescent
open Specs.AdjointCocharacters (coordinateHopfMap coordinateHopfIso)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsTorus IsMaximalTorus baseChangedSubgroup
  GeometricGroup IsTrivialSubgroup IsUnipotentRadical geometricUnipotentRadical)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel IsSmoothConnectedSolvable)
open RankOneFlag (IsGeometricallyMaximal)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open Pinning (PinnedGroup PinnedIso)
open AutomorphismSequence (forgetPinning)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open private standard standardAct twist coefficientAction coefficientAction_apply aut_ext
  extendedHom_comp extendedHom_id extendedHom_injective extendedIso baseHom_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.Forms
open private coordinateHopfMap_comp coordinateHopfMap_surjective extendedCoordinateIso
  extendedCoordinateIso_comm from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private coordinatePresentationMap from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private specGroupMap_comp specGroupMap_injective tensorMap_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private restrictHopfHom restrictHopfHom_base descendedMap_surjective comparison_equivariant
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AffineGroups

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem coordinateMap_id (G : AffineAlgebraicGroup k) :
    coordinateHopfMap (G := G) (H := G) (𝟙 G.val) = 𝟙 _ := by
  apply specGroupMap_injective
  rw [coordinatePresentationMap]
  simp [specGroupMap]

private def inversePullback {G : AffineAlgebraicGroup k} :
    Aut G.val →* Aut (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G)) where
  toFun a := Aut.of (extendedIso K
    { hom := coordinateHopfMap (G := G) (H := G) a.asIso.inv
      inv := coordinateHopfMap (G := G) (H := G) a.asIso.hom
      hom_inv_id := by rw [← coordinateHopfMap_comp, a.asIso.hom_inv_id, coordinateMap_id]
      inv_hom_id := by rw [← coordinateHopfMap_comp, a.asIso.inv_hom_id, coordinateMap_id] })
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change extendedHopfMap K (coordinateHopfMap (G := G) (H := G) (𝟙 _)) = 𝟙 _
    rw [coordinateMap_id, extendedHom_id]
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    change extendedHopfMap K (coordinateHopfMap (G := G) (H := G)
      (a.asIso.inv ≫ b.asIso.inv)) =
      extendedHopfMap K (coordinateHopfMap (G := G) (H := G) b.asIso.inv) ≫
      extendedHopfMap K (coordinateHopfMap (G := G) (H := G) a.asIso.inv)
    rw [coordinateHopfMap_comp, extendedHom_comp]

private abbrev coefficient {G : AffineAlgebraicGroup k} (a : Aut G.val) :
    extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G) ⟶ extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G) :=
  extendedHopfMap K (coordinateHopfMap (G := G) (H := G) a.asIso.inv)

private def pinnedDatum [FiniteDimensional k K] {G : AffineAlgebraicGroup k} (a : Gal(K/k) →* Aut G.val) :
    HopfDescentDatum k (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G)) := by
  letI : TopologicalSpace (Aut (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G))) := ⊥
  let b := (inversePullback (K := K)).comp a
  let R := standard K (Specs.AdjointCocharacters.coordinateHopf G)
  let c : NonabelianCohomology.Cocycle (coefficientAction R) :=
    ⟨b, continuous_of_discreteTopology, by
      intro σ τ
      rw [map_mul]
      congr 1
      apply aut_ext
      intro x
      obtain ⟨y, rfl⟩ := (R.action.act σ).surjective x
      rw [coefficientAction_apply]
      exact baseHom_equivariant (K := K)
        (coordinateHopfMap (G := G) (H := G) (a τ).asIso.inv) σ y⟩
  exact twist R c

private theorem pinnedDatum_apply [FiniteDimensional k K] {G : AffineAlgebraicGroup k}
    (a : Gal(K/k) →* Aut G.val) (σ : Gal(K/k)) (x : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G)) :
    (pinnedDatum a).action.act σ x =
      (coefficient (a σ)).hom ((standardAct K (Specs.AdjointCocharacters.coordinateHopf G)).act σ x) := rfl

private theorem pinnedDatum_equivariant [FiniteDimensional k K] {G H : AffineAlgebraicGroup k}
    (a : Gal(K/k) →* Aut G.val) (b : Gal(K/k) →* Aut H.val) (f : H.val ⟶ G.val)
    (h : ∀ σ, f ≫ (a σ).asIso.inv = (b σ).asIso.inv ≫ f) :
    (pinnedDatum a).Equivariant (pinnedDatum b)
      (extendedHopfMap K (coordinateHopfMap (G := H) (H := G) f)) := by
  intro σ x
  let q := coordinateHopfMap (G := H) (H := G) f
  have hc : coefficient (K := K) (a σ) ≫ extendedHopfMap K q =
      extendedHopfMap K q ≫ coefficient (K := K) (b σ) := by
    rw [← extendedHom_comp, ← extendedHom_comp, ← coordinateHopfMap_comp,
      ← coordinateHopfMap_comp, h σ]
  change (extendedHopfMap K q).hom ((pinnedDatum a).action.act σ x) =
    (pinnedDatum b).action.act σ ((extendedHopfMap K q).hom x)
  rw [pinnedDatum_apply, pinnedDatum_apply]
  have he := baseHom_equivariant (K := K) q σ x
  change (extendedHopfMap K q).hom ((standardAct K _).act σ x) =
    (standardAct K _).act σ ((extendedHopfMap K q).hom x) at he
  rw [← he]
  exact ConcreteCategory.congr_hom hc _

variable {A B C : HopfAlgebraCategory K}
variable {R : HopfDescentDatum k A} {S : HopfDescentDatum k B} {U : HopfDescentDatum k C}


private theorem descended_comp [FiniteDimensional k K] [IsGalois k K]
    (H : HopfDescent R) (J : HopfDescent S) (M : HopfDescent U)
    {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (eq : f ≫ g = h)
    (hf : R.Equivariant S f) (hg : S.Equivariant U g) (hh : R.Equivariant U h) :
    restrictHopfHom H J f hf ≫ restrictHopfHom J M g hg =
      restrictHopfHom H M h hh := by
  apply (extendedHom_injective (K := K))
  apply (cancel_mono M.iso.hom).mp
  rw [extendedHom_comp, Category.assoc, ← restrictHopfHom_base J M g hg,
    ← Category.assoc, ← restrictHopfHom_base H J f hf, Category.assoc, eq,
    restrictHopfHom_base H M h hh]

private def affineOfDescent {G : AffineAlgebraicGroup k} {D : HopfDescentDatum k
    (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G))} (H : HopfDescent D) : AffineAlgebraicGroup k := by
  let F := Grp.forget (SchemeOver K)
  have hbase : LocallyOfFiniteType ((groupBaseChange k K).obj G.val).X.hom :=
    (Unipotent.baseChangedAlgebraicGroup K G).property.2.1
  let e := F.mapIso (extendedCoordinateIso (K := K) G)
  have ht : LocallyOfFiniteType (specGroup (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G))).X.hom := by
    change LocallyOfFiniteType (F.obj (specGroup (extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G)))).hom
    rw [← Over.w e.hom]
    letI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @LocallyOfFiniteType) e.hom.left _).mpr hbase
  refine ⟨specGroup H.algebra, ?_, (affineGroupDescentProperties H).1 ht⟩
  change IsAffine (Spec (CommRingCat.of H.algebra))
  infer_instance


/-- Coordinates for a specified affine presentation, with the direction of pullback. -/
private def presentationIso (G : AffineAlgebraicGroup k) (H : HopfAlgebraCategory k)
    (e : specGroup H ≅ G.val) : Specs.AdjointCocharacters.coordinateHopf G ≅ H :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso
    (e ≪≫ (coordinateHopfIso G).symm)).unop

private theorem presentationIso_spec (G : AffineAlgebraicGroup k) (H : HopfAlgebraCategory k)
    (e : specGroup H ≅ G.val) :
    specGroupMap (presentationIso G H e).hom = e.hom ≫ (coordinateHopfIso G).inv :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _

private theorem presentationIso_natural {G J : AffineAlgebraicGroup k}
    {H M : HopfAlgebraCategory k} (e : specGroup H ≅ G.val) (d : specGroup M ≅ J.val)
    (f : J.val ⟶ G.val) (q : H ⟶ M) (hq : specGroupMap q ≫ e.hom = d.hom ≫ f) :
    (presentationIso G H e).hom ≫ q =
      coordinateHopfMap (G := J) (H := G) f ≫ (presentationIso J M d).hom := by
  apply specGroupMap_injective
  rw [specGroupMap_comp, specGroupMap_comp, presentationIso_spec, presentationIso_spec,
    coordinatePresentationMap, ← Category.assoc (specGroupMap q), hq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private def coordinateComparison {G : AffineAlgebraicGroup k}
    {D : HopfDescentDatum k A} (H : HopfDescent D) (e : specGroup H.algebra ≅ G.val) :
    A ≅ extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G) :=
  H.iso.symm ≪≫ extendedIso K (presentationIso G H.algebra e).symm

private theorem coordinateComparison_natural {G J : AffineAlgebraicGroup k}
    (H : HopfDescent R) (M : HopfDescent S)
    (e : specGroup H.algebra ≅ G.val) (d : specGroup M.algebra ≅ J.val)
    (f : J.val ⟶ G.val) (q : H.algebra ⟶ M.algebra)
    (hq : specGroupMap q ≫ e.hom = d.hom ≫ f)
    (p : A ⟶ B) (hp : H.iso.hom ≫ p = extendedHopfMap K q ≫ M.iso.hom) :
    (coordinateComparison H e).hom ≫ extendedHopfMap K
      (coordinateHopfMap (G := J) (H := G) f) =
      p ≫ (coordinateComparison M d).hom := by
  let e' := extendedIso K (presentationIso G H.algebra e)
  let d' := extendedIso K (presentationIso J M.algebra d)
  apply (cancel_mono d'.hom).mp
  have hn : e'.hom ≫ extendedHopfMap K q =
      extendedHopfMap K (coordinateHopfMap (G := J) (H := G) f) ≫ d'.hom := by
    change extendedHopfMap K _ ≫ extendedHopfMap K _ =
      extendedHopfMap K _ ≫ extendedHopfMap K _
    rw [← extendedHom_comp, ← extendedHom_comp, presentationIso_natural e d f q hq]
  change ((H.iso.inv ≫ e'.inv) ≫ _) ≫ d'.hom = (p ≫ (M.iso.inv ≫ d'.inv)) ≫ d'.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hn, Iso.inv_hom_id_assoc]
  apply (cancel_epi H.iso.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, hp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem coordinateComparison_equivariant {G : AffineAlgebraicGroup k}
    {D : HopfDescentDatum k A} (H : HopfDescent D) (e : specGroup H.algebra ≅ G.val)
    (σ : Gal(K/k)) (x : A) :
    (standardAct K (Specs.AdjointCocharacters.coordinateHopf G)).act σ ((coordinateComparison H e).hom.hom x) =
      (coordinateComparison H e).hom.hom (D.action.act σ x) := by
  let p := (presentationIso G H.algebra e).inv
  change (standardAct K (Specs.AdjointCocharacters.coordinateHopf G)).act σ
      ((extendedHopfMap K p).hom (H.iso.inv.hom x)) =
    (extendedHopfMap K p).hom (H.iso.inv.hom (D.action.act σ x))
  have he := baseHom_equivariant (K := K) p σ (H.iso.inv.hom x)
  change (extendedHopfMap K p).hom ((standardAct K _).act σ (H.iso.inv.hom x)) =
    (standardAct K _).act σ ((extendedHopfMap K p).hom (H.iso.inv.hom x)) at he
  rw [← he]
  congr 1
  letI := H.operations.toHopfAlgebra
  apply H.comparison.injective
  have hs := comparison_equivariant H σ (H.iso.inv.hom x)
  change H.comparison ((standardAct K H.algebra).act σ (H.comparison.symm x)) =
    D.action.act σ (H.comparison (H.comparison.symm x)) at hs
  change H.comparison ((standardAct K H.algebra).act σ (H.comparison.symm x)) =
    H.comparison (H.comparison.symm (D.action.act σ x))
  simpa only [BialgEquiv.apply_symm_apply] using hs

section Geometry

open private groupBaseChangeTower smooth_baseChange_iff connected_baseChange_iff
  transportSubgroup radical_transport unipotent_of_iso solvable_of_iso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private geometricallyConnected_of_connected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.WordDomainGeometry
open private maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private splitTorus_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

private abbrev underlying (k : Type u) [Field k] : GroupScheme k ⥤ Scheme :=
  Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))

private theorem smooth_of_iso {X Y : GroupScheme k} (e : X ≅ Y) (h : Smooth X.X.hom) :
    Smooth Y.X.hom := by
  let f := (underlying k).map e.inv
  letI : IsIso f := (underlying k).map_isIso e.inv
  have hw : f ≫ X.X.hom = Y.X.hom := Over.w e.inv.hom.hom
  rw [← hw]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth) f _).mpr h

private theorem connected_of_iso {X Y : GroupScheme k} (e : X ≅ Y)
    (h : ConnectedSpace X.X.left) : ConnectedSpace Y.X.left := by
  let f := (underlying k).map e.hom
  letI : IsIso f := (underlying k).map_isIso e.hom
  exact f.homeomorph.connectedSpace_iff.mp h

private theorem inverse_square {X Y S T : GroupScheme k} (e : X ≅ Y) (d : S ≅ T)
    (i : S ⟶ X) (j : T ⟶ Y) (h : d.hom ≫ j = i ≫ e.hom) :
    d.inv ≫ i = j ≫ e.inv := by
  apply (cancel_epi d.hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

private theorem borel_of_square [IsAlgClosed k] {X Y : AffineAlgebraicGroup k}
    (e : X.val ≅ Y.val) (B : ClosedSubgroup X.val) (C : ClosedSubgroup Y.val)
    (d : B.group ≅ C.group) (h : d.hom ≫ C.inclusion = B.inclusion ≫ e.hom)
    (hB : IsBorel B) : IsBorel C := by
  have hs := smooth_of_iso d hB.1.1
  have hc := connected_of_iso d hB.1.2.1
  have hsol := (solvable_of_iso
    (G := closedSubgroupAlgebraicGroup B) (H := closedSubgroupAlgebraicGroup C)
    d hB.1.1 hB.1.2.1 hs hc).mp hB.1.2.2
  refine ⟨⟨hs, hc, hsol⟩, ?_⟩
  intro J hJ hCJ
  obtain ⟨i, hi⟩ := hCJ
  let J' := transportSubgroup e.symm J
  have hBJ : IsSubgroupOf B J' := ⟨d.hom ≫ i, by
    change (d.hom ≫ i) ≫ (J.inclusion ≫ e.inv) = B.inclusion
    simp only [Category.assoc, reassoc_of% hi, reassoc_of% h, Iso.hom_inv_id, Category.comp_id]⟩
  obtain ⟨j, hj⟩ := hB.2 J' hJ hBJ
  refine ⟨j ≫ d.hom, ?_⟩
  change j ≫ B.inclusion = J.inclusion ≫ e.inv at hj
  rw [Category.assoc, h, ← Category.assoc, hj, Category.assoc, e.inv_hom_id, Category.comp_id]

private theorem reductive_of_geometric_iso {G H : AffineAlgebraicGroup k}
    (e : (GeometricGroup G).val ≅ (GeometricGroup H).val) (hG : IsReductive G) :
    IsReductive H := by
  let F := AlgebraicClosure k
  have hsG : Smooth (GeometricGroup G).val.X.hom :=
    (smooth_baseChange_iff (K := F) G.val.X).mpr hG.1
  have hsH : Smooth H.val.X.hom :=
    (smooth_baseChange_iff (K := F) H.val.X).mp (smooth_of_iso e hsG)
  have hcG : GeometricallyConnected G.val.X.hom := hG.2.1
  have hcG' : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  have hcH : ConnectedSpace H.val.X.left :=
    (connected_baseChange_iff (K := F) H).mp
      (connected_of_iso e ((connected_baseChange_iff (K := F) G).mpr hcG'))
  have hcH' := @geometricallyConnected_of_connected k _ H hcH
  refine ⟨hsH, hcH', ?_⟩
  let N := geometricUnipotentRadical G
  have hN : IsUnipotentRadical (GeometricGroup G) N :=
    LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest G
  let M := transportSubgroup e N
  have hM : IsUnipotentRadical (GeometricGroup H) M := by
    apply radical_transport (G := GeometricGroup G) (G' := GeometricGroup H)
      e Specs.Unipotent.IsUnipotent _ N hN
    intro J J' d _ _
    exact unipotent_of_iso (G := closedSubgroupAlgebraicGroup J)
      (H := closedSubgroupAlgebraicGroup J') d
  obtain ⟨d, _, _⟩ := LinearAlgebraicGroups.GeometricRadicals.radicalUnique
    (GeometricGroup H) Specs.Unipotent.IsUnipotent
    (LinearAlgebraicGroups.GeometricRadicals.geometricUnipotentRadicalLargest H) hM
  obtain ⟨t⟩ := hG.2.2
  exact ⟨d ≪≫ t⟩

private def comparisonOver {F : Type u} [Field F] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F] {G H : GroupScheme k}
    (e : (groupBaseChange k K).obj G ≅ (groupBaseChange k K).obj H) :
    (groupBaseChange k F).obj G ≅ (groupBaseChange k F).obj H :=
  (groupBaseChangeTower (k := k) (K := K) F).app G ≪≫
    (groupBaseChange K F).mapIso e ≪≫ (groupBaseChangeTower (k := k) (K := K) F).symm.app H

private theorem comparisonOver_square {F : Type u} [Field F] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F] {G H X Y : GroupScheme k}
    (e : (groupBaseChange k K).obj G ≅ (groupBaseChange k K).obj H)
    (d : (groupBaseChange k K).obj X ≅ (groupBaseChange k K).obj Y)
    (i : X ⟶ G) (j : Y ⟶ H)
    (h : d.hom ≫ (groupBaseChange k K).map j = (groupBaseChange k K).map i ≫ e.hom) :
    (comparisonOver (F := F) d).hom ≫ (groupBaseChange k F).map j =
      (groupBaseChange k F).map i ≫ (comparisonOver (F := F) e).hom := by
  let n := groupBaseChangeTower (k := k) (K := K) F
  let L := groupBaseChange K F
  change (n.hom.app X ≫ L.map d.hom ≫ n.inv.app Y) ≫ (groupBaseChange k F).map j =
    (groupBaseChange k F).map i ≫ n.hom.app G ≫ L.map e.hom ≫ n.inv.app H
  have hw := congrArg L.map h
  simp only [L.map_comp] at hw
  simp only [Category.assoc, ← n.inv.naturality j, n.hom.naturality_assoc i,
    Functor.comp_map]
  rw [← Category.assoc (L.map d.hom), hw, Category.assoc]

private abbrev groupComparison {G H : AffineAlgebraicGroup k}
    (e : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H)) :
    (groupBaseChange k K).obj H.val ≅ (groupBaseChange k K).obj G.val :=
  (extendedCoordinateIso (K := K) H).symm ≪≫
    (hopfSpec (CommRingCat.of K)).mapIso e.op ≪≫ extendedCoordinateIso (K := K) G

private theorem groupComparison_square {G G₀ H H₀ : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (f₀ : G₀.val ⟶ H₀.val)
    (e : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H₀) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H))
    (d : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G₀) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G))
    (h : e.hom ≫ extendedHopfMap K (coordinateHopfMap (G := G) (H := H) f) =
      extendedHopfMap K (coordinateHopfMap (G := G₀) (H := H₀) f₀) ≫ d.hom) :
    (groupComparison (G := G₀) (H := G) d).hom ≫ (groupBaseChange k K).map f₀ =
      (groupBaseChange k K).map f ≫ (groupComparison (G := H₀) (H := H) e).hom := by
  exact extendedCoordinateIso_comm (G := G) (G₀ := G₀) (H := H) (H₀ := H₀) f f₀ d e h

private theorem geometry_of_comparisons [IsGalois k K]
    {P : Specs.Pinning.SplitBorelPair k}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (e : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj P.G.val)
    (b : (groupBaseChange k K).obj B.group ≅ (groupBaseChange k K).obj P.B.group)
    (t : (groupBaseChange k K).obj T.group ≅ (groupBaseChange k K).obj P.T.group)
    (hb : b.hom ≫ (groupBaseChange k K).map P.B.inclusion =
      (groupBaseChange k K).map B.inclusion ≫ e.hom)
    (ht : t.hom ≫ (groupBaseChange k K).map P.T.inclusion =
      (groupBaseChange k K).map T.inclusion ≫ e.hom) :
    IsReductive G ∧ IsKBorel B ∧ IsTorus T.group ∧ IsGeometricallyMaximal T := by
  let F := AlgebraicClosure k
  let a : K →ₐ[k] F := IsAlgClosed.lift
  letI : Algebra K F := a.toRingHom.toAlgebra
  letI : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun x => (a.commutes x).symm
  let e' := comparisonOver (F := F) e
  let b' := comparisonOver (F := F) b
  let t' := comparisonOver (F := F) t
  have hb' := comparisonOver_square (F := F) e b B.inclusion P.B.inclusion hb
  have ht' := comparisonOver_square (F := F) e t T.inclusion P.T.inclusion ht
  obtain ⟨hB₀, hB⟩ := P.borel
  obtain ⟨hT₀, hT⟩ := P.maximal
  let hB' := baseChangeClosedSubgroup k F B.inclusion B.isClosedImmersion
  let hT' := baseChangeClosedSubgroup k F T.inclusion T.isClosedImmersion
  refine ⟨reductive_of_geometric_iso (G := P.G) (H := G) e'.symm P.reductive,
    ⟨hB', ?_⟩, ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩, ⟨hT', ?_⟩⟩
  · exact borel_of_square (X := GeometricGroup P.G) (Y := GeometricGroup G)
      e'.symm (baseChangedSubgroup F P.B hB₀) (baseChangedSubgroup F B hB') b'.symm
      (inverse_square e' b' _ _ hb') hB
  · obtain ⟨r, ⟨j⟩⟩ := splitTorus_baseChange (K := K) P.split
    exact ⟨r, ⟨t ≪≫ j⟩⟩
  · exact maximal_of_square e'.symm
      (baseChangedSubgroup F P.T hT₀) (baseChangedSubgroup F T hT') t'.symm
      (inverse_square e' t' _ _ ht') hT

private theorem descendGeometry [IsGalois k K]
    {L : Specs.RootGroups.AdditiveLine k} {P : PinnedGroup L}
    {D : Specs.Pinning.AttachedDatum P.pair} {l : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (data : Specs.AdjointBorelCohomology.PinnedTwist K D l B T) :
    IsReductive G ∧ IsKBorel B ∧ IsTorus T.group ∧ IsGeometricallyMaximal T := by
  let e := groupComparison (G := P.pair.G) (H := G) data.groupIso
  let b := groupComparison (G := closedSubgroupAlgebraicGroup P.pair.B)
    (H := closedSubgroupAlgebraicGroup B) data.borelIso
  let t := groupComparison (G := closedSubgroupAlgebraicGroup P.pair.T)
    (H := closedSubgroupAlgebraicGroup T) data.torusIso
  have hb : b.hom ≫ (groupBaseChange k K).map P.pair.B.inclusion =
      (groupBaseChange k K).map B.inclusion ≫ e.hom :=
    groupComparison_square (H := G) (H₀ := P.pair.G)
      (G := closedSubgroupAlgebraicGroup B) (G₀ := closedSubgroupAlgebraicGroup P.pair.B)
      B.inclusion P.pair.B.inclusion data.groupIso data.borelIso data.borelComm
  have ht : t.hom ≫ (groupBaseChange k K).map P.pair.T.inclusion =
      (groupBaseChange k K).map T.inclusion ≫ e.hom :=
    groupComparison_square (H := G) (H₀ := P.pair.G)
      (G := closedSubgroupAlgebraicGroup T) (G₀ := closedSubgroupAlgebraicGroup P.pair.T)
      T.inclusion P.pair.T.inclusion data.groupIso data.torusIso data.torusComm
  exact geometry_of_comparisons (P := P.pair) (G := G) (B := B) (T := T) e b t hb ht

end Geometry

section PinnedPair

open Specs.RootGroups (AdditiveLine)
open Specs.AdjointBorelCohomology (PinnedTwist)

private def forgetToBorel {L : AdditiveLine k} : PinnedGroup L ⥤ GroupScheme k where
  obj P := P.pair.B.group
  map f := f.borel.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private def forgetToTorus {L : AdditiveLine k} : PinnedGroup L ⥤ GroupScheme k where
  obj P := P.pair.T.group
  map f := f.torus.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private theorem mono_inclusion {G : GroupScheme k} (B : ClosedSubgroup G) :
    Mono B.inclusion := by
  haveI := B.isClosedImmersion
  exact (underlying k).mono_of_mono_map
    (inferInstanceAs (Mono B.inclusion.hom.hom.left))

private theorem extendedCoordinate_surjective {G H : AffineAlgebraicGroup k}
    (f : G.val ⟶ H.val) (hf : IsClosedImmersion f.hom.hom.left) :
    Function.Surjective (extendedHopfMap K (coordinateHopfMap (G := G) (H := H) f)).hom :=
  tensorMap_surjective (K := K) (coordinateHopfMap (G := G) (H := H) f).hom.toAlgHom
    (coordinateHopfMap_surjective (G := G) (H := H) f hf)

private theorem effectivePair [FiniteDimensional k K] [IsGalois k K]
    {L : AdditiveLine k} {P : PinnedGroup L}
    {D : Specs.Pinning.AttachedDatum P.pair} (l : Aut D.toBased ≃* Aut P)
    (ω : Gal(K/k) →* Aut D.toBased) :
    ∃ (G : AffineAlgebraicGroup k) (B T : ClosedSubgroup G.val)
      (j : T.group ⟶ B.group) (data : PinnedTwist K D l B T),
      j ≫ B.inclusion = T.inclusion ∧ data.outer = ω := by
  let G₀ := P.pair.G
  let B₀ := closedSubgroupAlgebraicGroup P.pair.B
  let T₀ := closedSubgroupAlgebraicGroup P.pair.T
  let a := l.toMonoidHom.comp ω
  let aG : Gal(K/k) →* Aut G₀.val := (Functor.mapAut P forgetPinning).comp a
  let aB : Gal(K/k) →* Aut B₀.val := (Functor.mapAut P forgetToBorel).comp a
  let aT : Gal(K/k) →* Aut T₀.val := (Functor.mapAut P forgetToTorus).comp a
  have hb (σ : Gal(K/k)) :
      P.pair.B.inclusion ≫ (aG σ).asIso.inv = (aB σ).asIso.inv ≫ P.pair.B.inclusion :=
    (a σ).asIso.inv.borel_comm
  have ht (σ : Gal(K/k)) :
      P.pair.T.inclusion ≫ (aG σ).asIso.inv = (aT σ).asIso.inv ≫ P.pair.T.inclusion :=
    (a σ).asIso.inv.torus_comm
  obtain ⟨j₀, hj₀⟩ := P.pair.containsTorus
  have hj (σ : Gal(K/k)) : j₀ ≫ (aB σ).asIso.inv = (aT σ).asIso.inv ≫ j₀ := by
    letI := mono_inclusion P.pair.B
    apply (cancel_mono P.pair.B.inclusion).mp
    rw [Category.assoc, ← hb σ, ← Category.assoc j₀, hj₀, ht σ, Category.assoc, hj₀]
  let fB := extendedHopfMap K (coordinateHopfMap (G := B₀) (H := G₀) P.pair.B.inclusion)
  let fT := extendedHopfMap K (coordinateHopfMap (G := T₀) (H := G₀) P.pair.T.inclusion)
  let fJ := extendedHopfMap K (coordinateHopfMap (G := T₀) (H := B₀) j₀)
  have efB : (pinnedDatum aG).Equivariant (pinnedDatum aB) fB :=
    pinnedDatum_equivariant aG aB P.pair.B.inclusion hb
  have efT : (pinnedDatum aG).Equivariant (pinnedDatum aT) fT :=
    pinnedDatum_equivariant aG aT P.pair.T.inclusion ht
  have efJ : (pinnedDatum aB).Equivariant (pinnedDatum aT) fJ :=
    pinnedDatum_equivariant aB aT j₀ hj
  let HG := descendHopf (pinnedDatum aG)
  let HB := descendHopf (pinnedDatum aB)
  let HT := descendHopf (pinnedDatum aT)
  let gB := restrictHopfHom HG HB fB efB
  let gT := restrictHopfHom HG HT fT efT
  let gJ := restrictHopfHom HB HT fJ efJ
  have fcomp : fB ≫ fJ = fT := by
    dsimp only [fB, fJ, fT]
    rw [← extendedHom_comp, ← coordinateHopfMap_comp, hj₀]
  have gcomp : gB ≫ gJ = gT := descended_comp HG HB HT fcomp efB efJ efT
  have hsurjB : Function.Surjective fB.hom :=
    extendedCoordinate_surjective (K := K) (G := B₀) (H := G₀)
      P.pair.B.inclusion P.pair.B.isClosedImmersion
  have hsurjT : Function.Surjective fT.hom :=
    extendedCoordinate_surjective (K := K) (G := T₀) (H := G₀)
      P.pair.T.inclusion P.pair.T.isClosedImmersion
  have surjB : Function.Surjective gB.hom := descendedMap_surjective HG HB fB efB hsurjB
  have surjT : Function.Surjective gT.hom := descendedMap_surjective HG HT fT efT hsurjT
  let G := affineOfDescent (G := G₀) HG
  let B : ClosedSubgroup G.val :=
    ⟨specGroup HB.algebra, specGroupMap gB, (hopfMapClosedImmersion k gB).mpr surjB⟩
  let T : ClosedSubgroup G.val :=
    ⟨specGroup HT.algebra, specGroupMap gT, (hopfMapClosedImmersion k gT).mpr surjT⟩
  let j : T.group ⟶ B.group := specGroupMap gJ
  have j_comm : j ≫ B.inclusion = T.inclusion := by
    change specGroupMap gJ ≫ specGroupMap gB = specGroupMap gT
    rw [← specGroupMap_comp, gcomp]
  let eG : specGroup HG.algebra ≅ G.val := Iso.refl _
  let eB : specGroup HB.algebra ≅ (closedSubgroupAlgebraicGroup B).val := Iso.refl _
  let eT : specGroup HT.algebra ≅ (closedSubgroupAlgebraicGroup T).val := Iso.refl _
  let data : PinnedTwist K D l B T :=
    { outer := ω
      groupIso := coordinateComparison HG eG
      borelIso := coordinateComparison HB eB
      torusIso := coordinateComparison HT eT
      borelComm := coordinateComparison_natural HG HB eG eB B.inclusion gB
        (by change specGroupMap gB ≫ 𝟙 _ = 𝟙 _ ≫ specGroupMap gB; simp)
        fB (restrictHopfHom_base HG HB fB efB)
      torusComm := coordinateComparison_natural HG HT eG eT T.inclusion gT
        (by change specGroupMap gT ≫ 𝟙 _ = 𝟙 _ ≫ specGroupMap gT; simp)
        fT (restrictHopfHom_base HG HT fT efT)
      twistedAction := by
        intro σ x
        exact (coordinateComparison_equivariant HG eG σ x).trans
          (congrArg (coordinateComparison HG eG).hom.hom (pinnedDatum_apply aG σ x)) }
  exact ⟨G, B, T, j, data, j_comm, rfl⟩

/-- The pinned lift preserves the pair, so all three Hopf algebras and
both subgroup inclusions descend by the same finite Galois action. -/
theorem pinnedPairDescent : Statement.{u} := by
  intro k K _ _ _ _ _ L P D l Q _ ω
  obtain ⟨G, B, T, j, data, hj, hω⟩ := effectivePair (P := P) l ω
  obtain ⟨hG, hB, hT, hm⟩ := descendGeometry (G := G) data
  exact ⟨⟨G, hG, B, T, hB, hT, hm, j, hj, data, hω⟩⟩

end PinnedPair

end

end LinearAlgebraicGroups.Descent.PinnedPairDescent
