import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots

open LinearAlgebraicGroups.Specs
open Specs.QuasiSplitOrbitDerivedRoots
open AbstractPairing (Root Datum IsAttachedCoroot)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots adjointWeightVectors pairing)
open RootGroups (IsRootSubgroup)
open Specs.GeometricRadicals (IsSplitTorus)
open CentralIsogenies (characterPullback)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open Pinning (AttachedDatum SplitBorelPair)
open RootGroups (rankOneWord rootPoint)
open SchemeDerivedGroup (IsCommutative IsSubgroupOf)
open StandardParabolicLevi (leviRoots)
open SubtorusCentralizer (IsCentralizer)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint)

open private centralizes_iff conjugateLe_iff mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private map_weightVector weightVector_of_map hom_commutes_with_weight_formula differential_injective
  differential_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private pairing_trivial torusWeightBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open private canonicalZero_eq from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private subgroupOf_of_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private character_restricts_trivially from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private isTorus_of_split pairing_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private contractingKilled postMul postInv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private torus_commutative from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private liftToSchemeKernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
open private cocharacter_ext_units from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private rankOneWord_comp rootPoint_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups
open private centralIsogeny_baseChange centralIsogeny_postIso isIso_of_scalarExtension
  splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private groupBaseChangeTowerIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private connectedOfGeometricallyConnected from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
open private split_of_torus from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
open private isTorus_iff_coordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint
open private sameSubgroupIso pairing_pushforward diagonalCharacterMap
  normalizerPoint_action finite_reflection_functionals reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private exists_weylIdentification from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
open private common_kernel powerMorphism_zero from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {P : SplitBorelPair k}

private theorem centralizer_le {G : GroupScheme k} {A B C E : ClosedSubgroup G}
    (hAB : IsSubgroupOf A B) (hC : IsCentralizer B C) (hE : IsCentralizer A E) :
    IsSubgroupOf C E := by
  obtain ⟨j, hj⟩ := hAB
  apply subgroupOf_of_sections
  apply (hE _ _).mp
  apply (centralizes_iff _ _).mpr
  intro Y y a
  have h := (centralizes_iff _ _).mp ((hC _ _).mpr ⟨𝟙 _, Category.id_comp _⟩) Y y
    (a ≫ j.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, hj] at h
  exact h

private theorem rankOneCentralizer_le {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (α : Root P.T)
    (hα : letI := D.comm; α ∈ leviRoots D.datum I)
    (C : RankOneFlag.Centralizer P.T α.val) :
    IsSubgroupOf C.subgroup S.levi := by
  letI := D.comm
  obtain ⟨j, hj⟩ := C.kernelTorus_largest.2.2 S.kernelTorus
    (isTorus_of_split S.kernel.1) (character_restricts_trivially (D := D.datum) S.kernel hα)
  apply centralizer_le _ C.centralizes S.centralizer
  exact ⟨j, by
    change j ≫ C.kernelTorus.inclusion ≫ P.T.inclusion =
      S.kernelTorus.inclusion ≫ P.T.inclusion
    rw [← Category.assoc, hj]⟩

private theorem rootPoint_comp_vanishing {A : RootGroups.AdditiveLine k} {G Q : GroupScheme k}
    {x : A.group ⟶ G} {q : G ⟶ Q} (h : x ≫ q = 0) (R : TestAlgebra k) (b : R) :
    rootPoint x R b ≫ q.hom.hom = 1 := by
  unfold rootPoint
  rw [Category.assoc, ← Grp.comp_hom_hom, h]
  exact MonObj.comp_one _

theorem faceCorootFactors : FaceCorootFactors.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro α hα
  obtain ⟨C, _, _, _, L, M, _, _, _, _, A, p, n, _, _, _, _, r, hr⟩ :=
    D.datum.attached α
  obtain ⟨v, hv⟩ := rankOneCentralizer_le S α hα C
  obtain ⟨Q, q, hq, _, hQt⟩ :=
    Reductive.CentralDerived.derivedTorusQuotient (closedSubgroupAlgebraicGroup S.levi)
      S.reductive S.derived S.isDerived
  letI := torus_commutative Q hQt
  have hQc : IsCommutative Q.val := fun _ _ _ => mul_comm _ _
  let τ := S.torusIso.hom ≫ S.leviTorus.inclusion
  let x := p.root.hom ≫ L.contracting.inclusion ≫ v
  let y := n.root.hom ≫ M.contracting.inclusion ≫ v
  have hx : x ≫ q = 0 := by
    dsimp only [x]
    rw [Category.assoc, Category.assoc,
      contractingKilled (G := closedSubgroupAlgebraicGroup C.subgroup)
        (v ≫ q) hQc L, comp_zero]
  have hy : y ≫ q = 0 := by
    dsimp only [y]
    rw [Category.assoc, Category.assoc,
      contractingKilled (G := closedSubgroupAlgebraicGroup C.subgroup)
        (v ≫ q) hQc M, comp_zero]
  haveI : Mono S.levi.inclusion.hom.hom := mono_over _ S.levi.isClosedImmersion
  have hw (R : TestAlgebra k) (b : Rˣ) :
      cocharacterPoint r.coroot R b ≫ τ.hom.hom =
        rankOneWord x y R b * (rankOneWord x y R 1)⁻¹ := by
    apply (cancel_mono S.levi.inclusion.hom.hom).mp
    have ht : (τ ≫ S.levi.inclusion).hom.hom = P.T.inclusion.hom.hom :=
      congrArg (fun f : P.T.group ⟶ P.G.val => f.hom.hom) S.torusInclusion
    have hv' : v.hom.hom ≫ S.levi.inclusion.hom.hom = C.subgroup.inclusion.hom.hom :=
      congrArg (fun f : C.subgroup.group ⟶ P.G.val => f.hom.hom) hv
    rw [Category.assoc, ← Grp.comp_hom_hom, ht, r.coroot_word, postMul, postInv]
    rw [← rankOneWord_comp, ← rankOneWord_comp]
    have hxp : x ≫ S.levi.inclusion =
        p.root.hom ≫ L.contracting.inclusion ≫ C.subgroup.inclusion := by
      simp only [x, Category.assoc, hv]
    have hyn : y ≫ S.levi.inclusion =
        n.root.hom ≫ M.contracting.inclusion ≫ C.subgroup.inclusion := by
      simp only [y, Category.assoc, hv]
    rw [hxp, hyn]
  have hkill : (r.coroot ≫ τ) ≫ q = 0 := by
    apply cocharacter_ext_units
    intro R b
    have hword (t : Rˣ) : rankOneWord x y R t ≫ q.hom.hom = 1 := by
      rw [rankOneWord, postMul, postMul, rootPoint_comp_vanishing hx,
        rootPoint_comp_vanishing hy, mul_one, mul_one]
    change ((cocharacterPoint r.coroot R b ≫ τ.hom.hom) ≫ q.hom.hom) =
      unitPoint R b ≫ (1 : _ ⟶ Q.val.X)
    rw [hw, postMul, postInv, hword, hword, inv_one, mul_one, MonObj.comp_one]
  obtain ⟨d, hd⟩ := liftToSchemeKernel hq (r.coroot ≫ τ) hkill
  have hcomp : r.coroot ≫ P.T.inclusion = d ≫ (S.derived.inclusion ≫ S.levi.inclusion) := by
    exact (congrArg (r.coroot ≫ ·) S.torusInclusion.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ S.levi.inclusion) hd.symm).trans (Category.assoc _ _ _)))
  exact ⟨S.intersection.lift r.coroot d hcomp,
    (S.intersection.lift_fst _ _ _).trans hr⟩

theorem faceRootSubgroupsFactor : FaceRootSubgroupsFactor.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro α hα U hU
  obtain ⟨C, _, _, _, L, _, _, _, _, _, _, _, _, hroot, _, _, _, _, _⟩ :=
    D.datum.attached α
  obtain ⟨v, hv⟩ := rankOneCentralizer_le S α hα C
  obtain ⟨Q, q, hq, _, hQt⟩ :=
    Reductive.CentralDerived.derivedTorusQuotient (closedSubgroupAlgebraicGroup S.levi)
      S.reductive S.derived S.isDerived
  letI := torus_commutative Q hQt
  have hQc : IsCommutative Q.val := fun _ _ _ => mul_comm _ _
  let f := L.contracting.inclusion ≫ v
  have hf : f ≫ q = 0 :=
    (Category.assoc _ _ _).trans
      (contractingKilled (G := closedSubgroupAlgebraicGroup C.subgroup)
        (v ≫ q) hQc L)
  obtain ⟨j, hj⟩ := liftToSchemeKernel hq f hf
  obtain ⟨_, _, _, _, _, _, huniq⟩ :=
    (RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 α.val α.property
  obtain ⟨e, he⟩ := sameSubgroupIso (huniq.2 U hU)
  obtain ⟨d, hd⟩ := sameSubgroupIso (huniq.2 _ hroot)
  refine ⟨e.inv ≫ d.hom ≫ j, ?_⟩
  change (e.inv ≫ d.hom ≫ j) ≫ S.derived.inclusion ≫ S.levi.inclusion = _
  simp only [Category.assoc, ← Category.assoc j S.derived.inclusion, hj, f]
  rw [hv]
  change e.inv ≫ d.hom ≫ (subgroupOfSubgroup C.subgroup L.contracting).inclusion = _
  rw [hd, ← he, Iso.inv_hom_id_assoc]

private theorem face_root_pairing {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (α β : Root P.T) (b : Cocharacter S.torus.group)
    (hb : letI := D.comm; b ≫ S.toAmbientTorus = (D.datum.rootDatum.coroot β).toMul) :
    letI := D.comm
    D.datum.rootDatum.pairing α β = pairing S.torus.group (S.toAmbientTorus ≫ α.val) b := by
  letI := D.comm
  change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root α) (D.datum.rootDatum.coroot β) = _
  rw [D.datum.root_eq]
  exact (D.datum.pairing_eq α.val (D.datum.rootDatum.coroot β).toMul).trans
    ((congrArg (pairing P.T.group α.val) hb.symm).trans
      (pairing_pushforward S.toAmbientTorus α.val b))

theorem faceRootRestrictionInjective : FaceRootRestrictionInjective.{u} := by
  intro k _ P D I S
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  intro α hα β hβ h
  obtain ⟨a, ha⟩ := faceCorootFactors D I S α hα
  obtain ⟨b, hb⟩ := faceCorootFactors D I S β hβ
  change S.toAmbientTorus ≫ α.val = S.toAmbientTorus ≫ β.val at h
  apply (D.datum.rootDatum.pairing_two_two_iff α β).mp
  constructor
  · calc
      _ = pairing S.torus.group (S.toAmbientTorus ≫ α.val) b := face_root_pairing S α β b hb
      _ = D.datum.rootDatum.pairing β β := by rw [h]; exact (face_root_pairing S β β b hb).symm
      _ = 2 := D.datum.rootDatum.pairing_same β
  · calc
      _ = pairing S.torus.group (S.toAmbientTorus ≫ β.val) a := face_root_pairing S β α a ha
      _ = D.datum.rootDatum.pairing α α := by rw [← h]; exact (face_root_pairing S α α a ha).symm
      _ = 2 := D.datum.rootDatum.pairing_same α

private theorem normalizes_restrict {G H A : GroupScheme k} (j : A ⟶ H) (f : H ⟶ G)
    [Mono f.hom.hom] (hj : IsClosedImmersion j.hom.hom.left)
    (hjf : IsClosedImmersion (j ≫ f).hom.hom.left) {Y Z : SchemeOver k}
    (t : Y ⟶ H.X) (a : Y ⟶ Z) (g : Z ⟶ G.X) (he : t ≫ f.hom.hom = a ≫ g)
    (hn : Normalizes (j ≫ f) g) : Normalizes j t := by
  have restrict (t' : Y ⟶ H.X) (g' : Z ⟶ G.X)
      (h : t' ≫ f.hom.hom = a ≫ g') (hn' : ConjugateLe (j ≫ f) g') :
      ConjugateLe j t' := by
    apply (conjugateLe_iff _ _).mpr
    intro R u v
    obtain ⟨w, hw⟩ := (conjugateLe_iff _ _).mp hn' R (u ≫ a) v
    refine ⟨w, (cancel_mono f.hom.hom).mp ?_⟩
    simp only [Grp.comp_hom_hom, Category.assoc] at hw
    simpa only [postMul f, postInv f, Category.assoc, h] using hw
  apply (LinearAlgebraicGroups.normalizesIff k j hj Y t).mpr
  obtain ⟨hp, hm⟩ := (LinearAlgebraicGroups.normalizesIff k (j ≫ f) hjf Z g).mp hn
  exact ⟨restrict t g he hp, restrict t⁻¹ g⁻¹ (by rw [postInv, he, GrpObj.comp_inv]) hm⟩

theorem faceRootRestrictions : FaceRootRestrictions.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro α hα
  let β := S.toAmbientTorus ≫ α.val
  have hT : S.torus.inclusion ≫ S.inclusion = S.toAmbientTorus ≫ P.T.inclusion :=
    S.intersection.w.symm
  have hClosed : IsClosedImmersion S.inclusion.hom.hom.left := by
    change IsClosedImmersion (S.derived.inclusion.hom.hom.left ≫ S.levi.inclusion.hom.hom.left)
    letI := S.derived.isClosedImmersion
    letI := S.levi.isClosedImmersion
    infer_instance
  letI : Mono S.inclusion.hom.hom := mono_over _ hClosed
  have restrict (U : ClosedSubgroup P.G.val) (hU : IsRootSubgroup P.T U α.val) :
      ∃ V : ClosedSubgroup S.group.val, IsRootSubgroup S.torus V β ∧
        ∃ e : V.group ≅ U.group, e.hom ≫ U.inclusion = V.inclusion ≫ S.inclusion := by
    obtain ⟨j, hj⟩ := faceRootSubgroupsFactor D I S α hα U hU
    letI := hClosed
    letI : IsClosedImmersion (j.hom.hom.left ≫ S.inclusion.hom.hom.left) := by
      change IsClosedImmersion (j ≫ S.inclusion).hom.hom.left
      rw [hj]
      exact U.isClosedImmersion
    have hc : IsClosedImmersion j.hom.hom.left :=
      IsClosedImmersion.of_comp_isClosedImmersion _ S.inclusion.hom.hom.left
    let V : ClosedSubgroup S.group.val := ⟨U.group, j, hc⟩
    refine ⟨V, ⟨hU.1, hU.2.1, ?_, ?_⟩, Iso.refl _, ?_⟩
    · apply normalizes_restrict j S.inclusion hc (hj.symm ▸ U.isClosedImmersion)
        S.torus.inclusion.hom.hom S.toAmbientTorus.hom.hom P.T.inclusion.hom.hom
      · exact congrArg (fun f : S.torus.group ⟶ P.G.val => f.hom.hom) hT
      · rw [hj]
        exact hU.2.2.1
    · rintro _ ⟨v, rfl⟩
      apply weightVector_of_map S.inclusion S.toAmbientTorus hT
      change mapPointKernel S.inclusion (mapPointKernel j v) ∈ adjointWeightVectors P.T α.val
      rw [← differential_comp, hj]
      exact hU.2.2.2 ⟨v, rfl⟩
    · simpa only [Iso.refl_hom, Category.id_comp] using hj.symm
  have hβ₀ : β ≠ 1 := by
    obtain ⟨c, hc⟩ := faceCorootFactors D I S α hα
    have h := (face_root_pairing S α α c hc).symm.trans (D.datum.rootDatum.pairing_same α)
    intro hβ
    change β = 1 at hβ
    change pairing S.torus.group β c = 2 at h
    rw [hβ] at h
    rw [pairing_trivial] at h
    omega
  obtain ⟨_, _, U, hU, _, hImage, _, _⟩ :=
    (RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 α.val α.property
  obtain ⟨V, hV, e, he⟩ := restrict U hU
  obtain ⟨v, hv, hv₀⟩ := α.property.2
  obtain ⟨w, hw⟩ := hImage.symm ▸ hv
  let z := mapPointKernel V.inclusion (mapPointKernel e.inv w)
  have hz : mapPointKernel S.inclusion z = v := by
    dsimp only [z]
    rw [← differential_comp, ← differential_comp, ← he, Iso.inv_hom_id_assoc]
    exact hw
  have hz₀ : z ≠ 0 := by
    intro h
    exact hv₀ (hz.symm.trans (by rw [h, map_zero]))
  exact ⟨⟨hβ₀, z, hV.2.2.2 ⟨_, rfl⟩, hz₀⟩, fun U hU => by
    obtain ⟨V, hV, e, he⟩ := restrict U hU
    exact ⟨V, hV, e, he⟩⟩

theorem faceRootRestrictionSurjective : FaceRootRestrictionSurjective.{u} := by
  classical
  intro k _ P D I S
  letI := D.comm
  intro β hβ
  let L := closedSubgroupAlgebraicGroup S.levi
  let T := S.leviTorus
  let V : ClosedSubgroup L.val := subgroupOfSubgroup S.derived S.torus
  have hT : V.inclusion = (S.toAmbientTorus ≫ S.torusIso.hom) ≫ T.inclusion := by
    letI : Mono S.levi.inclusion :=
      (Grp.forget (SchemeOver k)).mono_of_mono_map
        (mono_over _ S.levi.isClosedImmersion)
    apply (cancel_mono S.levi.inclusion).mp
    change (S.torus.inclusion ≫ S.derived.inclusion) ≫ S.levi.inclusion = _
    simp only [Category.assoc]
    rw [S.torusInclusion]
    exact S.intersection.w.symm
  have htSplit : GeometricRadicals.IsSplitTorus T.group := by
    obtain ⟨n, ⟨e⟩⟩ := P.split
    exact ⟨n, ⟨S.torusIso.symm.trans e⟩⟩
  obtain ⟨v, hv, hv₀⟩ := hβ.2
  let w := mapPointKernel S.derived.inclusion v
  have hw : w ∈ adjointWeightVectors V β := by
    apply map_weightVector S.derived.inclusion (Iso.refl _)
    · change S.torus.inclusion ≫ S.derived.inclusion = (𝟙 _) ≫ V.inclusion
      rw [Category.id_comp]
      rfl
    · simpa only [Iso.refl_hom, Category.id_comp] using hv
  have hw₀ : w ≠ 0 := by
    letI : Mono S.derived.inclusion.hom.hom := mono_over _ S.derived.isClosedImmersion
    intro h
    apply hv₀
    exact differential_injective S.derived.inclusion (h.trans (map_zero _).symm)
  let s := identityLieStructure L
  letI := s.lieRing
  letI := s.lieAlgebra
  obtain ⟨J, hJ, b, χ, hb, _⟩ := torusWeightBasis L T htSplit s
  obtain ⟨K, hK, d, ψ, _, hd⟩ := torusWeightBasis L V S.torusSplit s
  letI := hJ
  letI := hK
  let w' : Specs.Lie k L.val := w
  have hne : w' ≠ 0 := by
    intro h
    exact hw₀ (h.trans (canonicalZero_eq s))
  obtain ⟨l, hl⟩ : ∃ l, d.equivFun w' l ≠ 0 := by
    by_contra! h
    apply hne
    apply d.equivFun.injective
    ext l
    change d.equivFun w' l = d.equivFun (0 : Specs.Lie k L.val) l
    rw [h l, LinearEquiv.map_zero]
    rfl
  have hψ : ψ l = β := by
    by_contra h
    exact hl (hd β w' hw l h)
  let a : V.group ⟶ T.group := S.toAmbientTorus ≫ S.torusIso.hom
  have hweights (j : J) : b j ∈ adjointWeightVectors V (a ≫ χ j) := by
    apply weightVector_of_map (𝟙 L.val) a
    · rw [Category.comp_id]
      exact hT
    · rw [(lieFunctoriality k).2.1]
      exact hb j
  obtain ⟨j, hj⟩ : ∃ j, a ≫ χ j = β := by
    by_contra! h
    let p := (LinearMap.proj l).comp d.equivFun.toLinearMap
    have hp : p = 0 := by
      apply b.ext
      intro j
      change d.equivFun (b j) l = 0
      exact hd (a ≫ χ j) (b j) (hweights j) l (hψ ▸ Ne.symm (h j))
    exact hl (DFunLike.congr_fun hp w')
  have hχ : χ j ∈ absoluteRoots T := by
    refine ⟨?_, b j, hb j, ?_⟩
    · intro h
      apply hβ.1
      rw [← hj, h]
      apply Grp.hom_ext
      exact MonObj.comp_one _
    · intro h
      exact b.ne_zero j (h.trans (canonicalZero_eq s).symm)
  obtain ⟨α, hα, harg⟩ := S.leviRoots_eq ▸ hχ
  refine ⟨α, hα, ?_⟩
  change S.torusIso.inv ≫ α.val = χ j at harg
  rw [← hj, ← harg]
  change S.toAmbientTorus ≫ α.val = (S.toAmbientTorus ≫ S.torusIso.hom) ≫ _
  rw [Category.assoc, Iso.hom_inv_id_assoc]

private theorem rankOneRepresentative_factors {G H : GroupScheme k}
    (f : H ⟶ G) {A : RootGroups.AdditiveLine k} {x y : A.group ⟶ G}
    {x' y' : A.group ⟶ H} (hx : x' ≫ f = x) (hy : y' ≫ f = y)
    (T : ClosedSubgroup G) (α : Character T.group)
    (r : RootGroups.CorootReflection T α x y) :
    ∃ g : 𝟙_ (SchemeOver k) ⟶ H.X, g ≫ f.hom.hom = r.representative := by
  let R := CommAlgCat.of k k
  let Z := (testSpec k).obj (Opposite.op R)
  let e : Z ≅ 𝟙_ (SchemeOver k) :=
    (affineBaseTerminal k).uniqueUpToIso isTerminalTensorUnit
  have he : e.hom = toUnit Z := Subsingleton.elim _ _
  refine ⟨e.inv ≫ rankOneWord x' y' R 1, ?_⟩
  apply (cancel_epi e.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← rankOneWord_comp, hx, hy, he]
  exact (r.representative_word).symm

private theorem normalizes_pullback {G H : GroupScheme k} {T : ClosedSubgroup G}
    {V : ClosedSubgroup H} {a : V.group ⟶ T.group} {f : H ⟶ G}
    (hp : IsPullback a V.inclusion T.inclusion f) {Y : SchemeOver k} (g : Y ⟶ H.X)
    (hg : Normalizes T.inclusion (g ≫ f.hom.hom)) :
    Normalizes V.inclusion g := by
  let F := Grp.forget (SchemeOver k)
  have h := hp.map F
  have hle (n : Y ⟶ H.X) (hn : ConjugateLe T.inclusion (n ≫ f.hom.hom)) :
      ConjugateLe V.inclusion n := by
    apply (conjugateLe_iff _ _).mpr
    intro Z u v
    obtain ⟨t, ht⟩ := (conjugateLe_iff _ _).mp hn Z u (v ≫ a.hom.hom)
    let w := (u ≫ n) * (v ≫ V.inclusion.hom.hom) * (u ≫ n)⁻¹
    have htw : t ≫ T.inclusion.hom.hom = w ≫ f.hom.hom := by
      have hi := F.congr_map hp.w
      change a.hom.hom ≫ T.inclusion.hom.hom = V.inclusion.hom.hom ≫ f.hom.hom at hi
      rw [ht]
      simp only [w, postMul f, postInv f, Category.assoc, hi]
    exact ⟨h.lift t w htw, h.lift_snd _ _ _⟩
  obtain ⟨h₁, h₂⟩ := (LinearAlgebraicGroups.normalizesIff k T.inclusion
    T.isClosedImmersion Y (g ≫ f.hom.hom)).mp hg
  exact (LinearAlgebraicGroups.normalizesIff k V.inclusion V.isClosedImmersion Y g).mpr
    ⟨hle g h₁, hle g⁻¹ (by rw [postInv]; exact h₂)⟩

private theorem splitCharacterRestriction_surjective {G H : AffineAlgebraicGroup k}
    (hG : GeometricRadicals.IsReductive G) (hH : GeometricRadicals.IsReductive H)
    (T : ClosedSubgroup G.val) (V : ClosedSubgroup H.val)
    (ht : IsSplitTorus T.group) (hmt : RankOneFlag.IsGeometricallyMaximal T)
    (hv : IsSplitTorus V.group) (hmv : RankOneFlag.IsGeometricallyMaximal V)
    (a : V.group ⟶ T.group) (ha : IsClosedImmersion a.hom.hom.left) :
    Function.Surjective (characterPullback a) := by
  obtain ⟨_, e, he, _, _, _⟩ := RootData.SchemeCentre.schemeCentre G hG T ht hmt
  obtain ⟨_, d, hd, _, _, _⟩ := RootData.SchemeCentre.schemeCentre H hH V hv hmv
  have hc := diagonalCharacterMap a d e hd he
  let p := groupAlgebraMap k (characterPullback a)
  have hp : specGroupMap p = d.hom ≫ a ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc.symm
  have hsurj := (hopfMapClosedImmersion k p).mp (by
    rw [hp]
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget _
    change IsClosedImmersion (F.map (d.hom ≫ a ≫ e.inv))
    letI : IsIso (F.map d.hom) := F.map_isIso _
    letI : IsIso (F.map e.inv) := F.map_isIso _
    letI : IsClosedImmersion (F.map a) := ha
    simp only [Functor.map_comp]
    infer_instance)
  intro χ
  obtain ⟨b, hb⟩ := hsurj (MonoidAlgebra.single χ 1)
  apply Finsupp.mem_range_of_mapDomain_ne_zero (x := b.coeff)
  have hc := congrArg (fun x : MonoidAlgebra k (Character V.group) => x.coeff χ) hb
  change (Finsupp.mapDomain (characterPullback a) b.coeff) χ =
    (MonoidAlgebra.single χ 1 : MonoidAlgebra k (Character V.group)).coeff χ at hc
  rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hc
  rw [hc]
  exact one_ne_zero

private theorem contracting_factors_derived {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) {C : ClosedSubgroup P.G.val}
    (j : C.group ⟶ S.levi.group) (hj : j ≫ S.levi.inclusion = C.inclusion)
    {u : Cocharacter C.group} (L : CocharacterDynamics.LimitDecomposition u) :
    ∃ l : L.contracting.group ⟶ S.group.val,
      l ≫ S.inclusion = L.contracting.inclusion ≫ C.inclusion := by
  obtain ⟨Q, q, hq, _, hQt⟩ :=
    Reductive.CentralDerived.derivedTorusQuotient (closedSubgroupAlgebraicGroup S.levi)
      S.reductive S.derived S.isDerived
  letI := torus_commutative Q hQt
  have hQ : IsCommutative Q.val := fun _ _ _ => mul_comm _ _
  have h : (L.contracting.inclusion ≫ j) ≫ q = 0 :=
    (Category.assoc _ _ _).trans
      (contractingKilled (G := closedSubgroupAlgebraicGroup C) (j ≫ q) hQ L)
  obtain ⟨l, hl⟩ := liftToSchemeKernel hq (L.contracting.inclusion ≫ j) h
  refine ⟨l, ?_⟩
  change l ≫ S.derived.inclusion ≫ S.levi.inclusion = L.contracting.inclusion ≫ C.inclusion
  rw [← Category.assoc l, hl, Category.assoc, hj]

private theorem attachedReflection_point_lift {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (α : Root P.T)
    (hα : letI := D.comm; α ∈ leviRoots D.datum I) :
    letI := D.comm
    ∃ (A : RootGroups.AdditiveLine k) (x y : A.group ⟶ P.G.val)
      (r : RootGroups.CorootReflection P.T α.val x y)
      (g : 𝟙_ (SchemeOver k) ⟶ S.group.val.X),
      r.coroot = (D.datum.rootDatum.coroot α).toMul ∧
      g ≫ S.inclusion.hom.hom = r.representative := by
  letI := D.comm
  obtain ⟨C, _, _, _, L, M, _, _, _, _, A, p, n, _, _, _, _, r, hr⟩ :=
    D.datum.attached α
  obtain ⟨j, hj⟩ := rankOneCentralizer_le S α hα C
  obtain ⟨l, hl⟩ := contracting_factors_derived S j hj L
  obtain ⟨m, hm⟩ := contracting_factors_derived S j hj M
  let x' : A.group ⟶ S.group.val := p.root.hom ≫ l
  let y' : A.group ⟶ S.group.val := n.root.hom ≫ m
  let x : A.group ⟶ P.G.val := p.root.hom ≫ L.contracting.inclusion ≫ C.subgroup.inclusion
  let y : A.group ⟶ P.G.val := n.root.hom ≫ M.contracting.inclusion ≫ C.subgroup.inclusion
  have hx : x' ≫ S.inclusion = x :=
    (Category.assoc _ _ _).trans (congrArg (p.root.hom ≫ ·) hl)
  have hy : y' ≫ S.inclusion = y :=
    (Category.assoc _ _ _).trans (congrArg (n.root.hom ≫ ·) hm)
  obtain ⟨g, hg⟩ := rankOneRepresentative_factors S.inclusion
    (A := A) (x := x) (y := y) (x' := x') (y' := y') hx hy P.T α.val r
  exact ⟨A, x, y, r, g, hr, hg⟩

set_option maxHeartbeats 1000000 in
private theorem coroot_restricts_with_representative
    {G H : AffineAlgebraicGroup k} (hG : Specs.GeometricRadicals.IsReductive G)
    (hH : Specs.GeometricRadicals.IsReductive H)
    (T : ClosedSubgroup G.val) (V : ClosedSubgroup H.val)
    (ht : IsSplitTorus T.group) (hmt : RankOneFlag.IsGeometricallyMaximal T)
    (hv : IsSplitTorus V.group) (hmv : RankOneFlag.IsGeometricallyMaximal V)
    (f : H.val ⟶ G.val) (i : V.group ⟶ T.group)
    (hClosed : IsClosedImmersion f.hom.hom.left)
    (hp : IsPullback i V.inclusion T.inclusion f)
    (α : Character T.group) (hβ : i ≫ α ≠ 1)
    {A B : RootGroups.AdditiveLine k} {x y : A.group ⟶ G.val} {u v : B.group ⟶ H.val}
    (r : RootGroups.CorootReflection T α x y) (s : RootGroups.CorootReflection V (i ≫ α) u v)
    (g : 𝟙_ (SchemeOver k) ⟶ H.val.X) (hg : g ≫ f.hom.hom = r.representative)
    (d : Cocharacter V.group) (hd : d ≫ i = r.coroot) :
    s.coroot = d := by
  have hn : Normalizes V.inclusion g :=
    normalizes_pullback hp g (by rw [hg]; exact r.normalizes)
  obtain ⟨N, _, _, W, q, hN, _, _, _, _, _, hW⟩ :=
    Reductive.WeylScheme.weylScheme H hH V (isTorus_of_split hv) hmv
  obtain ⟨⟨Weyl⟩, _⟩ := hW hv
  obtain ⟨a, ha⟩ := normalizerPoint_action (G := H) V hN Weyl g hn
  obtain ⟨b, hb⟩ := normalizerPoint_action (G := H) V hN Weyl s.representative s.normalizes
  let forget := Grp.forget (SchemeOver k)
  have hin := forget.congr_map hp.w
  change i.hom.hom ≫ T.inclusion.hom.hom = V.inclusion.hom.hom ≫ f.hom.hom at hin
  haveI : Mono T.inclusion.hom.hom := mono_over _ T.isClosedImmersion
  haveI : Mono V.inclusion.hom.hom := mono_over _ V.isClosedImmersion
  have hconj : (Weyl.conjugation a).hom ≫ i = i ≫ r.conjugation.hom := by
    apply Grp.hom_ext
    apply (cancel_mono T.inclusion.hom.hom).mp
    change ((Weyl.conjugation a).hom.hom.hom ≫ i.hom.hom) ≫ T.inclusion.hom.hom =
      (i.hom.hom ≫ r.conjugation.hom.hom.hom) ≫ T.inclusion.hom.hom
    simp only [Category.assoc, hin]
    rw [← Category.assoc, ha]
    have hc : r.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom =
        (toUnit T.group.X ≫ r.representative) * T.inclusion.hom.hom *
          (toUnit T.group.X ≫ r.representative)⁻¹ := r.conjugates
    rw [hc]
    simp only [postMul f, postInv f, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc,
      comp_toUnit_assoc, hg, hin]
  have hconjInv : (Weyl.conjugation a).inv ≫ i = i ≫ r.conjugation.inv := by
    rw [← cancel_mono r.conjugation.hom, Category.assoc, ← hconj, Iso.inv_hom_id_assoc,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hbEq : (Weyl.conjugation b).hom = s.conjugation.hom := by
    apply Grp.hom_ext
    apply (cancel_mono V.inclusion.hom.hom).mp
    exact hb.trans s.conjugates.symm
  have hbInv : (Weyl.conjugation b).inv = s.conjugation.inv :=
    congrArg Iso.inv (Iso.ext hbEq)
  have hiClosed : IsClosedImmersion i.hom.hom.left :=
    MorphismProperty.of_isPullback (hp.map (forget ⋙ Over.forget _)).flip hClosed
  have hchars := splitCharacterRestriction_surjective hG hH T V ht hmt hv hmv i hiClosed
  have ha' (χ : Character V.group) : a.val χ = χ * (i ≫ α) ^ (-pairing V.group χ d) := by
    obtain ⟨ψ, rfl⟩ := hchars χ
    rw [Weyl.characterAction]
    change (Weyl.conjugation a).inv ≫ i ≫ ψ =
      characterPullback i ψ * characterPullback i α ^
        (-pairing V.group (characterPullback i ψ) d)
    rw [← Category.assoc, hconjInv, Category.assoc, r.reflection, ← pairing_pushforward, hd]
    change characterPullback i (ψ * α ^ (-pairing T.group ψ r.coroot)) = _
    rw [map_mul, map_zpow]
  have hb' (χ : Character V.group) : b.val χ = χ * (i ≫ α) ^ (-pairing V.group χ s.coroot) := by
    rw [Weyl.characterAction, hbInv, s.reflection]
  obtain ⟨hcomm, hfree, _, _, _, B, hB, hP⟩ :=
    RootData.CharacterPairing.perfectCharacterPairing V.group hv
  letI := hcomm
  letI := hfree
  letI := Weyl.finite
  have h₁ : B (Additive.ofMul (i ≫ α)) (Additive.ofMul d) = 2 := by
    rw [hP]
    change pairing V.group (characterPullback i α) d = 2
    rw [← pairing_pushforward, hd]
    exact r.root_pairing
  have h₂ : B (Additive.ofMul (i ≫ α)) (Additive.ofMul s.coroot) = 2 :=
    (hP _ _).trans s.root_pairing
  have hfunc := finite_reflection_functionals Weyl.labels a b (i ≫ α) hβ
    (B.flip (Additive.ofMul d)) (B.flip (Additive.ofMul s.coroot)) h₁ h₂
    (fun χ => by rw [ha', LinearMap.flip_apply, hP])
    (fun χ => by rw [hb', LinearMap.flip_apply, hP])
  exact congrArg Additive.toMul (hB.bijective_right.injective hfunc.symm)

set_option maxHeartbeats 600000 in
theorem faceAttachedCoroots : FaceAttachedCoroots.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro α hα hβ c hc
  obtain ⟨d, hd⟩ := faceCorootFactors D I S α hα
  obtain ⟨A, x, y, r, g, hr, hg⟩ := attachedReflection_point_lift S α hα
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s, hs⟩ := hc
  have hss := Reductive.CentralDerived.derivedSemisimple (closedSubgroupAlgebraicGroup S.levi)
    S.reductive S.derived S.isDerived
  have hred := reductive_of_semisimple S.group hss
  have hClosed : IsClosedImmersion S.inclusion.hom.hom.left := by
    change IsClosedImmersion (S.derived.inclusion.hom.hom.left ≫ S.levi.inclusion.hom.hom.left)
    letI := S.derived.isClosedImmersion
    letI := S.levi.isClosedImmersion
    infer_instance
  have heq := coroot_restricts_with_representative (G := P.G) (H := S.group) P.reductive hred
    P.T S.torus P.split P.maximal S.torusSplit S.torusMaximal S.inclusion S.toAmbientTorus
    hClosed S.intersection α.val hβ.1 r s g hg d (hd.trans hr.symm)
  exact (congrArg (· ≫ S.toAmbientTorus) (hs.symm.trans heq)).trans hd

/-- Cocharacter composition with the specified inclusion on integral lattices. -/
private def pushCocharacters {T V : GroupScheme k} [IsCommMonObj T.X] [IsCommMonObj V.X]
    (i : V ⟶ T) : Additive (Cocharacter V) →ₗ[ℤ] Additive (Cocharacter T) :=
  (show Cocharacter V →* Cocharacter T from {
    toFun c := c ≫ i
    map_one' := Grp.hom_ext _ _ (MonObj.one_comp i.hom.hom)
    map_mul' c d := Grp.hom_ext _ _ (MonObj.mul_comp c.hom.hom d.hom.hom i.hom.hom)
  }).toAdditive.toIntLinearMap

theorem splitDerivedSimplyConnected : SplitDerivedSimplyConnected.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro hSpan
  have hss := Reductive.CentralDerived.derivedSemisimple (closedSubgroupAlgebraicGroup S.levi)
    S.reductive S.derived S.isDerived
  obtain ⟨hComm, ⟨E⟩⟩ := RootData.AbstractPairing.abstractPairing S.group
    (reductive_of_semisimple S.group hss) S.torus S.torusSplit S.torusMaximal
  letI := hComm
  let f := pushCocharacters S.toAmbientTorus
  have hClosed : IsClosedImmersion S.inclusion.hom.hom.left := by
    change IsClosedImmersion (S.derived.inclusion.hom.hom.left ≫ S.levi.inclusion.hom.hom.left)
    letI := S.derived.isClosedImmersion
    letI := S.levi.isClosedImmersion
    infer_instance
  have hfClosed : IsClosedImmersion S.toAmbientTorus.hom.hom.left :=
    MorphismProperty.of_isPullback
      (S.intersection.map (Grp.forget (SchemeOver k) ⋙ Over.forget _)).flip hClosed
  letI : Mono S.toAmbientTorus :=
    (Grp.forget (SchemeOver k)).mono_of_mono_map (mono_over _ hfClosed)
  have hf : Function.Injective f := by
    intro x y h
    exact Additive.toMul.injective ((cancel_mono S.toAmbientTorus).mp
      (congrArg Additive.toMul h))
  apply (Classification.SimplyConnectedLattice.latticeCriterion S.group hss
    S.torus S.torusSplit S.torusMaximal E).mpr
  apply top_le_iff.mp
  intro x _
  let M := SimplyConnectedLattice.corootLatticeOf E
  have hx : f x ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I) :=
    (hSpan (f x)).mp ⟨x.toMul, rfl⟩
  have hLe : Submodule.span ℤ (D.datum.rootDatum.coroot '' I) ≤ M.map f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    have hα' : α ∈ leviRoots D.datum I := Submodule.subset_span ⟨α, hα, rfl⟩
    have hβ := (faceRootRestrictions D I S α hα').1
    let β : Root (G := S.group) S.torus := ⟨S.toAmbientTorus ≫ α.val, hβ⟩
    refine ⟨E.rootDatum.coroot β, Submodule.subset_span ⟨β, rfl⟩, ?_⟩
    apply Additive.toMul.injective
    exact faceAttachedCoroots D I S α hα' hβ _ (E.attached β)
  obtain ⟨y, hy, hyx⟩ := hLe hx
  exact (hf hyx) ▸ hy

private theorem restrictRootCoordinate {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (α : Root P.T) (U : ClosedSubgroup P.G.val)
    (V : ClosedSubgroup S.group.val) (e : V.group ≅ U.group)
    (he : e.hom ≫ U.inclusion = V.inclusion ≫ S.inclusion)
    {A : RootGroups.AdditiveLine k} (x : Pinning.RootCoordinate A P.T U α.val) :
    ∃ y : Pinning.RootCoordinate A S.torus V (S.toAmbientTorus ≫ α.val),
      y.val.hom ≫ V.inclusion ≫ S.inclusion = x.val.hom ≫ U.inclusion := by
  let z := x.val ≪≫ e.symm
  have hmark : z.hom ≫ V.inclusion ≫ S.inclusion = x.val.hom ≫ U.inclusion := by
    change (x.val.hom ≫ e.inv) ≫ V.inclusion ≫ S.inclusion = _
    simp only [Category.assoc, ← he, Iso.inv_hom_id_assoc]
  refine ⟨⟨z, ?_⟩, hmark⟩
  have hT := (Grp.forget (SchemeOver k)).congr_map S.intersection.w
  change S.toAmbientTorus.hom.hom ≫ P.T.inclusion.hom.hom =
    S.torus.inclusion.hom.hom ≫ S.inclusion.hom.hom at hT
  have hClosed : IsClosedImmersion S.inclusion.hom.hom.left := by
    change IsClosedImmersion (S.derived.inclusion.hom.hom.left ≫ S.levi.inclusion.hom.hom.left)
    letI := S.derived.isClosedImmersion
    letI := S.levi.isClosedImmersion
    infer_instance
  letI : Mono S.inclusion.hom.hom := mono_over _ hClosed
  intro R t u
  dsimp only
  apply (cancel_mono S.inclusion.hom.hom).mp
  rw [postMul, postMul, postInv]
  have hg : (t ≫ S.torus.inclusion.hom.hom) ≫ S.inclusion.hom.hom =
    (t ≫ S.toAmbientTorus.hom.hom) ≫ P.T.inclusion.hom.hom := by
    simp only [Category.assoc, hT]
  simp only [hg, ← rootPoint_comp, Category.assoc, hmark]
  exact x.property R (t ≫ S.toAmbientTorus.hom.hom) u

theorem facePinCoordinates : FacePinCoordinates.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro α hα U A hU x
  obtain ⟨V, hV, e, he⟩ := (faceRootRestrictions D I S α hα).2 U hU
  obtain ⟨y, hy⟩ := restrictRootCoordinate S α U V e he x
  exact ⟨V, y, hV, hy⟩

private theorem rootSubgroup_lieImage {H : AffineAlgebraicGroup k}
    (hH : Specs.GeometricRadicals.IsReductive H) (T : ClosedSubgroup H.val)
    (hs : IsSplitTorus T.group) (hm : RankOneFlag.IsGeometricallyMaximal T)
    (χ : Character T.group) (hχ : χ ∈ absoluteRoots T)
    (U : ClosedSubgroup H.val) (hU : IsRootSubgroup T U χ) :
    Set.range (mapPointKernel U.inclusion) = adjointWeightVectors T χ := by
  obtain ⟨_, _, V, _, _, hV, _, huniq⟩ :=
    (RootData.RootGroups.rootSubgroups H hH T hs hm).2 χ hχ
  obtain ⟨e, he⟩ := sameSubgroupIso (huniq U hU)
  apply Set.Subset.antisymm hU.2.2.2
  rintro v hv
  obtain ⟨w, rfl⟩ := hV.symm ▸ hv
  exact ⟨mapPointKernel e.hom w, (differential_comp _ _ _).symm.trans
    (congrArg (fun f => mapPointKernel f w) he)⟩

theorem faceBorelRoots : FaceBorelRoots.{u} := by
  intro k _ P D I S
  letI := D.comm
  intro B B' j hp α hα hβ
  let β := S.toAmbientTorus ≫ α.val
  obtain ⟨_, _, U, hU, _, hImage, _, _⟩ :=
    (RootData.RootGroups.rootSubgroups P.G P.reductive P.T P.split P.maximal).2 α.val α.property
  obtain ⟨V, hV, e, he⟩ := (faceRootRestrictions D I S α hα).2 U hU
  have hss := Reductive.CentralDerived.derivedSemisimple (closedSubgroupAlgebraicGroup S.levi)
    S.reductive S.derived S.isDerived
  have hvImage := rootSubgroup_lieImage (reductive_of_semisimple S.group hss) S.torus
    S.torusSplit S.torusMaximal β hβ V hV
  change adjointWeightVectors S.torus β ⊆ Set.range (mapPointKernel B'.inclusion) ↔
    adjointWeightVectors P.T α.val ⊆ Set.range (mapPointKernel B.inclusion)
  rw [← hvImage, ← hImage]
  constructor
  · rintro h _ ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := h (show mapPointKernel V.inclusion (mapPointKernel e.inv v) ∈
        Set.range (mapPointKernel V.inclusion) from ⟨_, rfl⟩)
    refine ⟨mapPointKernel j w, ?_⟩
    rw [← differential_comp, hp.w, differential_comp, hw, ← differential_comp,
      ← differential_comp, ← he, Iso.inv_hom_id_assoc]
  · rintro h _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := h (show mapPointKernel U.inclusion (mapPointKernel e.hom w) ∈
        Set.range (mapPointKernel U.inclusion) from ⟨_, rfl⟩)
    have hComp : mapPointKernel B.inclusion v =
        mapPointKernel S.inclusion (mapPointKernel V.inclusion w) := by
      rw [hv, ← differential_comp, he, differential_comp]
    obtain ⟨z, hz, _⟩ := liePullbackComparison k hp v (mapPointKernel V.inclusion w) hComp
    exact ⟨z, hz.2⟩

section FaceLattice

open RootPairing

/-- Averaging over the face Weyl group gives the component annihilated by the face
roots, with an integral difference in the face coroot lattice. -/
private theorem average_coreflections {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (Q : RootPairing J ℤ X Y) [Finite Q.weylGroup] (I : Set J) (y : Y) :
    ∃ (n : ℕ) (z : Y), 0 < n ∧ (∀ α ∈ I, Q.root' α z = 0) ∧
      n • y - z ∈ Submodule.span ℤ (Q.coroot '' I) := by
  classical
  let W := Subgroup.closure (weylGroup.ofIdx Q '' I)
  let M := Submodule.span ℤ (Q.coroot '' I)
  letI : Fintype W := Fintype.ofFinite _
  let z := ∑ w : W, w.val.val.coweightEquiv y
  have hdiff {w : Q.weylGroup} (hw : w ∈ W) :
      ∀ v, w.val.coweightEquiv v - v ∈ M := by
    refine Subgroup.closure_induction
      (p := fun w _ => ∀ v, w.val.coweightEquiv v - v ∈ M) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨i, hi, rfl⟩ v
      change (Equiv.reflection Q i).coweightEquiv v - v ∈ M
      rw [Equiv.reflection_coweightEquiv, coreflection_apply]
      simpa only [sub_sub_cancel_left] using
        M.neg_mem (M.smul_mem (Q.root' i v) (Submodule.subset_span ⟨i, hi, rfl⟩))
    · intro v
      change v - v ∈ M
      simp
    · intro x w _ _ hx hw v
      change w.val.coweightEquiv (x.val.coweightEquiv v) - v ∈ M
      convert M.add_mem (hw (x.val.coweightEquiv v)) (hx v) using 1
      abel
    · intro w _ hw v
      change w.val.coweightEquiv.symm v - v ∈ M
      have h := hw (w.val.coweightEquiv.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      simpa only [neg_sub] using M.neg_mem h
  refine ⟨Fintype.card W, z, Fintype.card_pos, ?_, ?_⟩
  · intro i hi
    let s : W := ⟨weylGroup.ofIdx Q i, Subgroup.subset_closure ⟨i, hi, rfl⟩⟩
    have h := _root_.Equiv.sum_comp (_root_.Equiv.mulRight s) (fun w : W => w.val.val.coweightEquiv y)
    have hfix : Q.coreflection i z = z := by
      rw [show z = ∑ w : W, w.val.val.coweightEquiv y from rfl, map_sum]
      refine (Finset.sum_congr rfl ?_).trans h
      intro w _
      change Q.coreflection i (w.val.val.coweightEquiv y) =
        (Equiv.reflection Q i).coweightEquiv (w.val.val.coweightEquiv y)
      rw [Equiv.reflection_coweightEquiv]
    rw [coreflection_apply, sub_eq_self] at hfix
    have he := congrArg (Q.root' i) hfix
    rw [map_smul, show Q.root' i (Q.coroot i) = 2 from Q.root_coroot_two i, map_zero,
      smul_eq_mul] at he
    change Q.root' i z = 0
    omega
  · change Fintype.card W • y - z ∈ M
    have hs : (∑ w : W, (y - w.val.val.coweightEquiv y)) ∈ M :=
      M.sum_mem fun w _ => by simpa only [neg_sub] using M.neg_mem (hdiff w.property y)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← show
      z = ∑ w : W, w.val.val.coweightEquiv y from rfl] using hs

private theorem face_cocharacter_multiple (D : AttachedDatum P) (I : Set (Root P.T))
    (c : Cocharacter P.T.group) :
    letI := D.comm
    ∃ (n : ℕ) (z : Additive (Cocharacter P.T.group)), 0 < n ∧
      (∀ α ∈ I, D.datum.rootDatum.root' α z = 0) ∧
      n • Additive.ofMul c - z ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I) := by
  letI := D.comm
  obtain ⟨W⟩ := exists_weylIdentification P D
  letI := W.image.finite
  letI : Finite D.datum.rootDatum.weylGroup := Finite.of_injective _ W.labelEquiv.injective
  exact average_coreflections D.datum.rootDatum I (Additive.ofMul c)

private theorem multiplicativeLine_split :
    IsSplitTorus (specGroup (groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters)) := by
  refine ⟨1, ?_⟩
  obtain ⟨e⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := k) 1
  let a : Specs.CharacterDescent.StandardLattice.{u} 1 ≃*
      Specs.DiagonalizableGroups.IntegerCharacters.{u} :=
    MulEquiv.funUnique (Fin 1) _
  exact ⟨(hopfSpec (CommRingCat.of k)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv k k a)).op ≪≫ e⟩

private theorem face_kernel_cocharacter {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (z : Cocharacter P.T.group)
    (hz : ∀ α ∈ I, pairing P.T.group α.val z = 0) :
    ∃ d : Cocharacter S.kernelTorus.group, d ≫ S.kernelTorus.inclusion = z := by
  obtain ⟨T, hT, hkill, _, hfac⟩ :=
    common_kernel P.split (fun α : I => α.val.val)
  obtain ⟨j, hj⟩ := S.kernel.2.2 T (isTorus_of_split hT)
    (fun α hα => hkill ⟨α, hα⟩)
  obtain ⟨d, hd⟩ := hfac multiplicativeLine_split z (fun α => by
    rw [← powerMorphism_zero]
    exact (RootData.CharacterPairing.characterPairingComposition P.T.group α.val.val z).1 0
      |>.mpr (hz α.val α.property))
  exact ⟨d ≫ j, by rw [Category.assoc, hj, hd]⟩

private theorem face_cocharacter_decomposition {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I)
    (hSpan : letI := D.comm
      ∀ y : D.toBased.Y, (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I))
    (lam : Cocharacter P.T.group) :
    letI := D.comm
    ∃ (n : ℕ) (c : Cocharacter S.torus.group) (z : Cocharacter S.kernelTorus.group),
      0 < n ∧ lam ^ n = (c ≫ S.toAmbientTorus) * (z ≫ S.kernelTorus.inclusion) := by
  letI := D.comm
  obtain ⟨n, z, hn, hzero, hz⟩ := face_cocharacter_multiple D I lam
  obtain ⟨c, hc⟩ := (hSpan (n • Additive.ofMul lam - z)).mpr hz
  obtain ⟨d, hd⟩ := face_kernel_cocharacter S z.toMul (fun α hα => by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq]
    exact hzero α hα)
  refine ⟨n, c, d, hn, ?_⟩
  rw [hc, hd]
  change Additive.toMul (n • Additive.ofMul lam) =
    Additive.toMul ((n • Additive.ofMul lam - z) + z)
  rw [sub_add_cancel]

private def restrictFaceCharacters {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) :
    Additive (Character P.T.group) →ₗ[ℤ] Additive (Character S.torus.group) :=
  (characterPullback S.toAmbientTorus).toAdditive.toIntLinearMap

private theorem face_character_span_injective {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I)
    (hSpan : letI := D.comm
      ∀ y : D.toBased.Y, (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)) :
    letI := D.comm
    Set.InjOn (restrictFaceCharacters S) (Submodule.span ℤ (D.datum.rootDatum.root '' I)) := by
  letI := D.comm
  have vanish (x : Additive (Character P.T.group))
      (hx : x ∈ Submodule.span ℤ (D.datum.rootDatum.root '' I))
      (hzero : restrictFaceCharacters S x = 0) : x = 0 := by
    let Q := D.datum.rootDatum
    have hfun : Q.toLinearMap x = 0 := by
      ext y
      obtain ⟨n, z, hn, hzeros, hz⟩ := face_cocharacter_multiple D I y.toMul
      obtain ⟨c, hc⟩ := (hSpan (n • y - z)).mpr hz
      have hxz : Q.toLinearMap x z = 0 := by
        have hle : Submodule.span ℤ (Q.root '' I) ≤ LinearMap.ker (Q.toLinearMap.flip z) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i, hi, rfl⟩
          exact LinearMap.mem_ker.mpr (hzeros i hi)
        exact LinearMap.mem_ker.mp (hle hx)
      have hxc : Q.toLinearMap x (n • y - z) = 0 := by
        have hc' : Additive.ofMul (c ≫ S.toAmbientTorus) = n • y - z :=
          congrArg Additive.ofMul hc
        rw [← hc']
        change D.datum.rootDatum.toLinearMap (Additive.ofMul x.toMul)
          (Additive.ofMul (c ≫ S.toAmbientTorus)) = 0
        rw [D.datum.pairing_eq, pairing_pushforward]
        have hh : S.toAmbientTorus ≫ x.toMul = 1 := congrArg Additive.toMul hzero
        change pairing S.torus.group (S.toAmbientTorus ≫ x.toMul) c = 0
        rw [hh, pairing_trivial]
      rw [map_sub, map_nsmul, hxz, sub_zero, nsmul_eq_mul] at hxc
      exact (mul_eq_zero.mp hxc).resolve_left (by exact_mod_cast hn.ne')
    exact Q.toLinearMap.toPerfPair.injective (by
      change Q.toLinearMap x = Q.toLinearMap 0
      rw [hfun, map_zero])
  intro x hx y hy h
  apply sub_eq_zero.mp
  exact vanish (x - y) (Submodule.sub_mem _ hx hy) (by rw [map_sub, h, sub_self])

end FaceLattice

section BorelIntersections

open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.RankOneFlag (SameSubgroup)
open LinearAlgebraicGroups.CocharacterDynamics
open private extendSubgroup extend_subgroupOf borel_of_same
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private subgroupOf_trans from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private pointHom pointHom_injective subgroupInclusionFactors
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private factor_laurent_descends from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

private def subgroupPreimage {G H : GroupScheme k} (f : H ⟶ G) (B : ClosedSubgroup G) :
    ClosedSubgroup H :=
  ⟨pullback B.inclusion f, pullback.snd B.inclusion f,
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback B.inclusion f).map (Grp.forget _ ⋙ Over.forget _))
      B.isClosedImmersion⟩

private theorem subgroupPreimage_pullback {G H : GroupScheme k} (f : H ⟶ G)
    (B : ClosedSubgroup G) :
    IsPullback (pullback.fst B.inclusion f) (subgroupPreimage f B).inclusion B.inclusion f :=
  IsPullback.of_hasPullback _ _

private theorem splitFace_reductive {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) : GeometricRadicals.IsReductive S.group := by
  apply reductive_of_semisimple
  exact Reductive.CentralDerived.derivedSemisimple (closedSubgroupAlgebraicGroup S.levi)
    S.reductive S.derived S.isDerived

private theorem kBorel_of_same {A : AffineAlgebraicGroup k} {B C : ClosedSubgroup A.val}
    (h : SameSubgroup B C) (hB : IsKBorel B) : IsKBorel C := by
  let E := AlgebraicClosure k
  exact ⟨(extendSubgroup E C).isClosedImmersion, borel_of_same (H := GeometricRadicals.GeometricGroup A)
    hB.choose_spec ⟨extend_subgroupOf h.1, extend_subgroupOf h.2⟩⟩

/-- On the derived Levi the central component of the ambient cocharacter acts
trivially. The equality is an equality of conjugation families over test rings. -/
private theorem face_orbit_eq {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (lam : Cocharacter P.T.group)
    (c : Cocharacter S.torus.group) (z : Cocharacter S.kernelTorus.group)
    (hlam : letI := D.comm; lam = (c ≫ S.toAmbientTorus) * (z ≫ S.kernelTorus.inclusion))
    (R : TestAlgebra k) (g : GroupPoints S.group.val R) :
    orbit (lam ≫ P.T.inclusion) (pointHom S.inclusion R g) =
      pointHom S.inclusion (laurentAlgebra R) (orbit (c ≫ S.torus.inclusion) g) := by
  letI := D.comm
  let L := laurentAlgebra R
  let Y := (testSpec k).obj (Opposite.op L)
  let s : Y ⟶ (multiplicativeLine k).X := unitPoint L (laurentParameter R)
  let q : Y ⟶ S.group.val.X := s ≫ (c ≫ S.torus.inclusion).hom.hom
  let t := q ≫ S.inclusion.hom.hom
  let Z := subgroupOfSubgroup P.T S.kernelTorus
  let v := (s ≫ z.hom.hom) ≫ Z.inclusion.hom.hom
  let p : Y ⟶ S.group.val.X := mapPoints (laurentConstants R) g
  let a := p ≫ S.inclusion.hom.hom
  have hc : (c ≫ S.toAmbientTorus) ≫ P.T.inclusion = (c ≫ S.torus.inclusion) ≫ S.inclusion := by
    rw [Category.assoc, Category.assoc, S.intersection.w]
  have hz : (z ≫ S.kernelTorus.inclusion) ≫ P.T.inclusion = z ≫ Z.inclusion :=
    Category.assoc _ _ _
  have hlam' : (lam ≫ P.T.inclusion).hom.hom =
      ((c ≫ S.toAmbientTorus).hom.hom * (z ≫ S.kernelTorus.inclusion).hom.hom) ≫
        P.T.inclusion.hom.hom := by
    rw [hlam]
    rfl
  have ht : s ≫ (lam ≫ P.T.inclusion).hom.hom = t * v := by
    rw [hlam', MonObj.mul_comp, MonObj.comp_mul,
      ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hc, hz]
    simp only [t, q, v, Grp.comp_hom_hom, Category.assoc]
  have hcomm : Commute a v := by
    have hcentral : Centralizes Z.inclusion a :=
      (S.centralizer _ _).mpr ⟨p ≫ S.derived.inclusion.hom.hom, Category.assoc _ _ _⟩
    simpa only [Category.id_comp] using
      (centralizes_iff _ _).mp hcentral Y (𝟙 Y) (s ≫ z.hom.hom)
  change (s ≫ (lam ≫ P.T.inclusion).hom.hom) *
      ((testSpec k).map (laurentConstants R).op ≫ (g ≫ S.inclusion.hom.hom)) *
        (s ≫ (lam ≫ P.T.inclusion).hom.hom)⁻¹ =
    (q * p * q⁻¹) ≫ S.inclusion.hom.hom
  rw [ht, ← Category.assoc ((testSpec k).map (laurentConstants R).op), postMul, postMul, postInv]
  change (t * v) * a * (t * v)⁻¹ = t * a * t⁻¹
  rw [mul_inv_rev]
  calc
    _ = t * (v * a * v⁻¹) * t⁻¹ := by simp only [mul_assoc]
    _ = _ := by
      have hv : v * a * v⁻¹ = a := by
        rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
      rw [hv]

private theorem face_extension_iff {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (lam : Cocharacter P.T.group)
    (c : Cocharacter S.torus.group) (z : Cocharacter S.kernelTorus.group)
    (hlam : letI := D.comm; lam = (c ≫ S.toAmbientTorus) * (z ≫ S.kernelTorus.inclusion))
    (R : TestAlgebra k) (g : GroupPoints S.group.val R) :
    HasExtension (lam ≫ P.T.inclusion) (pointHom S.inclusion R g) ↔
      HasExtension (c ≫ S.torus.inclusion) g := by
  have horbit := face_orbit_eq S lam c z hlam R g
  let H := subgroupOfSubgroup S.levi S.derived
  constructor
  · rintro ⟨_, q, hq, -⟩
    obtain ⟨q', hq'⟩ := factor_laurent_descends P.G H R q
      ⟨orbit (c ≫ S.torus.inclusion) g, horbit.symm.trans hq.symm⟩
    refine ⟨mapPoints (polynomialEvaluate R 0) q', q', pointHom_injective H _ ?_, rfl⟩
    change ((_ : _ ⟶ S.group.val.X) ≫ S.inclusion.hom.hom) =
      pointHom S.inclusion _ (orbit (c ≫ S.torus.inclusion) g)
    change ((testSpec k).map (polynomialToLaurent R).op ≫ q') ≫ S.inclusion.hom.hom = _
    rw [Category.assoc, show q' ≫ S.inclusion.hom.hom = q from hq', ← horbit]
    exact hq
  · rintro ⟨_, q, hq, -⟩
    refine ⟨mapPoints (polynomialEvaluate R 0) (pointHom S.inclusion _ q),
      pointHom S.inclusion _ q, ?_, rfl⟩
    rw [horbit, ← hq]
    exact (Category.assoc _ _ _).symm

private theorem face_kernel_pairing {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I) (α : Root P.T) (hα : letI := D.comm; α ∈ leviRoots D.datum I)
    (z : Cocharacter S.kernelTorus.group) :
    pairing P.T.group α.val (z ≫ S.kernelTorus.inclusion) = 0 := by
  letI := D.comm
  rw [pairing_pushforward]
  change pairing S.kernelTorus.group (S.kernelTorus.inclusion ≫ α.val) z = 0
  rw [character_restricts_trivially (D := D.datum) S.kernel hα, pairing_trivial]

private theorem pairing_pow {T : ClosedSubgroup P.G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (α : Character T.group) (c : Cocharacter T.group) (n : ℕ) :
    pairing T.group α (c ^ n) = (n : ℤ) * pairing T.group α c := by
  rw [← D.pairing_eq α (c ^ n), ← D.pairing_eq α c]
  change D.rootDatum.toLinearMap (Additive.ofMul α) (n • Additive.ofMul c) = _
  rw [map_nsmul, nsmul_eq_mul]

private theorem face_preimage_borel {D : AttachedDatum P} {I : Set (Root P.T)}
    (S : SplitFace D I)
    (hSpan : letI := D.comm
      ∀ y : D.toBased.Y, (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I))
    (B : ClosedSubgroup P.G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf P.T B) :
    IsKBorel (subgroupPreimage S.inclusion B) ∧ IsSubgroupOf S.torus (subgroupPreimage S.inclusion B) := by
  letI := D.comm
  obtain ⟨lam, _, hlam, _, hsign⟩ := (RootData.BorelsAndChambers.borelsThroughT
    P.G P.reductive P.T P.split P.maximal).1 B hB hTB
  obtain ⟨n, c, z, hn, hdecomp⟩ := face_cocharacter_decomposition S hSpan lam
  let d := lam ^ n
  have hd : IsRegular P.T d := fun α => by
    change pairing P.T.group α.val (lam ^ n) ≠ 0
    rw [pairing_pow D.datum]
    exact mul_ne_zero (by exact_mod_cast hn.ne') (hlam α)
  have hpos : positiveRoots P.T d = subgroupRoots P.T B := by
    rw [hsign]
    ext α
    change 0 < pairing P.T.group α.val (lam ^ n) ↔ 0 < pairing P.T.group α.val lam
    rw [pairing_pow D.datum, mul_pos_iff_of_pos_left (by exact_mod_cast hn)]
  have hH := splitFace_reductive S
  have hc : IsRegular S.torus c := by
    intro β
    obtain ⟨α, hα, ha⟩ := faceRootRestrictionSurjective D I S β.property
    change characterPullback S.toAmbientTorus α.val = β.val at ha
    have h := (hd α)
    change pairing P.T.group α.val (lam ^ n) ≠ 0 at h
    rw [hdecomp, ← D.datum.pairing_eq] at h
    change D.datum.rootDatum.toLinearMap (Additive.ofMul α.val)
      (Additive.ofMul (c ≫ S.toAmbientTorus) + Additive.ofMul (z ≫ S.kernelTorus.inclusion)) ≠ 0 at h
    rw [map_add, D.datum.pairing_eq, D.datum.pairing_eq, face_kernel_pairing S α hα,
      add_zero, pairing_pushforward, ha] at h
    exact h
  obtain ⟨L⟩ := CocharacterDynamics.existsLimitDecomposition P.G (d ≫ P.T.inclusion)
  obtain ⟨M⟩ := CocharacterDynamics.existsLimitDecomposition S.group (c ≫ S.torus.inclusion)
  obtain ⟨_, hL, hTL, hLpos, _, _⟩ := RootData.BorelsAndChambers.regularCocharacterBorel
    P.G P.reductive P.T P.split P.maximal d hd L
  obtain ⟨_, hM, hTM, _, _, _⟩ := RootData.BorelsAndChambers.regularCocharacterBorel
    S.group hH S.torus S.torusSplit S.torusMaximal c hc M
  have hsys := (RootData.BorelsAndChambers.positiveSystemsFromCocharacters P.G
    P.reductive P.T P.split P.maximal _).mpr ⟨d, hd, hpos⟩
  obtain ⟨X, _, _, _, huniq⟩ :=
    ((RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).2 _).mp hsys
  have h₁ : IsSubgroupOf B L.parabolic :=
    subgroupOf_trans (huniq B hB hTB rfl).2 (huniq L.parabolic hL hTL (hLpos.trans hpos)).1
  have h₂ : IsSubgroupOf L.parabolic B :=
    subgroupOf_trans (huniq L.parabolic hL hTL (hLpos.trans hpos)).2 (huniq B hB hTB rfl).1
  let C := subgroupPreimage S.inclusion B
  let hp := subgroupPreimage_pullback S.inclusion B
  have hCM : IsSubgroupOf C M.parabolic := by
    apply subgroupInclusionFactors (closedSubgroupAlgebraicGroup (G := S.group) C).property.1
      M.parabolic C.inclusion
    intro R p
    apply (M.parabolic_points R _).mp
    apply (face_extension_iff S d c z hdecomp R _).mp
    obtain ⟨b, hb⟩ := h₁
    apply (L.parabolic_points R _).mpr
    refine ⟨pointHom (pullback.fst B.inclusion S.inclusion ≫ b) R p, ?_⟩
    change pointHom ((pullback.fst B.inclusion S.inclusion ≫ b) ≫ L.parabolic.inclusion) R p =
      pointHom (C.inclusion ≫ S.inclusion) R p
    rw [Category.assoc, hb, hp.w]
    rfl
  have hMC : IsSubgroupOf M.parabolic C := by
    obtain ⟨b, hb⟩ := subgroupInclusionFactors
      (closedSubgroupAlgebraicGroup (G := S.group) M.parabolic).property.1 B
      (M.parabolic.inclusion ≫ S.inclusion) (fun R p => by
        have h := (M.parabolic_points R _).mpr ⟨p, rfl⟩
        have h' := (face_extension_iff S d c z hdecomp R _).mpr h
        obtain ⟨q, hq⟩ := (L.parabolic_points R _).mp h'
        obtain ⟨j, hj⟩ := h₂
        refine ⟨pointHom j R q, ?_⟩
        change pointHom (j ≫ B.inclusion) R q =
          pointHom S.inclusion R (pointHom M.parabolic.inclusion R p)
        rw [hj]
        exact hq)
    exact ⟨hp.lift b M.parabolic.inclusion hb, hp.lift_snd _ _ _⟩
  exact ⟨kBorel_of_same ⟨hMC, hCM⟩ hM, subgroupOf_trans hTM hMC⟩

end BorelIntersections

section Descent

open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.GeometricRadicals (IsReductive)
open Specs.Pinning (PinnedGroup SimpleRoot IsSimple)
open private extendedBorel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment
open private borelUnderIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private extendSubgroup borel_of_same from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

private theorem borel_of_compared_subgroups [IsAlgClosed k] {G H : AffineAlgebraicGroup k}
    {B : ClosedSubgroup G.val} {C : ClosedSubgroup H.val} (e : G.val ≅ H.val)
    (b : B.group ≅ C.group) (hb : b.hom ≫ C.inclusion = B.inclusion ≫ e.hom) :
    IsBorel B ↔ IsBorel C := by
  have hi : b.inv ≫ B.inclusion = C.inclusion ≫ e.inv := by
    apply (cancel_epi b.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hb, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  constructor
  · intro hB
    refine borel_of_same (H := H) (borelUnderIso e hB) ⟨⟨b.hom, hb⟩, ⟨b.inv, ?_⟩⟩
    change b.inv ≫ B.inclusion ≫ e.hom = C.inclusion
    rw [← Category.assoc, hi, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro hC
    refine borel_of_same (H := G) (borelUnderIso e.symm hC) ⟨⟨b.inv, hi⟩, ⟨b.hom, ?_⟩⟩
    change b.hom ≫ C.inclusion ≫ e.inv = B.inclusion
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem extended_borel_comparison
    (L : Type u) [Field L] [IsAlgClosed L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (B : ClosedSubgroup G.val) (C : ClosedSubgroup H.val)
    (e : (groupBaseChange F K).obj G.val ≅ H.val)
    (b : (groupBaseChange F K).obj B.group ≅ C.group)
    (hb : b.hom ≫ C.inclusion = (groupBaseChange F K).map B.inclusion ≫ e.hom) :
    IsBorel (extendSubgroup L B) ↔ IsBorel (extendSubgroup L C) := by
  let Ψ := groupBaseChange K L
  let t := groupBaseChangeTowerIso (k := F) (K := K) (L := L)
  let e' := (t.app G.val).symm ≪≫ Ψ.mapIso e
  let b' := (t.app B.group).symm ≪≫ Ψ.mapIso b
  have hb' : b'.hom ≫ (groupBaseChange K L).map C.inclusion =
      (groupBaseChange F L).map B.inclusion ≫ e'.hom := by
    change ((t.app B.group).inv ≫ Ψ.map b.hom) ≫ Ψ.map C.inclusion =
      (groupBaseChange F L).map B.inclusion ≫ (t.app G.val).inv ≫ Ψ.map e.hom
    rw [Category.assoc, ← Ψ.map_comp, hb, Ψ.map_comp]
    have hn : (groupBaseChange F L).map B.inclusion ≫ (t.app G.val).inv =
        (t.app B.group).inv ≫ Ψ.map ((groupBaseChange F K).map B.inclusion) :=
      t.inv.naturality B.inclusion
    rw [← Category.assoc (t.app B.group).inv, ← hn, Category.assoc]
  exact borel_of_compared_subgroups (G := Unipotent.baseChangedAlgebraicGroup L G)
    (H := Unipotent.baseChangedAlgebraicGroup L H) (B := extendSubgroup L B)
    (C := extendSubgroup L C) e' b' hb'

private theorem compared_borel_ascent {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (g : IsReductive G) (B : ClosedSubgroup G.val) (C : ClosedSubgroup H.val)
    (e : (groupBaseChange F K).obj G.val ≅ H.val)
    (b : (groupBaseChange F K).obj B.group ≅ C.group)
    (hb : b.hom ≫ C.inclusion = (groupBaseChange F K).map B.inclusion ≫ e.hom)
    (hB : IsKBorel B) : IsKBorel C := by
  let L := AlgebraicClosure K
  exact ⟨(extendSubgroup L C).isClosedImmersion,
    (extended_borel_comparison L B C e b hb).mp (extendedBorel G g B hB L)⟩

private theorem compared_borel_descent [IsGalois F K]
    {G : AffineAlgebraicGroup F} {H : AffineAlgebraicGroup K}
    (h : IsReductive H) (B : ClosedSubgroup G.val) (C : ClosedSubgroup H.val)
    (e : (groupBaseChange F K).obj G.val ≅ H.val)
    (b : (groupBaseChange F K).obj B.group ≅ C.group)
    (hb : b.hom ≫ C.inclusion = (groupBaseChange F K).map B.inclusion ≫ e.hom)
    (hC : IsKBorel C) : IsKBorel B := by
  let L := AlgebraicClosure F
  let a : K →ₐ[F] L := IsAlgClosed.lift
  letI : Algebra K L := a.toAlgebra
  letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  exact ⟨(extendSubgroup L B).isClosedImmersion,
    (extended_borel_comparison L B C e b hb).mpr (extendedBorel H h C hC L)⟩

private theorem derivedComparison_square {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} {S : SplitFace D I} (R : RationalFace F S) :
    R.derivedComparison.hom ≫ S.inclusion =
      (groupBaseChange F K).map R.inclusion ≫ R.groupComparison.hom := by
  change R.derivedComparison.hom ≫ S.derived.inclusion ≫ S.levi.inclusion = _
  rw [← Category.assoc R.derivedComparison.hom, R.derivedSquare, Category.assoc, R.leviSquare]
  simp only [RationalFace.inclusion, Functor.map_comp, Category.assoc]

private theorem inducedBorel [IsGalois F K] {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} {S : SplitFace D I} (R : RationalFace F S)
    (B : ClosedSubgroup R.ambient.val) (C : ClosedSubgroup P.G.val)
    (b : (groupBaseChange F K).obj B.group ≅ C.group)
    (hb : b.hom ≫ C.inclusion = (groupBaseChange F K).map B.inclusion ≫ R.groupComparison.hom)
    (hC : IsKBorel C) (hTC : IsSubgroupOf P.T C) :
    ∃ (Q : InducedBorel R B) (j : Q.split.group ⟶ C.group),
      IsPullback j Q.split.inclusion C.inclusion S.inclusion := by
  let E := groupBaseChange F K
  let A := subgroupPreimage R.inclusion B
  let A' := subgroupPreimage S.inclusion C
  let p := pullback.fst B.inclusion R.inclusion
  have hp : IsPullback p A.inclusion B.inclusion R.inclusion := subgroupPreimage_pullback _ _
  have hp' : IsPullback (E.map p ≫ b.hom) (E.map A.inclusion ≫ R.derivedComparison.hom)
      C.inclusion S.inclusion := by
    apply (LinearAlgebraicGroups.baseChangeSubgroupPullback F K hp).of_iso
      (Iso.refl _) b R.derivedComparison R.groupComparison
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · exact hb.symm
    · exact (derivedComparison_square R).symm
  let a : E.obj A.group ≅ A'.group := hp'.isoPullback
  have ha : a.hom ≫ A'.inclusion = E.map A.inclusion ≫ R.derivedComparison.hom :=
    hp'.isoPullback_hom_snd
  obtain ⟨hA', hTA'⟩ := face_preimage_borel S R.integralImage C hC hTC
  have hA := compared_borel_descent (G := R.group) (H := S.group) (splitFace_reductive S)
    A A' R.derivedComparison a ha hA'
  exact ⟨⟨A, p, hp, hA, A', hA', hTA', a, ha⟩, pullback.fst C.inclusion S.inclusion,
    subgroupPreimage_pullback _ _⟩

private theorem inducedOpposite {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} {S : SplitFace D I} {R : RationalFace F S}
    (Bp : InducedBorel R R.positive) (Bn : InducedBorel R R.negative) :
    ∃ (ip : R.torus.group ⟶ Bp.rational.group) (in' : R.torus.group ⟶ Bn.rational.group),
      IsPullback ip in' Bp.rational.inclusion Bn.rational.inclusion ∧
      ip ≫ Bp.rational.inclusion = R.torus.inclusion := by
  let i := R.torus.inclusion
  let t := R.toAmbientTorus
  let hp := Bp.intersection
  let hn := Bn.intersection
  let ip := hp.lift (t ≫ R.positiveTorus) i
    (by rw [Category.assoc, R.positiveTorusSquare]; exact R.intersection.w)
  let in' := hn.lift (t ≫ R.negativeTorus) i
    (by rw [Category.assoc, ← R.opposite.w, R.positiveTorusSquare]; exact R.intersection.w)
  have hip : ip ≫ Bp.rational.inclusion = i := hp.lift_snd _ _ _
  have hin : in' ≫ Bn.rational.inclusion = i := hn.lift_snd _ _ _
  letI : Mono i := (Grp.forget (SchemeOver F)).mono_of_mono_map (mono_over _ R.torus.isClosedImmersion)
  letI : Mono Bp.rational.inclusion := (Grp.forget (SchemeOver F)).mono_of_mono_map
    (mono_over _ Bp.rational.isClosedImmersion)
  letI : Mono Bn.rational.inclusion := (Grp.forget (SchemeOver F)).mono_of_mono_map
    (mono_over _ Bn.rational.isClosedImmersion)
  refine ⟨ip, in', IsPullback.mk' (hip.trans hin.symm) ?_ ?_, hip⟩
  · intro X x y h _
    apply (cancel_mono i).mp
    rw [← hip, ← Category.assoc, ← Category.assoc, h]
  · intro X x y h
    have hxy : (x ≫ Bp.toAmbient) ≫ R.positive.inclusion =
        (y ≫ Bn.toAmbient) ≫ R.negative.inclusion := by
      rw [Category.assoc, Category.assoc, hp.w, hn.w, ← Category.assoc, h, Category.assoc]
    let a := R.opposite.lift (x ≫ Bp.toAmbient) (y ≫ Bn.toAmbient) hxy
    have ha : a ≫ R.positiveTorus = x ≫ Bp.toAmbient := R.opposite.lift_fst _ _ _
    have h' : a ≫ R.ambientTorus.inclusion = (x ≫ Bp.rational.inclusion) ≫ R.inclusion := by
      rw [← R.positiveTorusSquare, ← Category.assoc, ha, Category.assoc, hp.w, Category.assoc]
    let u := R.intersection.lift a (x ≫ Bp.rational.inclusion) h'
    have hu : u ≫ i = x ≫ Bp.rational.inclusion := R.intersection.lift_snd _ _ _
    refine ⟨u, (cancel_mono Bp.rational.inclusion).mp (by rw [Category.assoc, hip, hu]),
      (cancel_mono Bn.rational.inclusion).mp (by rw [Category.assoc, hin, hu, h])⟩

private theorem splitInducedOpposite {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} {S : SplitFace D I} {R : RationalFace F S}
    (Bp : InducedBorel R R.positive) (Bn : InducedBorel R R.negative)
    {ip : R.torus.group ⟶ Bp.rational.group} {in' : R.torus.group ⟶ Bn.rational.group}
    (hp : IsPullback ip in' Bp.rational.inclusion Bn.rational.inclusion)
    (hi : ip ≫ Bp.rational.inclusion = R.torus.inclusion) :
    ∃ (tp : S.torus.group ⟶ Bp.split.group) (tn : S.torus.group ⟶ Bn.split.group),
      IsPullback tp tn Bp.split.inclusion Bn.split.inclusion ∧
        tp ≫ Bp.split.inclusion = S.torus.inclusion := by
  let E := groupBaseChange F K
  let t := R.torusComparison
  let tp := t.inv ≫ E.map ip ≫ Bp.comparison.hom
  let tn := t.inv ≫ E.map in' ≫ Bn.comparison.hom
  have hp' := (LinearAlgebraicGroups.baseChangeSubgroupPullback F K hp).of_iso
    t Bp.comparison Bn.comparison R.derivedComparison
    (fst' := tp) (snd' := tn)
    (by rw [Iso.hom_inv_id_assoc]) (by rw [Iso.hom_inv_id_assoc]) Bp.square.symm Bn.square.symm
  refine ⟨tp, tn, hp', ?_⟩
  dsimp only [tp, t]
  simp only [Category.assoc, Bp.square]
  rw [← Functor.map_comp_assoc, hi, ← R.torusSquare, Iso.inv_hom_id_assoc]

private theorem simplyConnected_of_compared_baseChange
    (G : AffineAlgebraicGroup F) (H : AffineAlgebraicGroup K)
    (j : (groupBaseChange F K).obj G.val ≅ H.val)
    (hc : SimplyConnectedLattice.GeometricallySimplyConnected H) :
    SimplyConnectedLattice.GeometricallySimplyConnected G := by
  let E := AlgebraicClosure F
  let L := AlgebraicClosure K
  let emb : E →ₐ[F] L := IsAlgClosed.lift
  letI : Algebra E L := emb.toAlgebra
  letI : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' emb.comp_algebraMap.symm
  let g : (groupBaseChange E L).obj ((GeometricRadicals.GeometricGroup G).val) ≅
      (GeometricRadicals.GeometricGroup H).val :=
    ((groupBaseChangeTowerIso (k := F) (K := E) (L := L)).app G.val) ≪≫
      ((groupBaseChangeTowerIso (k := F) (K := K) (L := L)).app G.val).symm ≪≫
      (groupBaseChange K L).mapIso j
  intro X hX f hf
  have hXr := reductive_of_semisimple X hX
  obtain ⟨T, hT, hm⟩ := MaximalToriExist.geometricallyMaximalTorusExists X hX.1
    (connectedOfGeometricallyConnected X hX.2.1)
  have hsplit : IsSplitTorus T.group :=
    split_of_torus ((isTorus_iff_coordinates (closedSubgroupAlgebraicGroup T)).mp hT)
  let P := splitBorelPair X hXr T hsplit hm
  have hCentral := centralIsogeny_baseChange L P f hf
  have hXL : GeometricRadicals.IsSemisimple (Unipotent.baseChangedAlgebraicGroup L X) :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension X hX.1 hX.2.1).mpr hX
  haveI := hc (Unipotent.baseChangedAlgebraicGroup L X) hXL
    ((groupBaseChange E L).map f ≫ g.hom) (centralIsogeny_postIso g hCentral)
  exact isIso_of_scalarExtension L f (IsIso.of_isIso_comp_right _ g.hom)

theorem rationalDerivedSimplyConnected : RationalDerivedSimplyConnected.{u} := by
  intro F K _ _ _ P D I S R
  exact simplyConnected_of_compared_baseChange R.group S.group R.derivedComparison
    (splitDerivedSimplyConnected D I S R.integralImage)

private abbrev forgetScheme (k : Type u) [Field k] : GroupScheme k ⥤ Scheme.{u} :=
  Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))

private theorem coefficientAction_naturality (σ : Gal(K/F)) {X Y : GroupScheme F}
    (f : X ⟶ Y) :
    coefficientAction σ X ≫ ((groupBaseChange F K).map f).hom.hom.left =
      ((groupBaseChange F K).map f).hom.hom.left ≫ coefficientAction σ Y := by
  apply pullback.hom_ext
  · simp only [coefficientAction, Functor.mapGrp_map_hom_hom, Over.pullback_map_left,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [coefficientAction, Functor.mapGrp_map_hom_hom, Over.pullback_map_left,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]

private theorem comparedAction_naturality (σ : Gal(K/F)) {X Y : GroupScheme F}
    {X' Y' : GroupScheme K} (e : (groupBaseChange F K).obj X ≅ X')
    (d : (groupBaseChange F K).obj Y ≅ Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : e.hom ≫ g = (groupBaseChange F K).map f ≫ d.hom) :
    comparedAction σ e ≫ g.hom.hom.left = g.hom.hom.left ≫ comparedAction σ d := by
  let U := forgetScheme K
  have h' : (U.mapIso e).hom ≫ U.map g = U.map ((groupBaseChange F K).map f) ≫
      (U.mapIso d).hom := by
    simpa only [Functor.map_comp, Functor.mapIso_hom] using U.congr_map h
  have hn := coefficientAction_naturality σ f
  change coefficientAction σ X ≫ U.map ((groupBaseChange F K).map f) =
    U.map ((groupBaseChange F K).map f) ≫ coefficientAction σ Y at hn
  have h'' : U.map g ≫ (U.mapIso d).inv =
      (U.mapIso e).inv ≫ U.map ((groupBaseChange F K).map f) := by
    rw [← cancel_mono (U.mapIso d).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, ← h', Iso.inv_hom_id_assoc]
  change (U.mapIso e).inv ≫ (coefficientAction σ X ≫ (U.mapIso e).hom) ≫ U.map g =
    U.map g ≫ (U.mapIso d).inv ≫ coefficientAction σ Y ≫ (U.mapIso d).hom
  simp only [Category.assoc, h', ← Category.assoc (coefficientAction σ X), hn]
  simp only [← Category.assoc (U.map g), h'', Category.assoc]

theorem rationalRootMarkAction : RationalRootMarkAction.{u} := by
  intro F K _ _ _ A₀ A Q D I S R a m ω h
  letI := D.comm
  intro σ α
  let U := forgetScheme K
  have ht : comparedAction σ⁻¹ R.torusComparison ≫ U.map S.toAmbientTorus =
      U.map S.toAmbientTorus ≫ comparedAction σ⁻¹ R.ambientTorusComparison :=
    comparedAction_naturality σ⁻¹ R.torusComparison R.ambientTorusComparison R.torusMapSquare
  have hd : R.derivedComparison.hom ≫ S.inclusion =
      (groupBaseChange F K).map R.inclusion ≫ R.groupComparison.hom := by
    change R.derivedComparison.hom ≫ S.derived.inclusion ≫ S.levi.inclusion =
      (groupBaseChange F K).map (R.derived.inclusion ≫ R.levi.inclusion) ≫ R.groupComparison.hom
    rw [← Category.assoc R.derivedComparison.hom, R.derivedSquare, Category.assoc, R.leviSquare]
    simp only [Functor.map_comp, Category.assoc]
  have hg : comparedAction σ⁻¹ R.derivedComparison ≫ U.map S.inclusion =
      U.map S.inclusion ≫ comparedAction σ⁻¹ R.groupComparison :=
    comparedAction_naturality σ⁻¹ R.derivedComparison R.groupComparison hd
  have hClosed : IsClosedImmersion S.inclusion.hom.hom.left := by
    change IsClosedImmersion (S.derived.inclusion.hom.hom.left ≫ S.levi.inclusion.hom.hom.left)
    letI := S.derived.isClosedImmersion
    letI := S.levi.isClosedImmersion
    infer_instance
  have hiClosed : IsClosedImmersion S.toAmbientTorus.hom.hom.left :=
    MorphismProperty.of_isPullback (S.intersection.map U).flip hClosed
  letI := hClosed
  letI := hiClosed
  dsimp only
  constructor
  · let β := diagramRoot ω σ α
    have hh : comparedAction σ⁻¹ R.ambientTorusComparison ≫ U.map β.val =
        U.map α.val ≫ comparedAction σ⁻¹ m := h.characters σ α
    change comparedAction σ⁻¹ R.torusComparison ≫ U.map (S.toAmbientTorus ≫ β.val) =
      U.map (S.toAmbientTorus ≫ α.val) ≫ comparedAction σ⁻¹ m
    rw [U.map_comp S.toAmbientTorus β.val, U.map_comp S.toAmbientTorus α.val,
      ← Category.assoc, ht]
    simp only [Category.assoc, hh]
  constructor
  · intro c d hc hd
    have hc' := (U.map_comp c S.toAmbientTorus).symm.trans (U.congr_map hc)
    have hd' := (U.map_comp d S.toAmbientTorus).symm.trans (U.congr_map hd)
    apply (cancel_mono S.toAmbientTorus.hom.hom.left).mp
    change (comparedAction σ⁻¹ m ≫ U.map d) ≫ U.map S.toAmbientTorus =
      (U.map c ≫ comparedAction σ⁻¹ R.torusComparison) ≫ U.map S.toAmbientTorus
    rw [Category.assoc, hd', Category.assoc (U.map c), ht,
      ← Category.assoc (U.map c), hc']
    exact h.cocharacters σ α
  · intro i x y _ hx hy
    have hx' := (U.map_comp x S.inclusion).symm.trans (U.congr_map hx)
    have hy' := (U.map_comp y S.inclusion).symm.trans (U.congr_map hy)
    apply (cancel_mono S.inclusion.hom.hom.left).mp
    change (comparedAction σ⁻¹ a ≫ U.map y) ≫ U.map S.inclusion =
      (U.map x ≫ comparedAction σ⁻¹ R.derivedComparison) ≫ U.map S.inclusion
    rw [Category.assoc, hy', Category.assoc (U.map x), hg, ← Category.assoc (U.map x), hx']
    exact h.pinning σ i

section Bases

open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.SimpleRoots (IsBaseFor evaluate positive)
open private root_weight_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RootGroups

private def oppositeRoot {P : SplitBorelPair k} (D : AttachedDatum P) (α : Root P.T) :
    Root P.T :=
  letI := D.comm
  D.datum.rootDatum.reflectionPerm α α

private theorem oppositeRoot_character {P : SplitBorelPair k} (D : AttachedDatum P)
    (α : Root P.T) : (oppositeRoot D α).val = α.val⁻¹ := by
  letI := D.comm
  apply Additive.ofMul.injective
  rw [← D.datum.root_eq, show Additive.ofMul (α.val⁻¹) = -Additive.ofMul α.val from rfl,
    ← D.datum.root_eq, oppositeRoot, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

private theorem oppositeRoot_involutive {P : SplitBorelPair k} (D : AttachedDatum P) (α : Root P.T) :
    oppositeRoot D (oppositeRoot D α) = α := by
  apply Subtype.ext
  rw [oppositeRoot_character, oppositeRoot_character, inv_inv]

private theorem oppositeRoot_mem_face {P : SplitBorelPair k} (D : AttachedDatum P)
    {I : Set (Root P.T)} {α : Root P.T} (hα : letI := D.comm; α ∈ leviRoots D.datum I) :
    letI := D.comm
    oppositeRoot D α ∈ leviRoots D.datum I := by
  letI := D.comm
  change D.datum.rootDatum.root (D.datum.rootDatum.reflectionPerm α α) ∈
    Submodule.span ℤ (D.datum.rootDatum.root '' I)
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  exact Submodule.neg_mem _ hα

private theorem opposite_roots_of_pullback {P : SplitBorelPair k} (D : AttachedDatum P)
    (N : ClosedSubgroup P.G.val) (hN : IsKBorel N)
    {ip : P.T.group ⟶ P.B.group} {in' : P.T.group ⟶ N.group}
    (hp : IsPullback ip in' P.B.inclusion N.inclusion)
    (ht : ip ≫ P.B.inclusion = P.T.inclusion) :
    ∀ α, α ∈ subgroupRoots P.T N ↔ oppositeRoot D α ∈ subgroupRoots P.T P.B := by
  letI := D.comm
  have disjoint (α : Root P.T) (h₁ : α ∈ subgroupRoots P.T P.B)
      (h₂ : α ∈ subgroupRoots P.T N) : False := by
    obtain ⟨v, hv, hv₀⟩ := α.property.2
    obtain ⟨x, hx⟩ := h₁ hv
    obtain ⟨y, hy⟩ := h₂ hv
    obtain ⟨w, hw, _⟩ := liePullbackComparison k hp x y (hx.trans hy.symm)
    have hw' : mapPointKernel P.T.inclusion w = v := by
      rw [← ht, differential_comp, hw.1, hx]
    let s := identityLieStructure P.G
    letI := s.lieRing
    letI := s.lieAlgebra
    have hvT : v ∈ adjointWeightVectors P.T 1 := by
      rw [← RootData.CharacterPairing.adjointWeightSpaceVectors P.G P.T s 1,
        (RootData.CharacterPairing.zeroWeightSpace P.G P.reductive P.T P.split P.maximal s).2]
      exact ⟨w, hw'⟩
    exact α.property.1 (root_weight_unique P.G P.T P.split hv₀ hv hvT)
  have hTN : IsSubgroupOf P.T N := ⟨in', hp.w.symm.trans ht⟩
  have signs (B : ClosedSubgroup P.G.val) (hB : IsKBorel B) (hT : IsSubgroupOf P.T B)
      (α : Root P.T) :
      oppositeRoot D α ∈ subgroupRoots P.T B ↔ α ∉ subgroupRoots P.T B := by
    obtain ⟨c, _, hc, _, he⟩ := (RootData.BorelsAndChambers.borelsThroughT
      P.G P.reductive P.T P.split P.maximal).1 B hB hT
    rw [he]
    change 0 < pairing P.T.group (oppositeRoot D α).val c ↔ ¬ 0 < pairing P.T.group α.val c
    have hpair : pairing P.T.group (oppositeRoot D α).val c = -pairing P.T.group α.val c := by
      rw [← D.datum.pairing_eq, ← D.datum.pairing_eq α.val, oppositeRoot_character]
      exact map_neg (D.datum.rootDatum.toLinearMap.flip (Additive.ofMul c)) _
    rw [hpair, neg_pos, not_lt]
    exact lt_iff_le_and_ne.trans ⟨And.left, fun h => ⟨h, hc α⟩⟩
  intro α
  constructor
  · intro hα
    exact (signs P.B P.borel P.containsTorus α).mpr (fun h => disjoint α h hα)
  · intro hα
    by_contra hn
    exact disjoint _ hα ((signs N hN hTN α).mpr hn)

private theorem simple_iff_opposite {P : SplitBorelPair k} (D : AttachedDatum P)
    {N : ClosedSubgroup P.G.val}
    (si : ∀ α, α ∈ subgroupRoots P.T N ↔ oppositeRoot D α ∈ subgroupRoots P.T P.B)
    (α : Root P.T) :
    (α ∈ subgroupRoots P.T N ∧
      ∀ β ∈ subgroupRoots P.T N, ∀ δ ∈ subgroupRoots P.T N, α.val ≠ β.val * δ.val) ↔
      IsSimple P (oppositeRoot D α) := by
  have si' (β : Root P.T) : oppositeRoot D β ∈ subgroupRoots P.T N ↔
      β ∈ subgroupRoots P.T P.B := by
    rw [si, oppositeRoot_involutive]
  constructor
  · rintro ⟨hα, h⟩
    refine ⟨(si α).mp hα, ?_⟩
    intro β hβ δ hδ he
    apply h _ ((si' β).mpr hβ) _ ((si' δ).mpr hδ)
    have h' := congrArg Inv.inv he
    simpa only [oppositeRoot_character, inv_inv, mul_inv_rev, mul_comm δ.val⁻¹ β.val⁻¹] using h'
  · rintro ⟨hα, h⟩
    refine ⟨(si α).mpr hα, ?_⟩
    intro β hβ δ hδ he
    apply h _ ((si β).mp hβ) _ ((si δ).mp hδ)
    have h' := congrArg Inv.inv he
    simpa only [oppositeRoot_character, mul_inv_rev, mul_comm δ.val⁻¹ β.val⁻¹] using h'

private theorem faceRootEquivalence {P : SplitBorelPair k} {D : AttachedDatum P}
    {I : Set (Root P.T)} (S : SplitFace D I) :
    letI := D.comm
    ∃ e : ↥(leviRoots D.datum I) ≃ Root (G := S.group) S.torus,
      ∀ α, (e α).val = S.toAmbientTorus ≫ α.val.val := by
  letI := D.comm
  let r (α : ↥(leviRoots D.datum I)) : Root (G := S.group) S.torus :=
    ⟨_, (faceRootRestrictions D I S α.val α.property).1⟩
  have hrI : Function.Injective r := by
    intro α β h
    exact Subtype.ext (faceRootRestrictionInjective D I S α.property β.property
      (congrArg Subtype.val h))
  have hrS : Function.Surjective r := by
    intro β
    obtain ⟨α, ha, h⟩ := faceRootRestrictionSurjective D I S β.property
    exact ⟨⟨α, ha⟩, Subtype.ext h⟩
  exact ⟨Equiv.ofBijective r ⟨hrI, hrS⟩, fun _ => rfl⟩

private theorem attachedBase_regular {P : SplitBorelPair k} (D : AttachedDatum P) :
    letI := D.comm
    ∃ c : Cocharacter P.T.group, IsRegular P.T c ∧
      positiveRoots P.T c = subgroupRoots P.T P.B ∧
      IsBaseFor D.datum.rootDatum (evaluate D.datum c) D.base := by
  letI := D.comm
  letI := D.datum.finiteRoots
  letI := D.datum.freeCharacters
  letI := D.datum.finiteCharacters
  letI := D.datum.reduced
  obtain ⟨c, _, hreg, _, hc⟩ := (RootData.BorelsAndChambers.borelsThroughT
    P.G P.reductive P.T P.split P.maximal).1 P.B P.borel P.containsTorus
  let f := evaluate D.datum c
  have hf (α : Root P.T) : f (D.datum.rootDatum.root α) = pairing P.T.group α.val c := by
    change D.datum.rootDatum.toLinearMap _ (Additive.ofMul c) = _
    rw [D.datum.root_eq, D.datum.pairing_eq]
  have hpos : positive D.datum.rootDatum f = subgroupRoots P.T P.B := by
    rw [hc]
    ext α
    change 0 < f (D.datum.rootDatum.root α) ↔ 0 < pairing P.T.group α.val c
    rw [hf]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor D.datum.rootDatum f (fun α => hf α ▸ hreg α)
  have hs : b.support = D.base.support := by
    ext α
    rw [hb.simple_iff, D.simple_iff, hpos]
    simp only [IsSimple, D.datum.root_eq]
    rfl
  have hEq : b = D.base := by
    revert hs
    cases b
    cases D.base
    intro hs
    cases hs
    rfl
  exact ⟨c, hreg, hc.symm, hEq ▸ hb⟩

private theorem face_positive_base {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} {S : SplitFace D I} {R : RationalFace F S}
    (Bp : InducedBorel R R.positive) {h : IsReductive S.group}
    (E : AttachedDatum (Bp.pair h)) (j : Bp.split.group ⟶ P.B.group)
    (hp : IsPullback j Bp.split.inclusion P.B.inclusion S.inclusion)
    (e : letI := D.comm; ↥(leviRoots D.datum I) ≃ Root (G := S.group) S.torus)
    (he : ∀ α, (e α).val = S.toAmbientTorus ≫ α.val.val) :
    letI := E.comm
    ∀ α, e α ∈ E.base.support ↔ α.val ∈ I := by
  letI := D.comm
  letI := E.comm
  obtain ⟨c, _, hc, hb⟩ := attachedBase_regular D
  obtain ⟨lam, hlam⟩ := Flag.StandardParabolicLevi.exists_face_cocharacter (D := D.datum)
    D.base I S.simple
  have signs (α : Root P.T) := Flag.StandardParabolicLevi.face_root_signs hc hb hlam α
  have compare (α : ↥(leviRoots D.datum I)) :
      e α ∈ subgroupRoots S.torus Bp.split ↔ α.val ∈ subgroupRoots P.T P.B := by
    have hβ := (faceRootRestrictions D I S α.val α.property).1
    have hEq : e α = ⟨S.toAmbientTorus ≫ α.val.val, hβ⟩ := Subtype.ext (he α)
    rw [hEq]
    exact faceBorelRoots D I S P.B Bp.split j hp α.val α.property hβ
  have lifts_sum (a b d : ↥(leviRoots D.datum I))
      (hh : (e a).val = (e b).val * (e d).val) :
      a.val.val = b.val.val * d.val.val := by
    apply Additive.ofMul.injective
    change Additive.ofMul a.val.val = Additive.ofMul b.val.val + Additive.ofMul d.val.val
    rw [← D.datum.root_eq a.val, ← D.datum.root_eq b.val, ← D.datum.root_eq d.val]
    apply face_character_span_injective S R.integralImage a.property
      (Submodule.add_mem _ b.property d.property)
    rw [map_add, D.datum.root_eq, D.datum.root_eq, D.datum.root_eq]
    change Additive.ofMul (S.toAmbientTorus ≫ a.val.val) =
      Additive.ofMul ((S.toAmbientTorus ≫ b.val.val) * (S.toAmbientTorus ≫ d.val.val))
    exact congrArg Additive.ofMul (by simpa only [he] using hh)
  intro α
  rw [E.simple_iff]
  constructor
  · intro hα
    have hPos : α.val ∈ subgroupRoots P.T P.B := (compare α).mp hα.1
    have hSimple : IsSimple P α.val := by
      refine ⟨hPos, ?_⟩
      intro β hβ δ hδ hh
      have hsum : pairing P.T.group α.val.val lam =
          pairing P.T.group β.val lam + pairing P.T.group δ.val lam := by
        rw [hh, ← D.datum.pairing_eq, ← D.datum.pairing_eq β.val, ← D.datum.pairing_eq δ.val]
        exact map_add (D.datum.rootDatum.toLinearMap.flip (Additive.ofMul lam)) _ _
      have hzero := (signs α.val).1.mpr α.property
      have hb₀ := (signs β).2 hβ
      have hd₀ := (signs δ).2 hδ
      let b : ↥(leviRoots D.datum I) := ⟨β, (signs β).1.mp (by omega)⟩
      let d : ↥(leviRoots D.datum I) := ⟨δ, (signs δ).1.mp (by omega)⟩
      apply hα.2 (e b) ((compare b).mpr hβ) (e d) ((compare d).mpr hδ)
      rw [he, he, he]
      change characterPullback S.toAmbientTorus α.val.val =
        characterPullback S.toAmbientTorus β.val * characterPullback S.toAmbientTorus δ.val
      rw [hh, map_mul]
    have hmem := (D.simple_iff _).mpr hSimple
    by_contra hn
    exact ((hlam.2 α.val ⟨hmem, hn⟩).ne') ((signs α.val).1.mpr α.property)
  · intro hα
    have hs := (D.simple_iff _).mp (S.simple hα)
    refine ⟨(compare α).mpr hs.1, ?_⟩
    intro β hβ δ hδ hh
    change β ∈ subgroupRoots S.torus Bp.split at hβ
    change δ ∈ subgroupRoots S.torus Bp.split at hδ
    let b := e.symm β
    let d := e.symm δ
    have hb : (e b) ∈ subgroupRoots S.torus Bp.split := by simpa only [b, e.apply_symm_apply] using hβ
    have hd : (e d) ∈ subgroupRoots S.torus Bp.split := by simpa only [d, e.apply_symm_apply] using hδ
    apply hs.2 _ ((compare b).mp hb) _ ((compare d).mp hd)
    apply lifts_sum α b d
    simpa only [b, d, e.apply_symm_apply] using hh

private theorem face_negative_base {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} {S : SplitFace D I} {R : RationalFace F S}
    (Bp : InducedBorel R R.positive) (Bn : InducedBorel R R.negative)
    {h : IsReductive S.group} (E : AttachedDatum (Bp.pair h)) (En : AttachedDatum (Bn.pair h))
    (e : letI := D.comm; ↥(leviRoots D.datum I) ≃ Root (G := S.group) S.torus)
    (he : ∀ α, (e α).val = S.toAmbientTorus ≫ α.val.val)
    (hpos : letI := E.comm; ∀ α, e α ∈ E.base.support ↔ α.val ∈ I)
    {tp : S.torus.group ⟶ Bp.split.group} {tn : S.torus.group ⟶ Bn.split.group}
    (hp : IsPullback tp tn Bp.split.inclusion Bn.split.inclusion)
    (ht : tp ≫ Bp.split.inclusion = S.torus.inclusion) :
    letI := En.comm
    ∀ α, e α ∈ En.base.support ↔ ∃ δ ∈ I, α.val.val = δ.val⁻¹ := by
  letI := D.comm
  letI := E.comm
  letI := En.comm
  have hs := opposite_roots_of_pullback E Bn.split Bn.splitBorel hp ht
  intro α
  let a : ↥(leviRoots D.datum I) := ⟨oppositeRoot D α.val, oppositeRoot_mem_face D α.property⟩
  have hOpp : e a = oppositeRoot E (e α) := by
    apply Subtype.ext
    rw [oppositeRoot_character, he, he]
    change S.toAmbientTorus ≫ (oppositeRoot D α.val).val = (S.toAmbientTorus ≫ α.val.val)⁻¹
    rw [oppositeRoot_character]
    exact map_inv (characterPullback S.toAmbientTorus) α.val.val
  have hsimple : IsSimple (Bn.pair h) (e α) ↔ IsSimple (Bp.pair h) (oppositeRoot E (e α)) :=
    simple_iff_opposite E hs (e α)
  rw [En.simple_iff, hsimple, ← hOpp, ← E.simple_iff, hpos]
  constructor
  · intro ha
    exact ⟨oppositeRoot D α.val, ha, by rw [oppositeRoot_character, inv_inv]⟩
  · rintro ⟨δ, hδ, heq⟩
    have heq' : oppositeRoot D α.val = δ := Subtype.ext (by
      rw [oppositeRoot_character, heq, inv_inv])
    change oppositeRoot D α.val ∈ I
    rwa [heq']

end Bases

open Specs.BorelsAndChambers (subgroupRoots)
open Specs.RootGroups (AdditiveLine)
open Specs.OrderedRootProducts (RootSubgroupFamily)

private theorem faceDiagram_stable {P : SplitBorelPair K} {D : AttachedDatum P}
    {I : Set (Root P.T)} (ω : Gal(K/F) →* Aut D.toBased)
    (hs : ∀ (σ : Gal(K/F)) (α : Root P.T), diagramRoot ω σ α ∈ I ↔ α ∈ I)
    (σ : Gal(K/F)) :
    letI := D.comm; ∀ α ∈ leviRoots D.datum I, diagramRoot ω σ α ∈ leviRoots D.datum I := by
  letI := D.comm
  let Q := D.datum.rootDatum
  let w := (ω σ).asIso.hom.val
  let M := Submodule.span ℤ (Q.root '' I)
  have hw (α : Root P.T) : w.weightEquiv (Q.root α) = Q.root (diagramRoot ω σ α) :=
    RootPairing.Hom.root_weightMap_apply Q Q α w.toHom
  have hle : M ≤ M.comap w.weightEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨α, hα, rfl⟩
    change w.weightEquiv (Q.root α) ∈ M
    rw [hw]
    exact Submodule.subset_span ⟨_, (hs σ α).mpr hα, rfl⟩
  intro α ha
  change Q.root (diagramRoot ω σ α) ∈ M
  rw [← hw]
  exact hle ha

private theorem face_pinning {A : AdditiveLine K} (Q : PinnedGroup A)
    {D : AttachedDatum Q.pair} {I : Set (Root Q.pair.T)} {S : SplitFace D I}
    {R : RationalFace F S} (Bp : InducedBorel R R.positive) {h : IsReductive S.group}
    (E : AttachedDatum (Bp.pair h))
    (e : letI := D.comm; ↥(leviRoots D.datum I) ≃ Root (G := S.group) S.torus)
    (he : ∀ α, (e α).val = S.toAmbientTorus ≫ α.val.val)
    (hpos : letI := E.comm; ∀ α, e α ∈ E.base.support ↔ α.val ∈ I) :
    letI := D.comm
    ∃ (U : RootSubgroupFamily (Bp.pair h).T) (p : Specs.Pinning.Pinning A (Bp.pair h) U),
      ∀ (α : ↥(leviRoots D.datum I)) (i : SimpleRoot Q.pair) (j : SimpleRoot (Bp.pair h)),
        i.val = α.val → j.val = e α →
        pinnedRootMap p j ≫ S.inclusion = pinnedRootMap Q.pin i := by
  classical
  letI := D.comm
  letI := E.comm
  have subgroups (α : ↥(leviRoots D.datum I)) :=
    (faceRootRestrictions D I S α.val α.property).2 (Q.roots α.val).val (Q.roots α.val).property
  choose V hV r hr using subgroups
  let U : RootSubgroupFamily (Bp.pair h).T := fun β => ⟨V (e.symm β), by
    have hv := he (e.symm β)
    rw [e.apply_symm_apply] at hv
    exact hv.symm ▸ hV (e.symm β)⟩
  let source (j : SimpleRoot (Bp.pair h)) : SimpleRoot Q.pair := ⟨(e.symm j.val).val, by
    apply (D.simple_iff _).mp
    apply S.simple
    apply (hpos (e.symm j.val)).mp
    rw [e.apply_symm_apply]
    exact (E.simple_iff _).mpr j.property⟩
  have marks (j : SimpleRoot (Bp.pair h)) :
      ∃ y : Specs.Pinning.RootCoordinate A (Bp.pair h).T (U j.val).val j.val.val,
        y.val.hom ≫ (U j.val).val.inclusion ≫ S.inclusion = pinnedRootMap Q.pin (source j) := by
    let α := e.symm j.val
    have hv : j.val.val = S.toAmbientTorus ≫ α.val.val := by
      simpa only [α, e.apply_symm_apply] using he α
    obtain ⟨y, hy⟩ := restrictRootCoordinate S α.val (Q.roots α.val).val (V α)
      (r α) (hr α) (Q.pin (source j))
    let y' : Specs.Pinning.RootCoordinate A S.torus (V α) j.val.val :=
      ⟨y.val, by
        change RootGroups.HasScalarAction S.torus j.val.val (y.val.hom ≫ (V α).inclusion)
        rw [hv]
        exact y.property⟩
    exact ⟨y', hy⟩
  choose p hp using marks
  refine ⟨U, p, ?_⟩
  intro α i j hi hj
  have hs : source j = i := Subtype.ext (by
    change (e.symm j.val).val = i.val
    rw [hj, e.symm_apply_apply, hi])
  rw [← hs]
  exact hp j

set_option maxHeartbeats 1000000 in
/-- The two rational scheme intersections give the opposite Borels of the
derived standard Levi, with the restricted roots, coroots and pinning. -/
theorem rationalDerivedRootComparison : RationalDerivedRootComparison.{u} := by
  classical
  intro F K _ _ _ _ _ A₀ A Q D I S R a m ω hAction
  letI := D.comm
  let E₀ := groupBaseChange F K
  let Cn := transportSubgroup R.groupComparison (extendSubgroup K R.negative)
  let b : E₀.obj R.negative.group ≅ Cn.group := Iso.refl _
  have hb : b.hom ≫ Cn.inclusion = E₀.map R.negative.inclusion ≫ R.groupComparison.hom := by
    change (𝟙 _) ≫ (E₀.map R.negative.inclusion ≫ R.groupComparison.hom) = _
    rw [Category.id_comp]
  have hn : IsKBorel Cn := compared_borel_ascent (G := R.ambient) (H := Q.pair.G)
    R.ambientReductive R.negative Cn R.groupComparison b hb R.negativeBorel
  have hTn : IsSubgroupOf Q.pair.T Cn := by
    refine ⟨R.ambientTorusComparison.inv ≫ E₀.map R.negativeTorus, ?_⟩
    change (R.ambientTorusComparison.inv ≫ E₀.map R.negativeTorus) ≫
      E₀.map R.negative.inclusion ≫ R.groupComparison.hom = Q.pair.T.inclusion
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← R.opposite.w, R.positiveTorusSquare]
    change R.ambientTorusComparison.inv ≫
      ((groupBaseChange F K).map R.ambientTorus.inclusion ≫ R.groupComparison.hom) = _
    rw [← R.ambientTorusSquare, Iso.inv_hom_id_assoc]
  obtain ⟨Bp, j, hj⟩ := inducedBorel R R.positive Q.pair.B R.positiveComparison R.positiveSquare
    Q.pair.borel Q.pair.containsTorus
  obtain ⟨Bn, _, _⟩ := inducedBorel R R.negative Cn b hb hn hTn
  obtain ⟨ip, in', hop, ht⟩ := inducedOpposite Bp Bn
  obtain ⟨_, _, hsop, hst⟩ := splitInducedOpposite Bp Bn hop ht
  let h := splitFace_reductive S
  obtain ⟨E⟩ := Classification.Pinning.datumExists (Bp.pair h)
  obtain ⟨En⟩ := Classification.Pinning.datumExists (Bn.pair h)
  letI := E.comm
  letI := En.comm
  obtain ⟨e, he⟩ := faceRootEquivalence S
  have hpos := face_positive_base Bp E j hj e he
  have hneg := face_negative_base Bp Bn E En e he hpos hsop hst
  have hcoroot (α : ↥(leviRoots D.datum I)) :
      (E.datum.rootDatum.coroot (e α)).toMul ≫ S.toAmbientTorus =
        (D.datum.rootDatum.coroot α.val).toMul := by
    have hβ := (faceRootRestrictions D I S α.val α.property).1
    have hEq : (⟨S.toAmbientTorus ≫ α.val.val, hβ⟩ : Root (G := S.group) S.torus) = e α :=
      Subtype.ext (he α).symm
    apply faceAttachedCoroots D I S α.val α.property hβ _
    rw [hEq]
    exact E.datum.attached (e α)
  obtain ⟨U, p, hp⟩ := face_pinning Q Bp E e he hpos
  refine ⟨h, Bp, Bn, E, En, e, ⟨ip, in', hop, ht⟩,
    rationalDerivedSimplyConnected D I S R, ?_, ?_, U, p, hp, ?_⟩
  · intro σ α
    exact faceDiagram_stable ω hAction.stable σ α.val α.property
  · intro α
    refine ⟨he α, hcoroot α, hpos α, hneg α, ?_⟩
    rw [he α]
    exact (faceRootRestrictions D I S α.val α.property).2
  · intro σ α α' hα'
    have ha := rationalRootMarkAction Q D I S R a m ω hAction σ α.val
    dsimp only at ha
    refine ⟨?_, ?_, ?_⟩
    · rw [he α, he α', hα']
      exact ha.1
    · apply ha.2.1 _ _ (hcoroot α)
      rw [← hα']
      exact hcoroot α'
    · intro i j j' hi hj hj'
      have hi' : (diagramSimple ω σ i).val = α'.val := by
        change diagramRoot ω σ i.val = α'.val
        rw [hi, hα']
      exact ha.2.2 i _ _ hi (hp α i j hi hj) (hp α' _ j' hi' hj')

end Descent

end
end LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitDerivedRoots
