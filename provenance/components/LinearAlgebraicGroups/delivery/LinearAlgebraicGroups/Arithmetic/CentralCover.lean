import Specs.LinearAlgebraicGroups.Arithmetic.CentralCover
import LinearAlgebraicGroups.Arithmetic.CentralCoverDescent
import LinearAlgebraicGroups.Arithmetic.CentralCoverSpreading
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Reductive.TorusCentralizer
import LinearAlgebraicGroups.Descent.AutomorphismSequence
import LinearAlgebraicGroups.RootData.SchemeCentre
import LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Arithmetic.CentralCover

open _root_.LinearAlgebraicGroups.Specs Specs.CentralCover Specs.DiagonalizableGroups Specs.CentralIsogenies
open Specs.CharacterDescent (Character)
open Specs.SchemeCentre (CentreFormula)
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTorus IsMaximalTorus
  IsTrivialSubgroup baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.IntegralCentralQuotient (OverBase)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.SchemeDerivedGroup (IsSubgroupOf RepresentsQuotient)
open LinearAlgebraicGroups.Classification.CentralIsogenies
open LinearAlgebraicGroups.DiagonalizableGroups

open private schemeKernel_sections isMonHom_of_comp_closed
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private diagonalIso diagonalCharacterMap groupAlgebraMap_comp from LinearAlgebraicGroups.Classification.CentralIsogenies

set_option linter.style.haveILetI false

noncomputable section

private theorem finite_scheme_discrete {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] :
    DiscreteTopology X := by
  letI : IsAffine X := isAffine_of_isAffineHom f
  let R : CommRingCat := Γ(X, ⊤)
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  let g : CommRingCat.of k ⟶ R := e.inv ≫ f.appTop
  have hfin : g.hom.Finite := (f.finite_appTop).comp
    (RingHom.Finite.of_surjective _ e.commRingCatIsoToRingEquiv.symm.surjective)
  letI : Algebra k R := g.hom.toAlgebra
  letI : Module.Finite k R := hfin
  have hA : IsArtinianRing R := isArtinian_of_tower k inferInstance
  haveI : IsLocallyArtinian (Spec R) := Scheme.isLocallyArtinianScheme_Spec.mpr hA
  exact X.isoSpec.hom.homeomorph.symm.discreteTopology

set_option backward.isDefEq.respectTransparency false in
theorem finiteTargetRigidity : FiniteTargetRigidity.{u} := by
  intro k _ G H hred hconn hfin f hf
  letI := hred
  letI := hconn
  letI := hfin
  letI : DiscreteTopology H.X.left := finite_scheme_discrete H.X.hom
  letI : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let e : (𝟙_ (SchemeOver k)) ⟶ H.X := η[H.X]
  let eG : (𝟙_ (SchemeOver k)) ⟶ G.X := η[G.X]
  let t : (𝟙_ (SchemeOver k)).left := IsLocalRing.closedPoint k
  have hpoint (x : G.X.left) : f.left x = e.left t := by
    have hmap := (isPreconnected_univ.image f.left f.left.continuous.continuousOn).subsingleton
    have eq : f.left x = f.left (eG.left t) :=
      hmap ⟨x, Set.mem_univ _, rfl⟩ ⟨eG.left t, Set.mem_univ _, rfl⟩
    exact eq.trans (congrArg (fun z : (𝟙_ (SchemeOver k)) ⟶ H.X => z.left t) hf)
  apply Over.OverMorphism.ext
  change f.left = G.X.hom ≫ e.left
  apply (cancel_mono H.X.left.isoSpec.hom).mp
  simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]
  congr 1
  suffices h : f.left.appTop = (G.X.hom ≫ e.left).appTop by rw [h]
  -- Compare global pullbacks by subtracting their value along the identity.
  apply CommRingCat.hom_ext
  ext a
  let a₀ := a - H.X.hom.appTop (e.left.appTop a)
  have hw : e.left ≫ H.X.hom = 𝟙 _ := e.w
  have hzero : e.left.appTop a₀ = 0 := by
    have h := congrArg (fun v => Scheme.Hom.appTop v (e.left.appTop a)) hw
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.comp_apply,
      CommRingCat.id_apply] at h
    change e.left.appTop (a - H.X.hom.appTop (e.left.appTop a)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h.symm
  have hopen : e.left ⁻¹ᵁ H.X.left.basicOpen a₀ = ⊥ := by
    rw [Scheme.preimage_basicOpen_top, hzero, Scheme.basicOpen_zero]
  have hbot : G.X.left.basicOpen (f.left.appTop a₀) = ⊥ := by
    rw [← Scheme.preimage_basicOpen_top]
    apply le_antisymm _ bot_le
    intro x hx
    change f.left x ∈ H.X.left.basicOpen a₀ at hx
    rw [hpoint] at hx
    have ht : t ∈ e.left ⁻¹ᵁ H.X.left.basicOpen a₀ := hx
    rw [hopen] at ht
    exact ht.elim
  have hz := eq_zero_of_basicOpen_eq_bot _ hbot
  have hwf : f.left ≫ H.X.hom = G.X.hom := f.w
  have hc := congrArg (fun v => Scheme.Hom.appTop v (e.left.appTop a)) hwf
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hc
  change f.left.appTop (a - H.X.hom.appTop (e.left.appTop a)) = 0 at hz
  rw [map_sub] at hz
  change f.left.appTop a = (G.X.hom ≫ e.left).appTop a
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact (sub_eq_zero.mp hz).trans hc

set_option backward.isDefEq.respectTransparency false in
theorem uniqueLift : UniqueLift.{u} := by
  intro k _ G H J hred hconn q hq a b hab
  obtain ⟨hfin, _, _, N, hN, _⟩ := hq
  letI : IsFinite q.hom.hom.left := hfin
  have hpb := (Over.forget (Spec (CommRingCat.of k))).map_isPullback hN
  letI : IsFinite N.group.X.hom := MorphismProperty.of_isPullback hpb hfin
  have heq : a.hom.hom ≫ q.hom.hom = b.hom.hom ≫ q.hom.hom :=
    congrArg (fun c : G ⟶ J => c.hom.hom) hab
  have hdiff : (a.hom.hom⁻¹ * b.hom.hom) ≫ q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, heq, inv_mul_cancel]
  obtain ⟨d, hd⟩ := (schemeKernel_sections hN _).mpr hdiff
  change d ≫ N.inclusion.hom.hom = a.hom.hom⁻¹ * b.hom.hom at hd
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hd1 : η[G.X] ≫ d = η[N.group.X] := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    rw [Category.assoc, hd, MonObj.comp_mul, GrpObj.comp_inv]
    rw [IsMonHom.one_hom, IsMonHom.one_hom, IsMonHom.one_hom]
    exact inv_mul_cancel _
  have e := finiteTargetRigidity G N.group hred hconn inferInstance d hd1
  apply Grp.hom_ext
  have hz : a.hom.hom⁻¹ * b.hom.hom = 1 := by rw [← hd, e, MonObj.one_comp]
  exact inv_mul_eq_one.mp hz

set_option backward.isDefEq.respectTransparency false in
private theorem kernelTorsorSquareOverRing {R : Type u} [CommRing R] {G H N : Grp (OverBase R)}
    (q : G ⟶ H) (j : N ⟶ G) (hjc : IsClosedImmersion j.hom.hom.left)
    (hN : IsPullback j.hom.hom (toUnit N.X) q.hom.hom η[H.X]) :
    IsPullback (fst G.X N.X) (fst G.X N.X * (snd G.X N.X ≫ j.hom.hom))
      q.hom.hom q.hom.hom := by
  let p := fst G.X N.X
  let z := snd G.X N.X
  let i := j.hom.hom
  have hj : i ≫ q.hom.hom = 1 := by exact hN.w
  have hcomm : p ≫ q.hom.hom = (p * (z ≫ i)) ≫ q.hom.hom := by
    rw [MonObj.mul_comp, Category.assoc, hj, MonObj.comp_one, mul_one]
  letI := hjc
  letI : Mono i := Over.mono_of_mono_left _
  let d (c : PullbackCone q.hom.hom q.hom.hom) : c.pt ⟶ N.X :=
    hN.lift (c.fst⁻¹ * c.snd) (toUnit c.pt) (by
      change (c.fst⁻¹ * c.snd) ≫ q.hom.hom = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, c.condition, inv_mul_cancel])
  have hd (c : PullbackCone q.hom.hom q.hom.hom) : d c ≫ i = c.fst⁻¹ * c.snd :=
    hN.lift_fst _ _ _
  refine IsPullback.mk ⟨hcomm⟩ ⟨PullbackCone.IsLimit.mk _ (fun c => lift c.fst (d c))
    (fun c => lift_fst _ _) ?_ ?_⟩
  · intro c
    rw [MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd, hd, mul_inv_cancel_left]
  · intro c f hf hg
    apply CartesianMonoidalCategory.hom_ext _ _
    · rw [lift_fst]
      exact hf
    · apply (cancel_mono i).mp
      change (f ≫ z) ≫ i = (lift c.fst (d c) ≫ z) ≫ i
      rw [show lift c.fst (d c) ≫ z = d c from lift_snd _ _, hd]
      rw [MonObj.comp_mul, hf] at hg
      exact (eq_inv_mul_iff_mul_eq).mpr (by simpa only [Category.assoc] using hg)

theorem kernelTorsorSquare : KernelTorsorSquare.{u} := by
  intro k _ G H q N hN
  exact kernelTorsorSquareOverRing q N.inclusion N.isClosedImmersion hN

theorem finiteKernelTorsorOfKernel : FiniteKernelTorsorOfKernel.{u} := by
  intro R _ G H Z q j hf hflat hsurj hfp hj hk
  exact ⟨hf, hflat, hsurj, hfp, hj, hk, kernelTorsorSquareOverRing q j hj hk⟩

theorem genericFibreImage : GenericFibreImage.{u} := by
  intro R E _ _ _ _ _ X Y f hf j
  letI := hf
  let a := Spec.map (CommRingCat.ofHom (algebraMap R E))
  letI : IsDominant a := by
    apply (isDominant_iff a).mpr
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := algebraMap R E)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R E)]
    exact bot_le
  letI := IsSchemeTheoreticallyDominant.of_isDominant a
  change (pullback.fst f a ≫ j).ker = j.ker
  rw [Scheme.Hom.ker_comp, (pullback.fst f a).ker_eq_bot, Scheme.IdealSheafData.map_bot]

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private finiteProductHomEquiv cyclicHomEquiv
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_is_central {k : Type u} [Field k] {G H : GroupScheme k}
    {q : G ⟶ H} (hq : IsCentralIsogeny q) {N : ClosedSubgroup G}
    (hN : IsSchemeKernel q N) : Centralizes (𝟙 G) N.inclusion.hom.hom := by
  obtain ⟨_, _, _, N₀, hN₀, hz₀⟩ := hq
  obtain ⟨d, hd⟩ := (schemeKernel_sections hN₀ N.inclusion.hom.hom).mpr
    (show N.inclusion.hom.hom ≫ q.hom.hom = 1 from hN.w)
  change d ≫ N₀.inclusion.hom.hom = N.inclusion.hom.hom at hd
  exact (centralizes_iff _ _).mpr (fun Y t g => by
    rw [← hd]
    exact (Category.assoc t (show N.group.X ⟶ N₀.group.X from d) N₀.inclusion.hom.hom) ▸
      (centralizes_iff _ _).mp hz₀ Y (t ≫ d) g)

set_option backward.isDefEq.respectTransparency false in
theorem splitKernelCharacters : SplitKernelCharacters.{u} := by
  intro k _ G H hG hH T S hsT hmT hsS hmS q qT hq hqT N hN
  let centre : CentreFormula.{u} := RootData.SchemeCentre.schemeCentre
  obtain ⟨hi, hfin⟩ := finiteIndexCharacterPullback centre G H hG hH T S hsT hmT hsS hmS
    q qT hq hqT
  let l := characterPullback qT
  refine ⟨hi, hfin, ?_⟩
  have hNZ := kernel_is_central hq hN
  obtain ⟨n, hn⟩ := kernel_le_maximalTorus centre G hG T hsT hmT N hNZ
  obtain ⟨hfg, eT, heT, _⟩ := centre G hG T hsT hmT
  obtain ⟨_, eS, heS, _⟩ := centre H hH S hsS hmS
  letI := hfg
  let j : Character S.group ≃* l.range :=
    MulEquiv.ofBijective l.rangeRestrict ⟨fun x y h => hi (congrArg Subtype.val h),
      fun ⟨x, hx⟩ => by obtain ⟨y, rfl⟩ := hx; exact ⟨y, rfl⟩⟩
  let i := diagonalIso (k := k) j
  let D := specGroup (groupAlgebra k (Character T.group ⧸ l.range))
  obtain ⟨hc, _, _, _, hD, _⟩ := diagonalRestrictionKernelAndQuotient k _ l.range
  let DD : ClosedSubgroup (specGroup (groupAlgebra k (Character T.group))) :=
    ⟨D, diagonalClosedInclusion k l.range, hc⟩
  change IsSchemeKernel (diagonalRestriction k l.range) DD at hD
  have he : diagonalRestriction k l.range ≫ i.hom ≫ eS.hom = eT.hom ≫ qT := by
    rw [← Category.assoc]
    have hcomp : diagonalRestriction k l.range ≫ i.hom =
        specGroupMap (groupAlgebraMap k l) := by
      change specGroupMap (groupAlgebraMap k l.range.subtype) ≫
        specGroupMap (groupAlgebraMap k j.toMonoidHom) = _
      rw [← specGroupMap_comp, groupAlgebraMap_comp]
      rfl
    rw [hcomp, diagonalCharacterMap qT eT eS heT heS]
  let iD := DD.inclusion ≫ eT.hom ≫ T.inclusion
  have hiD : IsClosedImmersion iD.hom.hom.left := by
    letI : IsClosedImmersion DD.inclusion.hom.hom.left := hc
    letI := T.isClosedImmersion
    letI : IsIso eT.hom.hom.hom.left :=
      (Grp.forget (SchemeOver k) ⋙ Over.forget _).map_isIso eT.hom
    change IsClosedImmersion
      (DD.inclusion.hom.hom.left ≫ eT.hom.hom.hom.left ≫ T.inclusion.hom.hom.left)
    infer_instance
  have hDq : iD.hom.hom ≫ q.hom.hom = 1 := by
    change (DD.inclusion.hom.hom ≫ eT.hom.hom.hom ≫ T.inclusion.hom.hom) ≫ q.hom.hom = _
    have eqT := congrArg (fun x : T.group ⟶ H.val => x.hom.hom) hqT.1
    have eqD := congrArg (Grp.forget (SchemeOver k)).map he
    simp only [Functor.map_comp] at eqD
    change qT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom at eqT
    change (diagonalRestriction k l.range).hom.hom ≫ i.hom.hom.hom ≫ eS.hom.hom.hom =
      eT.hom.hom.hom ≫ qT.hom.hom at eqD
    simp only [Category.assoc]
    rw [← eqT, ← Category.assoc eT.hom.hom.hom qT.hom.hom, ← eqD]
    simp only [Category.assoc]
    rw [← Category.assoc DD.inclusion.hom.hom, show DD.inclusion.hom.hom ≫
      (diagonalRestriction k l.range).hom.hom = 1 from hD.w]
    simp only [MonObj.one_comp]
  obtain ⟨a, ha⟩ := (schemeKernel_sections hN iD.hom.hom).mpr hDq
  haveI := S.isClosedImmersion
  letI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  have hn' : n.hom.hom ≫ T.inclusion.hom.hom = N.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hn
  have hqT' : qT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hqT.1
  have hnq : n.hom.hom ≫ qT.hom.hom = 1 := by
    apply (cancel_mono S.inclusion.hom.hom).mp
    rw [Category.assoc, hqT', ← Category.assoc, hn', MonObj.one_comp]
    exact hN.w
  have heTinv : eT.inv.hom.hom ≫ eT.hom.hom.hom = 𝟙 T.group.X :=
    ((Grp.forget (SchemeOver k)).mapIso eT).inv_hom_id
  let x := n.hom.hom ≫ eT.inv.hom.hom
  let e := (Grp.forget (SchemeOver k)).mapIso (i ≪≫ eS)
  have hx : x ≫ (diagonalRestriction k l.range).hom.hom = 1 := by
    apply (cancel_mono e.hom).mp
    have h := congrArg (Grp.forget (SchemeOver k)).map he
    simp only [Functor.map_comp] at h
    change (diagonalRestriction k l.range).hom.hom ≫ i.hom.hom.hom ≫ eS.hom.hom.hom =
      eT.hom.hom.hom ≫ qT.hom.hom at h
    change (x ≫ (diagonalRestriction k l.range).hom.hom) ≫
      (i.hom.hom.hom ≫ eS.hom.hom.hom) = 1 ≫ (i.hom.hom.hom ≫ eS.hom.hom.hom)
    rw [Category.assoc, h, MonObj.one_comp]
    change (n.hom.hom ≫ eT.inv.hom.hom) ≫ eT.hom.hom.hom ≫ qT.hom.hom = _
    rw [Category.assoc, ← Category.assoc eT.inv.hom.hom, heTinv, Category.id_comp, hnq]
  obtain ⟨b, hb⟩ := (schemeKernel_sections hD x).mpr hx
  change b ≫ DD.inclusion.hom.hom = x at hb
  change a ≫ N.inclusion.hom.hom = iD.hom.hom at ha
  have hb' : b ≫ iD.hom.hom = N.inclusion.hom.hom := by
    change b ≫ DD.inclusion.hom.hom ≫ eT.hom.hom.hom ≫ T.inclusion.hom.hom = _
    rw [← Category.assoc, hb]
    change (n.hom.hom ≫ eT.inv.hom.hom) ≫ eT.hom.hom.hom ≫ T.inclusion.hom.hom = _
    rw [Category.assoc, ← Category.assoc eT.inv.hom.hom, heTinv, Category.id_comp, hn']
  letI := N.isClosedImmersion
  letI := hiD
  letI : IsMonHom a := isMonHom_of_comp_closed a iD N.inclusion ha
  letI : IsMonHom b := isMonHom_of_comp_closed b N.inclusion iD hb'
  letI : Mono iD.hom.hom := Over.mono_of_mono_left _
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  exact ⟨⟨Grp.homMk b, Grp.homMk a,
    Grp.hom_ext _ _ ((cancel_mono N.inclusion.hom.hom).mp (by
      change (b ≫ a) ≫ N.inclusion.hom.hom = 𝟙 _ ≫ N.inclusion.hom.hom
      rw [Category.assoc, ha, hb', Category.id_comp])),
    Grp.hom_ext _ _ ((cancel_mono iD.hom.hom).mp (by
      change (a ≫ b) ≫ iD.hom.hom = 𝟙 _ ≫ iD.hom.hom
      rw [Category.assoc, hb', ha, Category.id_comp]))⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem globalFieldExtension : GlobalFieldExtension.{u, v} := by
  intro K E _ _ _ _ _ D
  cases D with
  | number h =>
    letI := h
    letI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
    letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ K E
    exact ⟨.number (NumberField.mk)⟩
  | function F t =>
    letI : Algebra F E := ((algebraMap K E).comp (algebraMap F K)).toAlgebra
    letI : IsScalarTower F K E := IsScalarTower.of_algebraMap_eq' rfl
    let φ := IsScalarTower.toAlgHom F K E
    let a := φ t.element
    have ha : Transcendental F a :=
      (transcendental_algebraMap_iff (algebraMap K E).injective).mpr t.transcendental
    let B := IntermediateField.adjoin F {t.element}
    let B' := IntermediateField.adjoin F {a}
    have himage : B.map φ = B' := by
      change (IntermediateField.adjoin F {t.element}).map φ = _
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    let e : B ≃ₐ[F] B' := (B.equivMap φ).trans (IntermediateField.equivOfEq himage)
    letI : Module.Finite B K := t.finite
    letI : Algebra.IsSeparable B K := t.separable
    letI : Module.Finite B E := Module.Finite.trans K E
    letI : Algebra.IsSeparable B E := Algebra.IsSeparable.trans B K E
    have he : (algebraMap B' E).comp e.toRingEquiv.toRingHom =
        (RingEquiv.refl E).toRingHom.comp (algebraMap B E) := by
      ext x
      change ((IntermediateField.equivOfEq himage (B.equivMap φ x) : B') : E) = _
      rw [IntermediateField.equivOfEq_apply]
      rfl
    exact ⟨.function F ⟨a, ha, Module.Finite.of_equiv_equiv e.toRingEquiv (.refl E) he,
      Algebra.IsSeparable.of_equiv_equiv e.toRingEquiv (.refl E) he⟩⟩

theorem finiteCoefficientsIntegral : FiniteCoefficientsIntegral.{u, v} := by
  intro E _ D B C hB hC
  let bad (a : E) : Set D.FinitePlace := {w | D.embedding (.inl w) a ∉ D.integers w}
  let S := B ∪ ⋃ a ∈ C, bad a
  refine ⟨S, hB.union (hC.biUnion fun a _ => D.finite_nonintegral a), Set.subset_union_left, ?_⟩
  intro a ha
  apply Subring.mem_iInf.mpr
  intro w
  change D.embedding (.inl w.val) a ∈ D.integers w.val
  by_contra hn
  exact w.property (Or.inr (Set.mem_biUnion ha hn))

open private monomialEquiv characterIso from LinearAlgebraicGroups.Classification.CentralIsogenies

set_option backward.isDefEq.respectTransparency false in
theorem characterSmithBases : CharacterSmithBases.{u} := by
  classical
  intro k _ T S q hT hi hfin
  obtain ⟨r, ⟨e⟩⟩ := hT
  obtain ⟨a⟩ := diagonalIntegerPowers k (ULift.{u} (Fin r))
  let l := characterPullback q
  let N := l.range.toAddSubgroup.toIntSubmodule
  let j : Character S ≃* l.range :=
    MulEquiv.ofBijective l.rangeRestrict ⟨fun x y h => hi (congrArg Subtype.val h),
      fun ⟨x, hx⟩ => by obtain ⟨y, rfl⟩ := hx; exact ⟨y, rfl⟩⟩
  let j' : Additive (Character S) ≃ₗ[ℤ] N := j.toAdditive.toIntLinearEquiv
  let b := (monomialEquiv (k := k) (Multiplicative (ULift.{u} (Fin r) → ℤ))).trans
    (characterIso (a ≪≫ e.symm))
  let bL : (ULift.{u} (Fin r) → ℤ) ≃ₗ[ℤ] Additive (Character T) :=
    b.toAdditive.toIntLinearEquiv
  let B := ((Pi.basisFun ℤ (ULift.{u} (Fin r))).map bL).reindex Equiv.ulift
  letI : Module.Free ℤ (Additive (Character T)) := Module.Free.of_basis B
  letI : Module.Finite ℤ (Additive (Character T)) := Module.Finite.of_basis B
  have hN : Finite (Additive (Character T) ⧸ N) := hfin
  have hr := (Submodule.finiteQuotient_iff N).mp hN
  obtain ⟨c, d, f, hf⟩ := N.exists_smith_normal_form_of_rank_eq B hr
  have hd (i : Fin r) : d i ≠ 0 := by
    intro hz
    apply f.ne_zero i
    apply Subtype.ext
    rw [hf, hz, zero_smul]
    rfl
  have hs (i : Fin r) : IsUnit (Int.sign (d i)) := by
    rcases lt_or_gt_of_ne (hd i) with h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · simp [Int.sign_eq_one_of_pos h]
  let f' := (f.isUnitSMul hs).map j'.symm
  refine ⟨r, c, f', fun i => (d i).natAbs, fun i => Int.natAbs_pos.mpr (hd i), ?_⟩
  intro i
  change ((j' (f' i) : N) : Additive (Character T)) = _
  rw [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.isUnitSMul_apply]
  rw [Submodule.coe_smul, hf, smul_smul, Int.sign_mul_self_eq_natAbs]


open private intHomEquiv pointsIso_precompose
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

private def basisCharacterEquiv {M : Type u} [CommGroup M] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ (Additive M)) :
    M ≃* (Fin r → Multiplicative ℤ) :=
  b.equivFun.toAddEquiv.toMultiplicative.trans (MulEquiv.piMultiplicative _)

private def basisPointsIso {k : Type u} [Field k] {M : Type u} [CommGroup M] {r : ℕ}
    (b : Module.Basis (Fin r) ℤ (Additive M)) :
    characterValuedPoints k M ≅ torusCoordinates (k := k) (Fin r) := by
  let e := basisCharacterEquiv b
  refine NatIso.ofComponents (fun R => ?_) ?_
  · let a : (M →* Rˣ) ≃* ((Fin r → Multiplicative ℤ) →* Rˣ) :=
      { toFun := fun f => f.comp e.symm.toMonoidHom
        invFun := fun g => g.comp e.toMonoidHom
        left_inv := by intro f; ext x; simp
        right_inv := by intro f; ext x; simp
        map_mul' := fun _ _ => rfl }
    exact (a.trans ((finiteProductHomEquiv (fun _ : Fin r => Multiplicative ℤ) Rˣ).trans
      (MulEquiv.piCongrRight fun _ => intHomEquiv Rˣ))).toGrpIso
  · intro R S f
    apply GrpCat.ext
    intro x
    rfl

private theorem basisPointsIso_eval {k : Type u} [Field k] {M : Type u} [CommGroup M]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ (Additive M)) (R : TestAlgebra k)
    (f : M →* Rˣ) (i : Fin r) :
    (show Fin r → Rˣ from (basisPointsIso b).hom.app R f) i = f (b i).toMul := by
  change f ((basisCharacterEquiv b).symm (Pi.mulSingle i (Multiplicative.ofAdd 1))) = _
  congr 1
  apply (basisCharacterEquiv b).injective
  rw [MulEquiv.apply_symm_apply]
  ext j
  change (Pi.mulSingle i (Multiplicative.ofAdd 1) : Fin r → Multiplicative ℤ) j =
    Multiplicative.ofAdd (b.equivFun (b i) j)
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h, ← ofAdd_zero]

set_option backward.isDefEq.respectTransparency false in
theorem splitTorusPowerCoordinates : SplitTorusPowerCoordinates.{u} := by
  intro k _ G H hG hH T S hsT hmT hsS hmS q qT hq hqT
  let centre : CentreFormula.{u} := RootData.SchemeCentre.schemeCentre
  obtain ⟨hi, hfin⟩ := finiteIndexCharacterPullback centre G H hG hH T S hsT hmT hsS hmS
    q qT hq hqT
  obtain ⟨r, bT, bS, n, hn, hb⟩ := characterSmithBases qT hsT hi hfin
  refine ⟨r, n, hn, ?_⟩
  obtain ⟨_, eT, hT, _⟩ := centre G hG T hsT hmT
  obtain ⟨_, eS, hS, _⟩ := centre H hH S hsS hmS
  let F := groupPointsFunctor k
  let ΦT := groupAlgebraPointsIso k (Character T.group)
  let ΦS := groupAlgebraPointsIso k (Character S.group)
  refine ⟨F.mapIso eT.symm ≪≫ ΦT ≪≫ basisPointsIso bT,
    F.mapIso eS.symm ≪≫ ΦS ≪≫ basisPointsIso bS, ?_⟩
  intro R x i
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((F.mapIso eT).hom.app R)).2 x
  have he := diagonalCharacterMap qT eT eS hT hS
  let L := specGroupMap (groupAlgebraMap k (characterPullback qT))
  have hq' : eT.hom ≫ qT ≫ eS.inv = L := by
    rw [← Category.assoc, he, Category.assoc, eS.hom_inv_id, Category.comp_id]
  change (show Fin r → Rˣ from (basisPointsIso bS).hom.app R
    (ΦS.hom.app R ((F.map eS.inv).app R ((F.map qT).app R ((F.map eT.hom).app R x))))) i =
    (show Fin r → Rˣ from (basisPointsIso bT).hom.app R
      (ΦT.hom.app R ((F.map eT.inv).app R ((F.map eT.hom).app R x)))) i ^ n i
  rw [basisPointsIso_eval, basisPointsIso_eval]
  have hQ : (F.map eS.inv).app R ((F.map qT).app R ((F.map eT.hom).app R x)) =
      (F.map L).app R x := by
    rw [← hq', Functor.map_comp, Functor.map_comp]
    rfl
  have hX : (F.map eT.inv).app R ((F.map eT.hom).app R x) = x := by
    have hh := congrArg F.map eT.hom_inv_id
    rw [F.map_comp, F.map_id] at hh
    exact congrArg (fun w => w.app R x) hh
  rw [hQ, hX]
  change (show Character S.group →* Rˣ from ΦS.hom.app R ((F.map L).app R x)) (bS i).toMul =
    (show Character T.group →* Rˣ from ΦT.hom.app R x) (bT i).toMul ^ n i
  rw [pointsIso_precompose]
  have hb' : characterPullback qT (bS i).toMul = (bT i).toMul ^ n i := by
    have h := congrArg Additive.toMul (hb i)
    change characterPullback qT (bS i).toMul = (bT i).toMul ^ (n i : ℤ) at h
    simpa only [zpow_natCast] using h
  rw [hb', map_pow]


set_option backward.isDefEq.respectTransparency false in
private theorem kernelPowerFactors {k : Type u} [Field k] {G H : GroupScheme k}
    {T : ClosedSubgroup H} {S : ClosedSubgroup G} {q : H ⟶ G} {qT : T.group ⟶ S.group}
    (hqT : IsTorusRestriction q qT) {N : ClosedSubgroup H} (hN : IsSchemeKernel q N)
    (j : N.group ⟶ T.group) (hj : j ≫ T.inclusion = N.inclusion)
    {I : Type} {n : I → ℕ} (h : HasPowerCoordinates qT n) :
    Nonempty ((groupPointsFunctor k).obj N.group ≅ splitProductPoints k PEmpty I n) := by
  obtain ⟨eT, eS, he⟩ := h
  let F := groupPointsFunctor k
  let I₀ := Grp.forget (SchemeOver k)
  have hj' : j.hom.hom ≫ T.inclusion.hom.hom = N.inclusion.hom.hom :=
    congrArg I₀.map hj
  have hqT' : qT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg I₀.map hqT.1
  letI := S.isClosedImmersion
  letI := N.isClosedImmersion
  letI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hjq : j.hom.hom ≫ qT.hom.hom = 1 := by
    apply (cancel_mono S.inclusion.hom.hom).mp
    rw [Category.assoc, hqT', ← Category.assoc, hj', MonObj.one_comp]
    exact hN.w
  let Φ (R : TestAlgebra k) : (F.obj N.group).obj R →* (I → Rˣ) :=
    (eT.hom.app R).hom.comp ((F.map j).app R).hom
  have hroot (R : TestAlgebra k) (x : (F.obj N.group).obj R) (i : I) : Φ R x i ^ n i = 1 := by
    have h := (he R ((F.map j).app R x) i).symm
    have hz : (F.map qT).app R ((F.map j).app R x) = 1 := by
      change (x ≫ j.hom.hom) ≫ qT.hom.hom = 1
      rw [Category.assoc, hjq, MonObj.comp_one]
    rw [hz, map_one] at h
    exact h
  let Ψ (R : TestAlgebra k) : (F.obj N.group).obj R →* (splitProductPoints k PEmpty I n).obj R :=
    { toFun := fun x => (1, fun i => ⟨Φ R x i, hroot R x i⟩)
      map_one' := by apply Prod.ext; rfl; funext i; apply Subtype.ext; exact congrFun (map_one (Φ R)) i
      map_mul' := by
        intro x y
        apply Prod.ext
        · exact (one_mul _).symm
        · funext i
          apply Subtype.ext
          exact congrFun (map_mul (Φ R) x y) i }
  have hbij (R : TestAlgebra k) : Function.Bijective (Ψ R) := by
    have hT := ConcreteCategory.bijective_of_isIso (eT.hom.app R)
    have hS := ConcreteCategory.bijective_of_isIso (eS.hom.app R)
    constructor
    · intro a b h
      have eq : Φ R a = Φ R b :=
        funext fun i => congrArg (fun z : (splitProductPoints k PEmpty I n).obj R =>
          ((z.2 i).val : Rˣ)) h
      have eq' : a ≫ j.hom.hom = b ≫ j.hom.hom := hT.1 eq
      change (a : Points N.group.X R) = b
      apply (cancel_mono N.inclusion.hom.hom).mp
      simpa only [Category.assoc, hj'] using
        congrArg (fun z => z ≫ T.inclusion.hom.hom) eq'
    · rintro ⟨f, roots⟩
      obtain ⟨t, ht⟩ := hT.2 (fun i => (roots i).val)
      have hp : (F.map qT).app R t = 1 := by
        apply hS.1
        rw [map_one]
        funext i
        calc
          _ = (show I → Rˣ from eT.hom.app R t) i ^ n i := he R t i
          _ = (roots i).val ^ n i := congrArg (· ^ n i) (congrFun ht i)
          _ = 1 := (roots i).property
      have hp' : t ≫ T.inclusion.hom.hom ≫ q.hom.hom = 1 := by
        rw [← hqT', ← Category.assoc]
        change t ≫ qT.hom.hom = 1 at hp
        rw [hp, MonObj.one_comp]
      obtain ⟨x, hx⟩ := (schemeKernel_sections hN
        (t ≫ T.inclusion.hom.hom : Points H.X R)).mpr (by rwa [Category.assoc])
      change x ≫ N.inclusion.hom.hom = t ≫ T.inclusion.hom.hom at hx
      letI := T.isClosedImmersion
      letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
      have hx' : x ≫ j.hom.hom = t := by
        apply (cancel_mono T.inclusion.hom.hom).mp
        rwa [Category.assoc, hj']
      refine ⟨x, Prod.ext (Subsingleton.elim _ _) ?_⟩
      funext i
      apply Subtype.ext
      change (show I → Rˣ from eT.hom.app R (x ≫ j.hom.hom)) i = (roots i).val
      rw [hx']
      exact congrFun ht i
  refine ⟨NatIso.ofComponents (fun R => (MulEquiv.ofBijective (Ψ R) (hbij R)).toGrpIso) ?_⟩
  intro R R' a
  apply GrpCat.ext
  intro x
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · funext i
    apply Subtype.ext
    have eq := congrArg
      (fun f : (F.obj T.group).obj R ⟶ (torusCoordinates (k := k) I).obj R' =>
        (show I → R'ˣ from f ((F.map j).app R x)) i) (eT.hom.naturality a)
    change (show I → R'ˣ from eT.hom.app R'
      (mapPoints a (x ≫ j.hom.hom))) i = Units.map a.hom.toMonoidHom (Φ R x i) at eq
    change (show I → R'ˣ from eT.hom.app R'
      (mapPoints a x ≫ j.hom.hom)) i = _
    rw [Category.assoc]
    exact eq


open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTorus IsMaximalTorus
  IsTrivialSubgroup baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.SubtorusCentralizer (IsCentralizer)
open Specs.IntegralCentralQuotient (OverBase)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_nontrivial_iff {k : Type u} [Field k] {H : AffineAlgebraicGroup k}
    (N : ClosedSubgroup H.val) {I : Type} {n : I → ℕ} (hn : ∀ i, 0 < n i)
    (e : (groupPointsFunctor k).obj N.group ≅ splitProductPoints k PEmpty I n) :
    (¬ IsTrivialSubgroup N) ↔ ∃ i, 1 < n i := by
  classical
  let F := groupPointsFunctor k
  constructor
  · intro hN
    by_contra! h
    have h1 (i : I) : n i = 1 := Nat.le_antisymm (h i) (hn i)
    have hs (R : TestAlgebra k) : Subsingleton ((splitProductPoints k PEmpty I n).obj R) := by
      change Subsingleton ((PEmpty → Rˣ) × (∀ i, rootsOfUnity (n i) R))
      haveI (i : I) : Subsingleton (rootsOfUnity (n i) R) := by
        rw [h1 i, rootsOfUnity_one]
        infer_instance
      infer_instance
    let p : N.group ⟶ Grp.trivial (SchemeOver k) := default
    let j : Grp.trivial (SchemeOver k) ⟶ N.group := default
    have hleft : IsAffine N.group.X.left := (Unipotent.closedSubgroupAlgebraicGroup N).property.1
    have hpj : p ≫ j = 𝟙 N.group := by
      apply Grp.hom_ext
      apply hom_ext_of_points hleft
      intro R x
      apply ((ConcreteCategory.bijective_of_isIso (e.hom.app R)).1)
      exact (hs R).elim _ _
    exact hN ⟨⟨p, j, hpj, Subsingleton.elim _ _⟩⟩
  · rintro ⟨i, hi⟩ ⟨e₀⟩
    haveI : Fact (1 < n i) := ⟨hi⟩
    let M := Multiplicative (ZMod (n i))
    let A := MonoidAlgebra k M
    let R := CommAlgCat.of k A
    let g : M := Multiplicative.ofAdd 1
    have hg : g ^ n i = 1 := by
      change Multiplicative.ofAdd ((n i) • (1 : ZMod (n i))) = Multiplicative.ofAdd 0
      simp [nsmul_eq_mul]
    let f := (MonoidAlgebra.of k M).toHomUnits
    let a : rootsOfUnity (n i) R := ⟨f g, by
      rw [mem_rootsOfUnity, ← map_pow, hg, map_one]⟩
    have ha : a ≠ 1 := by
      intro h
      have hv := congrArg (fun v : rootsOfUnity (n i) R => ((v.val : Rˣ) : R)) h
      change MonoidAlgebra.of k M g = (1 : A) at hv
      rw [← map_one (MonoidAlgebra.of k M)] at hv
      have hm : g = (1 : M) := MonoidAlgebra.of_injective hv
      exact (one_ne_zero : (1 : ZMod (n i)) ≠ 0) (congrArg Multiplicative.toAdd hm)
    let y : (splitProductPoints k PEmpty I n).obj R := (1, Function.update 1 i a)
    have hy : y ≠ 1 := by
      intro h
      apply ha
      have eq := congrArg (fun z : (splitProductPoints k PEmpty I n).obj R => z.2 i) h
      change Function.update (1 : ∀ i, rootsOfUnity (n i) R) i a i = (1 : rootsOfUnity (n i) R) at eq
      simpa only [Function.update_self] using eq
    let e' := (F.mapIso e₀.symm ≪≫ e).app R
    have hs : Subsingleton ((F.obj (Grp.trivial (SchemeOver k))).obj R) :=
      ⟨fun x y => (isTerminalTensorUnit (C := SchemeOver k)).hom_ext x y⟩
    apply hy
    exact ((ConcreteCategory.bijective_of_isIso e'.inv).1) (hs.elim _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem torusRestrictionKernel {k : Type u} [Field k] {G H : GroupScheme k}
    {T : ClosedSubgroup H} {S : ClosedSubgroup G} {q : H ⟶ G} {qT : T.group ⟶ S.group}
    (hqT : IsTorusRestriction q qT) {N : ClosedSubgroup H} (hN : IsSchemeKernel q N)
    (j : N.group ⟶ T.group) (hj : j ≫ T.inclusion = N.inclusion) :
    IsPullback j.hom.hom (toUnit N.group.X) qT.hom.hom η[S.group.X] := by
  let F := Grp.forget (SchemeOver k)
  have hj' : j.hom.hom ≫ T.inclusion.hom.hom = N.inclusion.hom.hom := congrArg F.map hj
  have hqT' : qT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg F.map hqT.1
  let := S.isClosedImmersion
  let := T.isClosedImmersion
  let := N.isClosedImmersion
  letI : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hc : j.hom.hom ≫ qT.hom.hom = toUnit N.group.X ≫ η[S.group.X] := by
    change j.hom.hom ≫ qT.hom.hom = 1
    apply (cancel_mono S.inclusion.hom.hom).mp
    rw [Category.assoc, hqT', ← Category.assoc, hj', MonObj.one_comp]
    exact hN.w
  let kernelCone (c : PullbackCone qT.hom.hom η[S.group.X]) : c.pt ⟶ N.group.X :=
    hN.lift (c.fst ≫ T.inclusion.hom.hom) (toUnit _) (by
      rw [Category.assoc, ← hqT', ← Category.assoc, c.condition, Category.assoc, IsMonHom.one_hom]
      exact congrArg (· ≫ η[G.X]) (toUnit_unique c.snd (toUnit c.pt)))
  have hKernelCone (c : PullbackCone qT.hom.hom η[S.group.X]) :
      kernelCone c ≫ N.inclusion.hom.hom = c.fst ≫ T.inclusion.hom.hom := hN.lift_fst _ _ _
  refine IsPullback.mk ⟨hc⟩ ⟨PullbackCone.IsLimit.mk _ kernelCone ?_ ?_ ?_⟩
  · intro c
    apply (cancel_mono T.inclusion.hom.hom).mp
    rw [Category.assoc, hj', hKernelCone]
  · intro c
    exact toUnit_unique _ _
  · intro c f hf _
    apply (cancel_mono N.inclusion.hom.hom).mp
    change f ≫ N.inclusion.hom.hom = kernelCone c ≫ N.inclusion.hom.hom
    calc
      f ≫ N.inclusion.hom.hom = f ≫ j.hom.hom ≫ T.inclusion.hom.hom :=
        congrArg (f ≫ ·) hj'.symm
      _ = (f ≫ j.hom.hom) ≫ T.inclusion.hom.hom := (Category.assoc _ _ _).symm
      _ = c.fst ≫ T.inclusion.hom.hom := congrArg (· ≫ T.inclusion.hom.hom) hf
      _ = kernelCone c ≫ N.inclusion.hom.hom := (hKernelCone c).symm

set_option backward.isDefEq.respectTransparency false in
theorem splitCoverDataExists : SplitCoverDataExists.{u} := by
  intro k _ G H hG hH T S hsT hmT hsS hmS q qT hq hqT N hN
  obtain ⟨r, n, hn, hp⟩ := splitTorusPowerCoordinates H G hH hG T S hsT hmT hsS hmS q qT hq hqT
  have hj := kernel_le_maximalTorus RootData.SchemeCentre.schemeCentre H hH T hsT hmT N
    (kernel_is_central hq hN)
  obtain ⟨j, hj'⟩ := hj
  obtain ⟨e⟩ := kernelPowerFactors hqT hN j hj' hp
  exact ⟨⟨T, S, hsT, hsS, hmT, hmS, qT, hqT, j, hj', torusRestrictionKernel hqT hN j hj',
    Fin r, inferInstance, n, hn, hp, ⟨e⟩, kernel_nontrivial_iff N hn e⟩⟩

section SchemeCoordinates

open private groupIsoOfPointIso from LinearAlgebraicGroups.Affine.IdentityTangent
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private def splitTorusPointsIso (I : Type) [Fintype I] [DecidableEq I] :
    (groupPointsFunctor k).obj (integralSplitTorus k I) ≅ torusCoordinates (k := k) I := by
  let M := ULift.{u} (Multiplicative (I → ℤ))
  change (groupPointsFunctor k).obj (specGroup (groupAlgebra k M)) ≅ torusCoordinates (k := k) I
  refine groupAlgebraPointsIso k M ≪≫ NatIso.ofComponents (fun R => ?_) ?_
  · let p : M ≃* (I → Multiplicative ℤ) :=
      MulEquiv.ulift.trans (MulEquiv.piMultiplicative (fun _ : I => ℤ))
    let e : (M →* Rˣ) ≃* ((I → Multiplicative ℤ) →* Rˣ) := p.monoidHomCongrLeft
    exact (e.trans ((finiteProductHomEquiv (fun _ : I => Multiplicative ℤ) Rˣ).trans
      (MulEquiv.piCongrRight fun _ => intHomEquiv Rˣ))).toGrpIso
  · intro R S a
    apply GrpCat.ext
    intro x
    rfl

private theorem splitTorusPointsIso_power {I : Type} [Fintype I] [DecidableEq I]
    (n : I → ℕ) (R : TestAlgebra k)
    (x : ((groupPointsFunctor k).obj (integralSplitTorus k I)).obj R) (i : I) :
    (show I → Rˣ from (splitTorusPointsIso I).hom.app R
      (((groupPointsFunctor k).map (integralPowerMap k n)).app R x)) i =
      (show I → Rˣ from (splitTorusPointsIso I).hom.app R x) i ^ n i := by
  let v : I → Multiplicative ℤ := Pi.mulSingle i (Multiplicative.ofAdd (1 : ℤ))
  let m : ULift.{u} (Multiplicative (I → ℤ)) :=
    ⟨(MulEquiv.piMultiplicative (fun _ : I => ℤ)).symm v⟩
  change (show ULift.{u} (Multiplicative (I → ℤ)) →* Rˣ from
      (groupAlgebraPointsIso k _).hom.app R
        (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k (powerOnLiftedCharacters n)))).app R x)) m =
    (show ULift.{u} (Multiplicative (I → ℤ)) →* Rˣ from (groupAlgebraPointsIso k _).hom.app R x) m ^ n i
  rw [pointsIso_precompose, ← map_pow]
  congr 1
  apply ULift.ext
  apply Multiplicative.toAdd.injective
  funext j
  change (n j : ℤ) * (v j).toAdd =
    (n i : ℤ) • (v j).toAdd
  by_cases h : j = i
  · subst j
    simp [v]
  · simp [v, h, ← ofAdd_zero]

private def splitRootsPointsIso {I : Type} [Fintype I] [DecidableEq I] (n : I → ℕ) :
    (groupPointsFunctor k).obj (integralRootsOfUnityProduct k n) ≅
      splitProductPoints k PEmpty I n := by
  let M := ∀ i, Multiplicative (ZMod (n i))
  change (groupPointsFunctor k).obj (specGroup (groupAlgebra k (ULift.{u} M))) ≅
    splitProductPoints k PEmpty I n
  refine groupAlgebraPointsIso k (ULift.{u} M) ≪≫ NatIso.ofComponents (fun R => ?_) ?_
  · let e₀ : (ULift.{u} M →* Rˣ) ≃* (M →* Rˣ) := MulEquiv.ulift.monoidHomCongrLeft
    let h := e₀.trans ((finiteProductHomEquiv (fun i => Multiplicative (ZMod (n i))) Rˣ).trans
      (MulEquiv.piCongrRight fun i => cyclicHomEquiv (n i) R))
    let e : (∀ i, rootsOfUnity (n i) R) ≃* ((PEmpty → Rˣ) × (∀ i, rootsOfUnity (n i) R)) :=
      { toFun := fun x => (1, x)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := fun x => Prod.ext (Subsingleton.elim _ _) rfl
        map_mul' := fun _ _ => Prod.ext (Subsingleton.elim _ _) rfl }
    exact (h.trans e).toGrpIso
  · intro R S a
    apply GrpCat.ext
    intro x
    apply Prod.ext (Subsingleton.elim _ _)
    rfl

private theorem groupIsoOfPointIso_map_hom {G H : GroupScheme k} [IsAffine G.X.left]
    [IsAffine H.X.left] (e : (groupPointsFunctor k).obj G ≅ (groupPointsFunctor k).obj H) :
    (groupPointsFunctor k).map (groupIsoOfPointIso e).hom = e.hom :=
  (LinearAlgebraicGroups.groupHomEquiv G H inferInstance).apply_symm_apply _

theorem splitCoverSchemeCoordinates : SplitCoverSchemeCoordinates.{u} := by
  intro k _ G H q N T
  classical
  letI := T.finiteIndices
  letI := G.property.1
  letI := H.property.1
  letI := T.sourceTorus.isClosedImmersion
  letI := T.targetTorus.isClosedImmersion
  letI := N.isClosedImmersion
  letI : IsAffine T.sourceTorus.group.X.left := isAffine_of_isAffineHom T.sourceTorus.inclusion.hom.hom.left
  letI : IsAffine T.targetTorus.group.X.left := isAffine_of_isAffineHom T.targetTorus.inclusion.hom.hom.left
  letI : IsAffine N.group.X.left := isAffine_of_isAffineHom N.inclusion.hom.hom.left
  letI : IsAffine (integralSplitTorus k T.indices).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MonoidAlgebra k (ULift.{u} (Multiplicative (T.indices → ℤ)))))))
  letI : IsAffine (integralRootsOfUnityProduct k T.exponents).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra k (ULift.{u} (∀ i, Multiplicative (ZMod (T.exponents i))))))))
  obtain ⟨eT, eS, he⟩ := T.powerCoordinates
  obtain ⟨eN⟩ := T.kernelFactors
  let e := splitTorusPointsIso (k := k) T.indices
  let f := groupIsoOfPointIso (eT ≪≫ e.symm)
  let g := groupIsoOfPointIso (eS ≪≫ e.symm)
  refine ⟨f, g, ?_, ⟨groupIsoOfPointIso (eN ≪≫ (splitRootsPointsIso T.exponents).symm)⟩⟩
  apply (LinearAlgebraicGroups.groupHomComparison k _ _ inferInstance).injective
  change (groupPointsFunctor k).map (T.restriction ≫ g.hom) =
    (groupPointsFunctor k).map (f.hom ≫ integralPowerMap k T.exponents)
  dsimp only [f, g]
  rw [Functor.map_comp, Functor.map_comp, groupIsoOfPointIso_map_hom,
    groupIsoOfPointIso_map_hom]
  apply (cancel_mono e.hom).mp
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  intro x
  funext i
  change (show T.indices → Rˣ from e.hom.app R
    (e.inv.app R (eS.hom.app R (((groupPointsFunctor k).map T.restriction).app R x)))) i =
    (show T.indices → Rˣ from e.hom.app R
      (((groupPointsFunctor k).map (integralPowerMap k T.exponents)).app R
        (e.inv.app R (eT.hom.app R x)))) i
  rw [splitTorusPointsIso_power]
  simpa only [e, Iso.inv_hom_id_app_apply] using he R x i

end SchemeCoordinates

open private baseChangeMapPullback baseChangeKernelSquare
  from LinearAlgebraicGroups.Affine.Components
open private reductive_of_semisimple schemeKernel_eq_iff descendClosedFactor
  from LinearAlgebraicGroups.Classification.CentralIsogenies
open private isIso_of_scalarExtension centralIsogeny_postIso
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private schemeKernel_exists quotientRepresentsImage
  from LinearAlgebraicGroups.Affine.SchemeImageQuotient

open private isIso_of_schemeIso from LinearAlgebraicGroups.Reductive.GeometricRadicals

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_trivial_iff_isIso {k : Type u} [Field k]
    {H G : AffineAlgebraicGroup k} {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}
    (hq : IsCentralIsogeny q) (hN : IsSchemeKernel q N) :
    IsTrivialSubgroup N ↔ IsIso q := by
  constructor
  · rintro ⟨e⟩
    have hsub (Y : SchemeOver k) (z : Y ⟶ N.group.X) : z = 1 := by
      exact (cancel_mono ((Grp.forget (SchemeOver k)).mapIso e).hom).mp
        ((isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _)
    letI : Mono q.hom.hom := ⟨fun {Y} x y hxy => by
      obtain ⟨z, hz⟩ := (schemeKernel_eq_iff hN x y).mp hxy
      rw [hsub Y z, MonObj.one_comp] at hz
      exact inv_mul_eq_one.mp hz.symm⟩
    letI := hq.1
    letI := hq.2.1
    letI := hq.2.2.1
    letI : IsIso q.hom.hom.left := AlgebraicGeometry.Flat.isIso_of_surjective_of_mono _
    exact isIso_of_schemeIso q
  · intro h
    letI := h
    let e := (Grp.forget (SchemeOver k)).mapIso (asIso q)
    have h0 : N.inclusion.hom.hom = 1 := (cancel_mono e.hom).mp
      (by
        change N.inclusion.hom.hom ≫ q.hom.hom = 1 ≫ q.hom.hom
        rw [MonObj.one_comp]
        exact hN.w)
    have hzero : N.inclusion = 0 := Grp.hom_ext _ _ h0
    letI := N.isClosedImmersion
    letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
    let F := Grp.forget (SchemeOver k)
    letI : Mono N.inclusion := F.mono_of_mono_map
      (show Mono (F.map N.inclusion) from inferInstanceAs (Mono N.inclusion.hom.hom))
    exact ⟨(IsZero.of_mono_eq_zero N.inclusion hzero).iso (Grp.isZero_trivial _)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem centralIsogenyFieldExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H G : AffineAlgebraicGroup k} {q : H.val ⟶ G.val}
    (hq : IsCentralIsogeny q) : IsCentralIsogeny ((groupBaseChange k K).map q) := by
  let F := groupBaseChange k K
  obtain ⟨hfin, hflat, hsurj, N, hN, hn⟩ := hq
  letI := H.property.1
  let whole : ClosedSubgroup H.val :=
    ⟨H.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 H.val.X.left))⟩
  obtain ⟨Z, hZ⟩ := LinearAlgebraicGroups.centralizerScheme k H whole
  change RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 H.val) z) at hZ
  obtain ⟨a, ha⟩ := (hZ _ _).mp hn
  letI := Z.isClosedImmersion
  letI := isMonHom_of_comp_closed a N.inclusion Z.inclusion ha
  let j : N.group ⟶ Z.group := Grp.homMk a
  have hj : j ≫ Z.inclusion = N.inclusion := Grp.hom_ext _ _ ha
  obtain ⟨hcZ, hZ'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K (𝟙 H.val) Z hZ
  rw [F.map_id] at hZ'
  have hcN : IsClosedImmersion (F.map N.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) N.inclusion.hom.hom).flip
      N.isClosedImmersion
  let N' := Specs.GeometricRadicals.baseChangedSubgroup K N hcN
  have hN' : IsSchemeKernel (F.map q) N' := baseChangeKernelSquare q N.inclusion hN
  have hj' : (F.map j).hom.hom ≫ (F.map Z.inclusion).hom.hom =
      (F.map N.inclusion).hom.hom :=
    congrArg (fun f => f.hom.hom) ((F.map_comp _ _).symm.trans (F.congr_map hj))
  have hcentral := (hZ' _ N'.inclusion.hom.hom).mpr ⟨(F.map j).hom.hom, hj'⟩
  let hpb := (baseChangeMapPullback (K := K) q.hom.hom).flip
  exact ⟨MorphismProperty.of_isPullback hpb hfin, MorphismProperty.of_isPullback hpb hflat,
    MorphismProperty.of_isPullback hpb hsurj, N', hN', hcentral⟩

set_option backward.isDefEq.respectTransparency false in
theorem trivialKernelIffSimplyConnected : TrivialKernelIffSimplyConnected.{u} := by
  intro k _ G H hH hsc q N hq hN
  let K := AlgebraicClosure k
  let f := (groupBaseChange k K).map q
  rw [kernel_trivial_iff_isIso hq hN]
  constructor
  · intro h
    letI := h
    letI : IsIso f := Functor.map_isIso (groupBaseChange k K) q
    intro L hL a ha
    letI := hsc L hL (a ≫ inv f) (centralIsogeny_postIso (asIso f).symm ha)
    exact IsIso.of_isIso_comp_right a (inv f)
  · intro h
    have hH' := (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K)
      H hH.1 hH.2.1).mpr hH
    exact isIso_of_scalarExtension K q
      (h (baseChangedAlgebraicGroup K H) hH' f (centralIsogenyFieldExtension hq))

set_option backward.isDefEq.respectTransparency false in
private theorem factors_through_source_torus {k : Type u} [Field k]
    {H G : GroupScheme k} {q : H ⟶ G}
    {T : ClosedSubgroup H} {S : ClosedSubgroup G} {qT : T.group ⟶ S.group}
    (hq : IsCentralIsogeny q) (hqT : IsTorusRestriction q qT)
    {N : ClosedSubgroup H} (hN : IsSchemeKernel q N) (hNT : IsSubgroupOf N T)
    {Y : SchemeOver k} [IsAffine Y.left] (x : Y ⟶ H.X) (y : Y ⟶ S.group.X)
    (hxy : x ≫ q.hom.hom = y ≫ S.inclusion.hom.hom) :
    ∃ t : Y ⟶ T.group.X, t ≫ T.inclusion.hom.hom = x := by
  obtain ⟨j, hj⟩ := hNT
  let U := pullback y qT.hom.hom
  let a : U ⟶ Y := pullback.fst _ _
  let b : U ⟶ T.group.X := pullback.snd _ _
  have hpb : IsPullback a b y qT.hom.hom := IsPullback.of_hasPullback _ _
  let hp := hpb.map (Over.forget (Spec (CommRingCat.of k)))
  letI : Flat a.left := MorphismProperty.of_isPullback hp.flip hqT.2.1
  letI : Surjective a.left := MorphismProperty.of_isPullback hp.flip hqT.2.2
  letI : IsFinite a.left :=
    MorphismProperty.of_isPullback hp.flip (finiteTorusRestriction hq.1 hqT)
  letI : IsAffine U.left := isAffine_of_isAffineHom a.left
  have hcomm : qT.hom.hom ≫ S.inclusion.hom.hom = T.inclusion.hom.hom ≫ q.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hqT.1
  have h : (b ≫ T.inclusion.hom.hom) ≫ q.hom.hom = (a ≫ x) ≫ q.hom.hom := by
    rw [Category.assoc, ← hcomm, ← Category.assoc, ← hpb.w, Category.assoc,
      ← hxy, Category.assoc]
  obtain ⟨z, hz⟩ := (schemeKernel_eq_iff hN _ _).mp h
  have hj' : j.hom.hom ≫ T.inclusion.hom.hom = N.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  letI := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  apply descendClosedFactor a T.inclusion.hom.hom x (b * (z ≫ j.hom.hom))
  rw [MonObj.mul_comp, Category.assoc, hj', hz, mul_inv_cancel_left]

set_option backward.isDefEq.respectTransparency false in
private theorem centralizes_image {k : Type u} [Field k] {H G : GroupScheme k}
    {q : H ⟶ G} (hf : Flat q.hom.hom.left) (hs : Surjective q.hom.hom.left)
    {X : SchemeOver k} {x : X ⟶ H.X} (hx : Centralizes (𝟙 H) x) :
    Centralizes (𝟙 G) (x ≫ q.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro Y y g
  let p : pullback g q.hom.hom ⟶ Y := pullback.fst _ _
  let s : pullback g q.hom.hom ⟶ H.X := pullback.snd _ _
  have hpb : IsPullback p s g q.hom.hom := IsPullback.of_hasPullback _ _
  let hp := hpb.map (Over.forget (Spec (CommRingCat.of k)))
  letI : Flat p.left := MorphismProperty.of_isPullback hp.flip hf
  letI : Surjective p.left := MorphismProperty.of_isPullback hp.flip hs
  letI : Epi p.left := Flat.epi_of_flat_of_surjective _
  letI : Epi p := Over.epi_of_epi_left _
  have hc := (centralizes_iff _ _).mp hx _ (p ≫ y) s
  change Commute ((p ≫ y) ≫ x) s at hc
  change Commute (y ≫ x ≫ q.hom.hom) g
  apply (cancel_epi p).mp
  rw [MonObj.comp_mul, MonObj.comp_mul, hpb.w]
  simp only [Category.assoc] at hc ⊢
  exact (hc.map (((yonedaGrp.map q).app (op _)).hom)).eq

open Specs.CharacterPairing (absoluteRoots)
open private centralizes_precomp from LinearAlgebraicGroups.RootData.SchemeCentre

set_option backward.isDefEq.respectTransparency false in
private theorem compositeKernel_isCentre
    {k : Type u} [Field k] (G H : AffineAlgebraicGroup k)
    (hG : GeometricRadicals.IsSemisimple G) (hH : GeometricRadicals.IsSemisimple H)
    (T : ClosedSubgroup H.val) (S : ClosedSubgroup G.val)
    (hsT : GeometricRadicals.IsSplitTorus T.group) (hmT : RankOneFlag.IsGeometricallyMaximal T)
    (hsS : GeometricRadicals.IsSplitTorus S.group) (hmS : RankOneFlag.IsGeometricallyMaximal S)
    (q : H.val ⟶ G.val) (qT : T.group ⟶ S.group) (hq : IsCentralIsogeny q)
    (hqT : IsTorusRestriction q qT)
    (W : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (p : G.val ⟶ Q.val)
    (hW : RepresentsSubgroup W (fun _ z => Centralizes (𝟙 G.val) z))
    (hk : IsSchemeKernel p W) (Z : ClosedSubgroup H.val) (hZ : IsSchemeKernel (q ≫ p) Z) :
    RepresentsSubgroup Z (fun _ x => Centralizes (𝟙 H.val) x) := by
  have hrH := reductive_of_semisimple H hH
  have hrG := reductive_of_semisimple G hG
  letI := Q.property.1
  letI := H.property.1
  letI := G.property.1
  obtain ⟨N, hN, hn⟩ := hq.2.2.2
  let cf : CentreFormula.{u} := RootData.SchemeCentre.schemeCentre
  have hNT := kernel_le_maximalTorus cf H hrH T hsT hmT N hn
  have hST := kernel_le_maximalTorus cf G hrG S hsS hmS W
    ((hW _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
  have hZq : Z.inclusion.hom.hom ≫ q.hom.hom ≫ p.hom.hom = 1 := hZ.w
  obtain ⟨z, hz⟩ := (schemeKernel_sections hk
    (Z.inclusion.hom.hom ≫ q.hom.hom)).mpr (by rw [Category.assoc]; exact hZq)
  change z ≫ W.inclusion.hom.hom = Z.inclusion.hom.hom ≫ q.hom.hom at hz
  obtain ⟨j, hj⟩ := hST
  have hjs : j.hom.hom ≫ S.inclusion.hom.hom = W.inclusion.hom.hom :=
    congrArg (Grp.forget (SchemeOver k)).map hj
  have hz' : Z.inclusion.hom.hom ≫ q.hom.hom =
      (z ≫ j.hom.hom) ≫ S.inclusion.hom.hom := by
    simpa only [Category.assoc, hjs] using hz.symm
  letI := Z.isClosedImmersion
  letI : IsAffine Z.group.X.left := isAffine_of_isAffineHom Z.inclusion.hom.hom.left
  obtain ⟨t, ht⟩ := factors_through_source_torus hq hqT hN hNT _ _ hz'
  have htq : (t ≫ qT.hom.hom) ≫ S.inclusion.hom.hom =
      z ≫ W.inclusion.hom.hom := by
    rw [Category.assoc, show qT.hom.hom ≫ S.inclusion.hom.hom =
      T.inclusion.hom.hom ≫ q.hom.hom from congrArg (Grp.forget (SchemeOver k)).map hqT.1,
      ← Category.assoc, ht, hz]
  have htc : Centralizes (𝟙 G.val) ((t ≫ qT.hom.hom) ≫ S.inclusion.hom.hom) := by
    rw [htq]
    exact (hW _ _).mpr ⟨z, rfl⟩
  obtain ⟨_, _, _, _, _, hrootsT⟩ := cf H hrH T hsT hmT
  obtain ⟨_, _, _, _, _, hrootsS⟩ := cf G hrG S hsS hmS
  obtain ⟨_, _, hb, _⟩ :=
    centralIsogenyComparison H G hrH hrG T S hsT hmT hsS hmS q qT hq hqT.1 hqT.2.2
  have hZi : Centralizes (𝟙 H.val) Z.inclusion.hom.hom := by
    obtain ⟨A, ⟨a⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr
      (inferInstance : IsAffine Z.group.X.left)
    have hAt : Centralizes (𝟙 G.val) ((a.hom ≫ t ≫ qT.hom.hom) ≫ S.inclusion.hom.hom) := by
      simpa only [Category.assoc] using centralizes_precomp htc a.hom
    have hAr := (hrootsT A.unop (a.hom ≫ t)).mpr (by
      intro α hα
      obtain ⟨β, hβ, rfl⟩ := hb.surjOn hα
      change (a.hom ≫ t) ≫ (qT.hom.hom ≫ β.hom.hom) = 1
      simpa only [Category.assoc] using
        (hrootsS A.unop (a.hom ≫ t ≫ qT.hom.hom)).mp hAt β hβ)
    have h := centralizes_precomp hAr a.inv
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc t, ht] using h
  intro Y x
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (hW _ _).mp (centralizes_image hq.2.1 hq.2.2.1 hx)
    change c ≫ W.inclusion.hom.hom = x ≫ q.hom.hom at hc
    apply (schemeKernel_sections hZ _).mpr
    change x ≫ q.hom.hom ≫ p.hom.hom = 1
    rw [← Category.assoc, ← hc]
    exact (schemeKernel_sections hk _).mp ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact centralizes_precomp hZi c
set_option backward.isDefEq.respectTransparency false in
private theorem commonAdjointQuotient_of_composite {k : Type u} [Field k]
    {H G Q : AffineAlgebraicGroup k} (q : H.val ⟶ G.val) (p : G.val ⟶ Q.val)
    (hq : IsCentralIsogeny q)
    (W : ClosedSubgroup G.val) (hW : RepresentsSubgroup W (fun _ w => Centralizes (𝟙 G.val) w))
    (hk : IsSchemeKernel p W)
    (hp : Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left)
    (Z : ClosedSubgroup H.val) (hZ : IsSchemeKernel (q ≫ p) Z)
    (hCZ : RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 H.val) z)) :
    SameAdjointQuotient q := by
  letI := H.property.1
  letI := G.property.1
  letI := Q.property.1
  let f := q ≫ p
  refine ⟨Z, W, Q, p, hCZ, hW, ?_, ?_⟩
  · letI := hq.2.1
    letI := hq.2.2.1
    letI := hq.1
    letI := G.property.2.1
    letI : IsLocallyNoetherian G.val.X.left := LocallyOfFiniteType.isLocallyNoetherian G.val.X.hom
    letI : LocallyOfFinitePresentation q.hom.hom.left := inferInstance
    letI := hp.1
    letI := hp.2.1
    letI := hp.2.2
    exact quotientRepresentsImage
      (p := f) (i := 𝟙 Q.val) ⟨Category.comp_id _,
        inferInstanceAs (Flat (q.hom.hom.left ≫ p.hom.hom.left)),
        inferInstanceAs (Surjective (q.hom.hom.left ≫ p.hom.hom.left)),
        inferInstanceAs (LocallyOfFinitePresentation (q.hom.hom.left ≫ p.hom.hom.left)),
        inferInstance,
        inferInstanceAs (IsClosedImmersion (𝟙 Q.val.X.left))⟩ hZ
  · exact quotientRepresentsImage
      (p := p) (i := 𝟙 Q.val) ⟨Category.comp_id _, hp.1,
        hp.2.1, hp.2.2, inferInstance,
        inferInstanceAs (IsClosedImmersion (𝟙 Q.val.X.left))⟩ hk

open private factor_of_baseChange from LinearAlgebraicGroups.Affine.ClosedSubgroups

set_option backward.isDefEq.respectTransparency false in
private theorem isCentre_of_scalarExtension {k K : Type u} [Field k] [Field K] [Algebra k K]
    (H : AffineAlgebraicGroup k) (Z : ClosedSubgroup H.val)
    (hZ : IsClosedImmersion ((groupBaseChange k K).map Z.inclusion).hom.hom.left)
    (h : RepresentsSubgroup (scalarExtendedSubgroup K Z hZ)
      (fun _ x => Centralizes (𝟙 ((groupBaseChange k K).obj H.val)) x)) :
    RepresentsSubgroup Z (fun _ x => Centralizes (𝟙 H.val) x) := by
  let F := groupBaseChange k K
  let whole : ClosedSubgroup H.val :=
    ⟨H.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 H.val.X.left))⟩
  obtain ⟨C, hC⟩ := LinearAlgebraicGroups.centralizerScheme k H whole
  change RepresentsSubgroup C (fun _ x => Centralizes (𝟙 H.val) x) at hC
  obtain ⟨hc, hC'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K (𝟙 H.val) C hC
  rw [F.map_id] at hC'
  obtain ⟨a, ha⟩ := (hC' _ _).mp
    ((h _ (F.map Z.inclusion).hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨b, hb⟩ := (h _ _).mp
    ((hC' _ (F.map C.inclusion).hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩)
  letI := C.isClosedImmersion
  letI := Z.isClosedImmersion
  obtain ⟨r, hr⟩ := factor_of_baseChange K Z.inclusion.hom.hom C.inclusion.hom.hom a ha
  obtain ⟨s, hs⟩ := factor_of_baseChange K C.inclusion.hom.hom Z.inclusion.hom.hom b hb
  intro Y y
  rw [hC Y y]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x ≫ s, by rw [Category.assoc, hs, hx]⟩
  · rintro ⟨x, hx⟩
    exact ⟨x ≫ r, by rw [Category.assoc, hr, hx]⟩


set_option backward.isDefEq.respectTransparency false in
private theorem commonAdjointQuotient_of_splitExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H Q : AffineAlgebraicGroup k} (q : H.val ⟶ G.val) (hq : IsCentralIsogeny q)
    (W : ClosedSubgroup G.val) (hW : RepresentsSubgroup W (fun _ w => Centralizes (𝟙 G.val) w))
    (p : G.val ⟶ Q.val) (hk : IsSchemeKernel p W)
    (hp : Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧ LocallyOfFinitePresentation p.hom.hom.left)
    (hG : GeometricRadicals.IsSemisimple (baseChangedAlgebraicGroup K G))
    (hH : GeometricRadicals.IsSemisimple (baseChangedAlgebraicGroup K H))
    (T : ClosedSubgroup (baseChangedAlgebraicGroup K H).val)
    (S : ClosedSubgroup (baseChangedAlgebraicGroup K G).val)
    (hsT : GeometricRadicals.IsSplitTorus T.group) (hmT : RankOneFlag.IsGeometricallyMaximal T)
    (hsS : GeometricRadicals.IsSplitTorus S.group) (hmS : RankOneFlag.IsGeometricallyMaximal S)
    (qT : T.group ⟶ S.group) (hqT : IsTorusRestriction ((groupBaseChange k K).map q) qT) :
    SameAdjointQuotient q := by
  let F := groupBaseChange k K
  letI := Q.property.1
  obtain ⟨Z, hZ⟩ := schemeKernel_exists (q ≫ p)
  let hZc : IsClosedImmersion (F.map Z.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) Z.inclusion.hom.hom).flip
      Z.isClosedImmersion
  let Z' : ClosedSubgroup (F.obj H.val) := scalarExtendedSubgroup K Z hZc
  have hz' : IsSchemeKernel (F.map (q ≫ p)) Z' := baseChangeKernelSquare (q ≫ p) Z.inclusion hZ
  rw [F.map_comp] at hz'
  obtain ⟨hWc, hW'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K (𝟙 G.val) W hW
  rw [F.map_id] at hW'
  let W' : ClosedSubgroup (F.obj G.val) := scalarExtendedSubgroup K W hWc
  have hw' : IsSchemeKernel (F.map p) W' := baseChangeKernelSquare p W.inclusion hk
  have hc := compositeKernel_isCentre (baseChangedAlgebraicGroup K G) (baseChangedAlgebraicGroup K H)
    hG hH T S hsT hmT hsS hmS (F.map q) qT (centralIsogenyFieldExtension hq) hqT W'
    (baseChangedAlgebraicGroup K Q) (F.map p) hW' hw' Z' hz'
  exact commonAdjointQuotient_of_composite q p hq W hW hk hp Z hZ
    (isCentre_of_scalarExtension H Z hZc hc)

set_option backward.isDefEq.respectTransparency false in
theorem splitSameAdjointQuotient : SplitSameAdjointQuotient.{u} := by
  intro k _ G H hG hH T S hsT hmT hsS hmS q qT hq hqT
  obtain ⟨Q⟩ := LinearAlgebraicGroups.Descent.AutomorphismSequence.adjointQuotient_exists G
  letI := Q.quotient.property.1
  obtain ⟨Z, hZ⟩ := schemeKernel_exists (q ≫ Q.projection)
  exact commonAdjointQuotient_of_composite q Q.projection hq Q.centre Q.isCentre Q.kernel
    Q.fppf Z hZ
    (compositeKernel_isCentre G H hG hH T S hsT hmT hsS hmS q qT hq hqT Q.centre
      Q.quotient Q.projection Q.isCentre Q.kernel Z hZ)

set_option backward.isDefEq.respectTransparency false in
theorem sameAdjointQuotientAfterSplitting : SameAdjointQuotientAfterSplitting.{u} := by
  intro k E _ _ _ G H q hq _ _ hG hH T S hsT hmT hsS hmS qT hqT
  obtain ⟨Q⟩ := LinearAlgebraicGroups.Descent.AutomorphismSequence.adjointQuotient_exists G
  exact commonAdjointQuotient_of_splitExtension q hq Q.centre Q.isCentre Q.projection Q.kernel
    Q.fppf hG hH T S hsT hmT hsS hmS qT hqT


open Specs.CharacterDescent (StandardLattice)
open LinearAlgebraicGroups.CharacterDescent
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private groupLikeIso from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isTorus_of_split from LinearAlgebraicGroups.RootData.CharacterPairing
open private splitTorus_baseChange from LinearAlgebraicGroups.Classification.CentralIsogenies
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private splitBorelPair from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

section SplittingField

set_option backward.isDefEq.respectTransparency false

private theorem exists_finite_galois_splitting {k : Type u} [Field k]
    (T : AffineAlgebraicGroup k) (hT : IsTorus T.val) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E)
      (_ : IsGalois k E), IsSplitTorus ((groupBaseChange k E).obj T.val) := by
  let L := SeparableClosure k
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation T
  have hA := (torusOnSchemes A).mpr (by
    obtain ⟨K, hK, halg, hsep, r, ⟨d⟩⟩ := hT
    exact ⟨K, hK, halg, hsep, r, ⟨(groupBaseChange k K).mapIso e ≪≫ d⟩⟩)
  have hMT := torusIsMultiplicativeType A hA
  obtain ⟨r, ⟨h⟩⟩ := ((torusAndSplitCriteria (K := L) A hMT).1).mp hA
  obtain ⟨E, hE, hEgal, M, ⟨i⟩⟩ := finiteGaloisSplitting (K := L) A hMT
  let j := (CommHopfAlgCat.isoMk (groupAlgebraBaseChange E L M.obj)).symm ≪≫
    (extendedHopfFunctor L).mapIso i ≪≫ extendedHopfTower L A
  let c : M.obj ≃* StandardLattice.{u} r :=
    (monomialCharacterEquiv L).trans ((groupLikeIso j).trans h)
  let d : groupAlgebra E (StandardLattice.{u} r) ≅ extendedHopf E A :=
    CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv E E c.symm) ≪≫ i
  obtain ⟨s⟩ := standardSplitTorus (k := E) r
  exact ⟨E, inferInstance, inferInstance, hE, hEgal, r,
    ⟨((groupBaseChange k E).mapIso e).symm ≪≫ (extendedGroupIso E A).symm ≪≫
      (hopfSpec (CommRingCat.of E)).mapIso d.op ≪≫ s⟩⟩

private theorem isGeometricallyMaximal_of_centralizer {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (hs : IsSplitTorus T.group) (hc : IsCentralizer T T) :
    IsGeometricallyMaximal T := by
  let K := AlgebraicClosure k
  obtain ⟨h, hc'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K T.inclusion T hc
  refine ⟨h, isTorus_of_split (splitTorus_baseChange K hs), ?_⟩
  intro S hS hTS
  obtain ⟨i, hi⟩ := hTS
  letI : IsCommMonObj S.group.X := torus_commutative (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G) S) hS
  let F := groupBaseChange k K
  have hi' : i.hom.hom ≫ S.inclusion.hom.hom = (F.map T.inclusion).hom.hom :=
    congrArg (Grp.forget (SchemeOver K)).map hi
  have hz : Centralizes (F.map T.inclusion) S.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y x y
    rw [← hi', ← Category.assoc]
    exact (Commute.all x (y ≫ i.hom.hom)).map (((yonedaGrp.map S.inclusion).app (Opposite.op Y)).hom)
  obtain ⟨a, ha⟩ := (hc' _ _).mp hz
  letI : IsClosedImmersion (F.map T.inclusion).hom.hom.left := h
  letI := isMonHom_of_comp_closed a S.inclusion (F.map T.inclusion) ha
  exact ⟨Grp.homMk a, Grp.hom_ext _ _ ha⟩

private theorem geometricallyMaximalTorusFiniteSplitting {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (T : ClosedSubgroup G.val) (ht : IsTorus T.group) (hm : IsGeometricallyMaximal T) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E)
      (_ : IsGalois k E),
      ∃ i : IsClosedImmersion ((groupBaseChange k E).map T.inclusion).hom.hom.left,
        let T' := baseChangedSubgroup E T i
        IsSplitTorus T'.group ∧ IsGeometricallyMaximal T' := by
  obtain ⟨E, hE, hA, hfin, hgal, hs⟩ :=
    exists_finite_galois_splitting (closedSubgroupAlgebraicGroup T) ht
  have hc := Reductive.TorusCentralizer.maximalTorusCentralizer G hG T ht hm
  obtain ⟨hi, hc'⟩ :=
    LinearAlgebraicGroups.centralizerSchemeBaseChange k E T.inclusion T hc
  exact ⟨E, hE, hA, hfin, hgal, hi, hs,
    isGeometricallyMaximal_of_centralizer (baseChangedAlgebraicGroup E G)
      (baseChangedSubgroup E T hi) hs hc'⟩

private theorem exists_split_maximalTorus_finiteGalois {k : Type u} [Field k]
    (G : AffineAlgebraicGroup k) (hG : IsSemisimple G) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : FiniteDimensional k E)
      (_ : IsGalois k E),
      let G' := baseChangedAlgebraicGroup E G
      ∃ T : ClosedSubgroup G'.val,
        IsSemisimple G' ∧ IsSplitTorus T.group ∧ IsGeometricallyMaximal T := by
  have hGr := reductive_of_semisimple G hG
  letI := hG.2.1
  have hconn : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  obtain ⟨T, ht, hm⟩ := MaximalToriExist.geometricallyMaximalTorusExists G hG.1 hconn
  obtain ⟨E, hE, hA, hEF, hEG, hTs, hs, hm'⟩ :=
    geometricallyMaximalTorusFiniteSplitting G hGr T ht hm
  let G' := baseChangedAlgebraicGroup E G
  let T' := baseChangedSubgroup E T hTs
  have hG' : IsSemisimple G' :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) G hG.1 hG.2.1).mpr hG
  exact ⟨E, hE, hA, hEF, hEG, T', hG', hs, hm'⟩

theorem splitCoverAfterFiniteGaloisExtension : SplitCoverAfterFiniteGaloisExtension.{u} := by
  intro k _ G hG
  obtain ⟨E, hE, hA, hEF, hEG, T', hG', hs, hm'⟩ := exists_split_maximalTorus_finiteGalois G hG
  let G' := baseChangedAlgebraicGroup E G
  let P := splitBorelPair G' (reductive_of_semisimple G' hG') T' hs hm'
  let D := Classification.Pinning.attachedDatum P
  letI : IsCommMonObj T'.group.X := D.comm
  obtain ⟨S, _, f, fT, hS, hsc, hf, hfT, _, _⟩ :=
    Classification.SimplyConnectedLattice.splitCover G' hG' T' hs hm' D.datum
  obtain ⟨N, hN, _⟩ := hf.2.2.2
  exact ⟨E, hE, hA, hEF, hEG, S.G, f, N, hG', hS, hsc, hf, hN,
    splitCoverDataExists G' S.G (reductive_of_semisimple G' hG') S.reductive S.T T'
      S.split S.maximal hs hm' f fT hf hfT N hN⟩

end SplittingField

open IsDedekindDomain
open private integers_contained from LinearAlgebraicGroups.Arithmetic.GlobalPlaces

private theorem fraction_ring_of_containing_integers
    {A E : Type u} [CommRing A] [Field E] [Algebra A E] [IsFractionRing A E]
    (R : Subring E) (h : ∀ a : A, algebraMap A E a ∈ R) : IsFractionRing R E := by
  letI : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro x
  obtain ⟨a, b, _, hx⟩ := IsFractionRing.div_surjective A x
  exact ⟨⟨algebraMap A E a, h a⟩, ⟨algebraMap A E b, h b⟩, hx.symm⟩

theorem dedekindIntegralBase : DedekindIntegralBase.{u, v} := by
  intro E _ D B hB
  cases D with
  | number h =>
    letI := h
    refine ⟨NumberField.RingOfIntegers E, inferInstance, inferInstance, inferInstance,
      inferInstance, B, hB, Set.Subset.rfl, ?_⟩
    intro a
    apply Subring.mem_iInf.mpr
    intro w
    change (algebraMap E (w.val.adicCompletion E)) (algebraMap (NumberField.RingOfIntegers E) E a) ∈
      w.val.adicCompletionIntegers E
    exact HeightOneSpectrum.coe_algebraMap_mem (R := NumberField.RingOfIntegers E) (K := E) (v := w.val) a
  | function F t =>
    let P : Set (FunctionPlace E) := {w | t.element ∉ w.val}
    refine ⟨t.integerRing, inferInstance, inferInstance, inferInstance, inferInstance,
      B ∪ P, hB.union t.finite_poles, Set.subset_union_left, ?_⟩
    intro a
    apply Subring.mem_iInf.mpr
    intro w
    change w.val.embedding (algebraMap t.integerRing E a) ∈ w.val.integers
    rw [FunctionPlace.embedding_mem_integers]
    apply integers_contained t
    by_contra h
    exact w.property (Or.inr h)

theorem integersOutsideFractionRing : IntegersOutsideFractionRing.{u, v} := by
  intro E _ D B hB
  obtain ⟨A, hR, _, hAlg, hFrac, S, hS, hBS, hA⟩ := dedekindIntegralBase D B hB
  refine ⟨S, hS, hBS, fun T hST => fraction_ring_of_containing_integers (A := A) _ ?_⟩
  intro a
  apply Subring.mem_iInf.mpr
  intro w
  exact (Subring.mem_iInf.mp (hA a)) ⟨w.val, fun hw => w.property (hST hw)⟩

theorem integralLocalization : IntegralLocalization.{u, v} := by
  intro A E _ _ _ _ D B hB hA d _ _ hd
  let z := algebraMap A E d
  have hz : z ≠ 0 := by simpa [z] using (IsFractionRing.injective A E).ne hd
  obtain ⟨S, hS, hBS, hC⟩ := finiteCoefficientsIntegral D B {z⁻¹} hB (Set.finite_singleton _)
  let R := integersOutside D S
  have hmem (a : A) : algebraMap A E a ∈ R := by
    apply Subring.mem_iInf.mpr
    intro w
    exact (Subring.mem_iInf.mp (hA a)) ⟨w.val, fun hw => w.property (hBS hw)⟩
  let g := (algebraMap A E).codRestrict R hmem
  let y : R := ⟨z⁻¹, hC (Set.mem_singleton _)⟩
  have hu : IsUnit (g d) := IsUnit.of_mul_eq_one y (Subtype.ext (mul_inv_cancel₀ hz))
  refine ⟨S, hS, hBS, IsLocalization.Away.lift d hu, ?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, ← IsScalarTower.algebraMap_eq]
  rfl

open private fieldSpecMap_surjective from LinearAlgebraicGroups.Affine.Stabilizers


set_option backward.isDefEq.respectTransparency false in
private theorem finite_of_affine_faithfullyFlat_pullback {U X Y V : Scheme.{u}}
    [IsAffine U] [IsAffine X] [IsAffine Y] {a : V ⟶ U} {b : V ⟶ X}
    {f : U ⟶ Y} {g : X ⟶ Y} (h : IsPullback a b f g)
    [Flat f] [Surjective f] (ha : IsFinite a) : IsFinite g := by
  let e := U.isoSpec
  let d := X.isoSpec
  let t := Y.isoSpec
  let f' := e.inv ≫ f ≫ t.hom
  let g' := d.inv ≫ g ≫ t.hom
  have h' : IsPullback (a ≫ e.hom) (b ≫ d.hom) f' g' := by
    apply h.of_iso (Iso.refl _) e d t
    · simp
    · simp
    · simp [f']
    · simp [g']
  have hpf : IsFinite (pullback.fst f' g') := by
    rw [← h'.isoPullback_inv_fst]
    letI := ha
    haveI : IsFinite (a ≫ e.hom) := inferInstance
    infer_instance
  have hf : IsFinite g' := by
    refine of_pullback_fst_Spec_of_codescendsAlong (P := @IsFinite)
      (Q' := RingHom.FaithfullyFlat) (Q := RingHom.Finite) (P' := @Surjective ⊓ @Flat)
      RingHom.Finite.codescendsAlong_faithfullyFlat ?_ ?_ ?_ hpf
    · intro A B u hu
      rwa [← flat_and_surjective_SpecMap_iff, and_comm]
    · exact IsFinite.SpecMap_iff _
    · exact ⟨inferInstanceAs (Surjective (e.inv ≫ f ≫ t.hom)),
        inferInstanceAs (Flat (e.inv ≫ f ≫ t.hom))⟩
  letI := hf
  have hcomp : g = d.hom ≫ g' ≫ t.inv := by simp [g']
  rw [hcomp]
  infer_instance

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem centralIsogeny_of_fieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H G : AffineAlgebraicGroup k} (q : H.val ⟶ G.val) {N : ClosedSubgroup H.val}
    (hN : IsSchemeKernel q N) (hq : IsCentralIsogeny ((groupBaseChange k K).map q)) :
    IsCentralIsogeny q := by
  let F := groupBaseChange k K
  let a := fieldSpecMap k K
  letI : Surjective a := fieldSpecMap_surjective K
  let s := pullback.fst G.val.X.hom a
  let fpqc : MorphismProperty Scheme.{u} := @Surjective ⊓ @Flat ⊓ @QuasiCompact
  have hs : fpqc s := ⟨⟨inferInstanceAs (Surjective (pullback.fst G.val.X.hom a)),
    inferInstanceAs (Flat (pullback.fst G.val.X.hom a))⟩,
    inferInstanceAs (QuasiCompact (pullback.fst G.val.X.hom a))⟩
  have hpb := baseChangeMapPullback (K := K) q.hom.hom
  letI := H.property.1
  letI := G.property.1
  letI : IsAffine (pullback G.val.X.hom a) := isAffine_of_isAffineHom s
  letI : Flat s := hs.1.2
  letI : Surjective s := hs.1.1
  change IsPullback (F.map q).hom.hom.left (pullback.fst H.val.X.hom a) s q.hom.hom.left at hpb
  have hf := finite_of_affine_faithfullyFlat_pullback
    (U := pullback G.val.X.hom a) hpb hq.1
  have hflat := MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat) hpb hs hq.2.1
  have hsurj := MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective) hpb hs hq.2.2.1
  let whole : ClosedSubgroup H.val :=
    ⟨H.val, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 H.val.X.left))⟩
  obtain ⟨C, hC⟩ := LinearAlgebraicGroups.centralizerScheme k H whole
  change RepresentsSubgroup C (fun _ x => Centralizes (𝟙 H.val) x) at hC
  obtain ⟨hc, hC'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange k K (𝟙 H.val) C hC
  rw [F.map_id] at hC'
  have hi : IsClosedImmersion (F.map N.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := K) N.inclusion.hom.hom).flip
      N.isClosedImmersion
  let N' := scalarExtendedSubgroup K N hi
  have hN' : IsSchemeKernel (F.map q) N' := baseChangeKernelSquare q N.inclusion hN
  have hz : Centralizes (𝟙 (F.obj H.val)) N'.inclusion.hom.hom :=
    kernel_is_central (q := F.map q) (N := N') hq hN'
  obtain ⟨b, hb⟩ := (hC' (F.obj N.group).X (F.map N.inclusion).hom.hom).mp hz
  letI := C.isClosedImmersion
  obtain ⟨c, hc'⟩ := factor_of_baseChange K N.inclusion.hom.hom C.inclusion.hom.hom b hb
  exact ⟨hf, hflat, hsurj, N, hN, (hC _ _).mpr ⟨c, hc'⟩⟩

set_option backward.isDefEq.respectTransparency false in
theorem coverExists_of_descent (descend : CoverDescent.{u}) : CoverExists.{u} := by
  intro k _ G hG
  obtain ⟨E, hE, hA, hEF, hEG, S, hG', hsS, hmS⟩ := exists_split_maximalTorus_finiteGalois G hG
  obtain ⟨H, q, hH, hsc, hq', T, qT, hsT, hmT, hqT⟩ := descend G hG S hsS hmS
  let F := groupBaseChange k E
  let G' := baseChangedAlgebraicGroup E G
  let H' := baseChangedAlgebraicGroup E H
  have hH' : IsSemisimple H' :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := E) H hH.1 hH.2.1).mpr hH
  letI := G.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists q
  have hq := centralIsogeny_of_fieldExtension q hN hq'
  have hi : IsClosedImmersion (F.map N.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapPullback (K := E) N.inclusion.hom.hom).flip
      N.isClosedImmersion
  let N' := baseChangedSubgroup E N hi
  have hN' : IsSchemeKernel (F.map q) N' := baseChangeKernelSquare q N.inclusion hN
  have hrH' := reductive_of_semisimple H' hH'
  have hrG' := reductive_of_semisimple G' hG'
  obtain ⟨_, hM, e⟩ :=
    splitKernelCharacters H' G' hrH' hrG' T S hsT hmT hsS hmS (F.map q) qT hq' hqT N' hN'
  let M := Character T.group ⧸ (characterPullback qT).range
  have hf : IsFinite N.group.X.hom :=
    MorphismProperty.of_isPullback (hN.map (Over.forget (Spec (CommRingCat.of k)))) hq.1
  have hMT : IsFiniteMultiplicativeType N.group :=
    ⟨hf, E, hE, hA, hEF, hEG, M, inferInstance, hM, e⟩
  exact ⟨H, q, N, hH, hsc, hq, hN, hMT,
    sameAdjointQuotientAfterSplitting G H q hq hG' hH' T S hsT hmT hsS hmS qT hqT,
    trivialKernelIffSimplyConnected G H hH hsc q N hq hN,
    E, hE, hA, hEF, hEG, hi, hG', hH', hq', hN',
    splitCoverDataExists G' H' hrG' hrH' T S hsT hmT hsS hmS (F.map q) qT hq' hqT N' hN'⟩

/-- The simply connected central cover with its split torus and scheme kernel. -/
theorem coverExists : CoverExists.{u} :=
  coverExists_of_descent CentralCoverDescent.coverDescent

/-! Integral models of the marked split isogeny. -/

open scoped TensorProduct
open Algebra.TensorProduct
open Specs.IntegralCentralQuotient (HopfSpectrum fibreGroup spectrumOfHopfHom spectrumOfAlgHom)
open Specs.CentralCoverSpreading
  (Diagram IntegralDiagram TorusCoordinates KernelCoordinates IsFullKernel GenericFibre
    groupAlgebraInclusion tensorComparison)
open private eval_comul spectrumOfAlgHom_comp spectrumOfHopfHom_comp central_translation
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient

section

section ScalarExtension

variable {R S U A B : Type u} [CommRing R] [CommRing S] [Algebra R S]

abbrev scalarSpec (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))

abbrev scalarExtension (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :=
  (Over.pullback (scalarSpec R S)).mapGrp

abbrev affineSpectrum (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))

set_option backward.isDefEq.respectTransparency false in
def spectrumBaseChangeIso [CommRing A] [Algebra R A] :
    (Over.pullback (scalarSpec R S)).obj (affineSpectrum R A) ≅
      affineSpectrum S (S ⊗[R] A) :=
  let e := pullbackSymmetry _ _ ≪≫ pullbackSpecIso' R S A
  have h : e.hom.IsOver (Spec (CommRingCat.of S)) := inferInstance
  Over.isoMk e ((Scheme.Hom.isOver_iff (Spec (CommRingCat.of S))).mp h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem spectrumBaseChangeIso_inv_fst [CommRing A] [Algebra R A] :
    (spectrumBaseChangeIso (R := R) (S := S) (A := A)).inv.left ≫
      pullback.fst (affineSpectrum R A).hom (scalarSpec R S) =
      Spec.map (CommRingCat.ofHom (includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) := by
  change (pullbackSpecIso' R S A).inv ≫ (pullbackSymmetry _ _).inv ≫
      pullback.fst _ _ = _
  rw [pullbackSymmetry_inv_comp_fst]
  exact pullbackSpecIso_inv_snd R S A

set_option backward.isDefEq.respectTransparency false in
def hopfSpectrumBaseChangeIso [CommRing A] [HopfAlgebra R A] :
    (scalarExtension R S).obj (HopfSpectrum R A) ≅ HopfSpectrum S (S ⊗[R] A) := by
  let e : ((scalarExtension R S).obj (HopfSpectrum R A)).X ≅
      (HopfSpectrum S (S ⊗[R] A)).X := spectrumBaseChangeIso
  letI : IsMonHom e.hom := inferInstanceAs (IsMonHom
    ((pullbackSymmetry _ _ ≪≫ pullbackSpecIso' R S A).hom.asOver (Spec (CommRingCat.of S))))
  exact Grp.mkIso e (IsMonHom.one_hom (f := e.hom)) (IsMonHom.mul_hom (f := e.hom))

set_option backward.isDefEq.respectTransparency false in
def hopfSpectrumIsoOfBialgEquiv {S : Type u} [CommRing S]
    [CommRing A] [CommRing B] [HopfAlgebra S A] [HopfAlgebra S B] (e : A ≃ₐc[S] B) :
    HopfSpectrum S B ≅ HopfSpectrum S A :=
  (hopfSpec (CommRingCat.of S)).mapIso (CommHopfAlgCat.isoMk e).op

set_option backward.isDefEq.respectTransparency false in
def genericBialgEquiv [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra S B]
    [Algebra R B] [IsScalarTower R S B] (f : GenericFibre R S A B) : S ⊗[R] A ≃ₐc[S] B := by
  let l := AlgHom.liftEquiv R S A B f.inclusion
  have hl : l.toLinearMap = f.baseChange.equiv.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    exact (f.baseChange.equiv_tmul s a).symm
  let e := AlgEquiv.ofBijective l (show Function.Bijective l.toLinearMap from hl ▸
    f.baseChange.equiv.bijective)
  refine BialgEquiv.ofAlgEquiv e ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    ext a
    change Bialgebra.counitAlgHom S B (l (1 ⊗ₜ[R] a)) =
      Bialgebra.counitAlgHom S (S ⊗[R] A) (1 ⊗ₜ[R] a)
    simpa [l, Algebra.smul_def, Bialgebra.counitAlgHom_apply] using (f.counit a).symm
  · apply Algebra.TensorProduct.ext_ring
    ext a
    change (Algebra.TensorProduct.map l l)
      (Bialgebra.comulAlgHom S (S ⊗[R] A) (1 ⊗ₜ[R] a)) =
      Bialgebra.comulAlgHom S B (l (1 ⊗ₜ[R] a))
    rw [show l (1 ⊗ₜ[R] a) = f.inclusion a by simp [l], ← f.comul]
    simp [Bialgebra.comulAlgHom_apply, ← (Coalgebra.Repr.arbitrary R a).eq,
      TensorProduct.tmul_sum, tensorComparison, l]

@[simp]
theorem genericBialgEquiv_tmul [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra S B]
    [Algebra R B] [IsScalarTower R S B] (f : GenericFibre R S A B) (s : S) (a : A) :
    genericBialgEquiv f (s ⊗ₜ[R] a) = s • f.inclusion a :=
  rfl

def genericFibreIso [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra S B]
    [Algebra R B] [IsScalarTower R S B] (f : GenericFibre R S A B) :
    (scalarExtension R S).obj (HopfSpectrum R A) ≅ HopfSpectrum S B :=
  hopfSpectrumBaseChangeIso ≪≫ (hopfSpectrumIsoOfBialgEquiv (genericBialgEquiv f)).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem genericFibreIso_inv_fst [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra S B]
    [Algebra R B] [IsScalarTower R S B] (f : GenericFibre R S A B) :
    (genericFibreIso f).inv.hom.hom.left ≫
      pullback.fst (HopfSpectrum R A).X.hom (scalarSpec R S) =
      Spec.map (CommRingCat.ofHom f.inclusion.toRingHom) := by
  change Spec.map (CommRingCat.ofHom (genericBialgEquiv f).toAlgEquiv.toRingHom) ≫
      (spectrumBaseChangeIso (A := A) (R := R) (S := S)).inv.left ≫
        pullback.fst (affineSpectrum R A).hom (scalarSpec R S) = _
  rw [spectrumBaseChangeIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  change genericBialgEquiv f (1 ⊗ₜ[R] x) = f.inclusion x
  simp

end ScalarExtension

end

section

section MatrixCoordinates

variable {R S U : Type u} [CommRing R] [CommRing S] [Algebra R S]

theorem map_matrixDeterminant (m : ℕ) :
    MvPolynomial.map (algebraMap R S) (matrixDeterminant R m) = matrixDeterminant S m := by
  unfold matrixDeterminant
  exact ((MvPolynomial.map (algebraMap R S)).map_det _).trans
    (congrArg Matrix.det (Matrix.ext fun i j => MvPolynomial.map_X (algebraMap R S) (i, j)))

@[simp]
theorem matrixCoordinateMap_algebraMap (m : ℕ)
    (x : MvPolynomial (ULift.{u} (Fin m) × ULift.{u} (Fin m)) R) :
    matrixCoordinateMap R S m (algebraMap _ _ x) =
      algebraMap _ _ (MvPolynomial.map (algebraMap R S) x) := by
  unfold matrixCoordinateMap IsLocalization.Away.map
  letI : IsLocalization.Away (MvPolynomial.map (algebraMap R S) (matrixDeterminant R m))
        (matrixCoordinates S m) := (map_matrixDeterminant (R := R) (S := S) m).symm ▸
      inferInstanceAs (IsLocalization.Away (matrixDeterminant S m) (matrixCoordinates S m))
  exact IsLocalization.map_eq _ _

theorem matrixCoordinateMap_comp [CommRing U] [Algebra R U] [Algebra S U] [IsScalarTower R S U]
    (m : ℕ) :
    (matrixCoordinateMap S U m).comp (matrixCoordinateMap R S m) =
      matrixCoordinateMap R U m := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant R m))
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply, matrixCoordinateMap_algebraMap]
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

def matrixCoordinatesScalarEquiv (m : ℕ) :
    S ⊗[R] matrixCoordinates R m ≃ₐ[S] matrixCoordinates S m := by
  let p := MvPolynomial.algebraTensorAlgEquiv (σ := ULift.{u} (Fin m) × ULift.{u} (Fin m)) R S
  let det := (1 : S) ⊗ₜ[R] matrixDeterminant R m
  have h : (Submonoid.powers det).map p = Submonoid.powers (matrixDeterminant S m) := by
    rw [Submonoid.map_powers]
    simp [det, p, map_matrixDeterminant]
  exact (IsLocalization.Away.tensorProductEquivTMulRight R S (matrixDeterminant R m)
    (matrixCoordinates R m)).trans (IsLocalization.algEquivOfAlgEquiv
      (Localization.Away det) (matrixCoordinates S m) p h)

@[simp]
theorem matrixCoordinatesScalarEquiv_one_tmul (m : ℕ) (x : matrixCoordinates R m) :
    matrixCoordinatesScalarEquiv (R := R) (S := S) m (1 ⊗ₜ[R] x) =
      matrixCoordinateMap R S m x := by
  let e := matrixCoordinatesScalarEquiv (R := R) (S := S) m
  suffices h : e.toRingHom.comp (includeRight : matrixCoordinates R m →ₐ[R] _).toRingHom =
      matrixCoordinateMap R S m from DFunLike.congr_fun h x
  apply IsLocalization.ringHom_ext (Submonoid.powers (matrixDeterminant R m))
  apply RingHom.ext
  intro p
  change e (1 ⊗ₜ[R] (algebraMap _ _ p)) = matrixCoordinateMap R S m (algebraMap _ _ p)
  simp only [e, matrixCoordinatesScalarEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul, IsLocalization.algEquivOfAlgEquiv_eq,
    MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul, matrixCoordinateMap_algebraMap]

theorem matrixCoordinates_finitePresentation (R : Type u) [CommRing R] (m : ℕ) :
    Algebra.FinitePresentation R (matrixCoordinates R m) := by
  exact Algebra.FinitePresentation.trans R
    (MvPolynomial (ULift.{u} (Fin m) × ULift.{u} (Fin m)) R) (matrixCoordinates R m)

end MatrixCoordinates

end

section

set_option backward.isDefEq.respectTransparency false

section BaseChangeGeometry

variable {Y Z : Scheme.{u}} (b : Z ⟶ Y) {A B : Over Y} (f : A ⟶ B)

@[reassoc]
theorem overPullbackMap_fst :
    ((Over.pullback b).map f).left ≫ pullback.fst B.hom b =
      pullback.fst A.hom b ≫ f.left :=
  pullback.lift_fst _ _ _

theorem overPullbackMap_isPullback :
    IsPullback ((Over.pullback b).map f).left (pullback.fst A.hom b)
      (pullback.fst B.hom b) f.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd B.hom b) (h₂₂ := B.hom) (v₁₃ := b)
  · have h : ((Over.pullback b).map f).left ≫ pullback.snd B.hom b =
        pullback.snd A.hom b := Over.w _
    rw [h, Over.w]
    exact (IsPullback.of_hasPullback A.hom b).flip
  · exact overPullbackMap_fst b f
  · exact (IsPullback.of_hasPullback B.hom b).flip

theorem property_overPullbackMap (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hf : P f.left) : P ((Over.pullback b).map f).left :=
  MorphismProperty.of_isPullback (overPullbackMap_isPullback b f).flip hf


end BaseChangeGeometry

variable {R S U A B A' B' : Type u}
  [CommRing R] [CommRing S] [Algebra R S]

theorem scalarSpec_tower [CommRing U] [Algebra R U] [Algebra S U] [IsScalarTower R S U] :
    scalarSpec S U ≫ scalarSpec R S = scalarSpec R U := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

section GenericNaturality

variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [HopfAlgebra R A] [HopfAlgebra R B] [HopfAlgebra S A'] [HopfAlgebra S B']
  [Algebra R A'] [Algebra R B'] [IsScalarTower R S A'] [IsScalarTower R S B']

@[reassoc]
theorem genericFibreIso_naturality (p : GenericFibre R S A A') (q : GenericFibre R S B B')
    (f : A →ₐc[R] B) (g : A' →ₐc[S] B')
    (h : ∀ a, q.inclusion (f a) = g (p.inclusion a)) :
    (scalarExtension R S).map (spectrumOfHopfHom f) ≫ (genericFibreIso p).hom =
      (genericFibreIso q).hom ≫ spectrumOfHopfHom g := by
  rw [← cancel_epi (genericFibreIso q).inv, ← cancel_mono (genericFibreIso p).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((genericFibreIso q).inv.hom.hom.left ≫
        ((Over.pullback (scalarSpec R S)).map (spectrumOfHopfHom f).hom.hom).left) ≫
          pullback.fst _ _ =
      ((spectrumOfHopfHom g).hom.hom.left ≫ (genericFibreIso p).inv.hom.hom.left) ≫
        pullback.fst _ _
    rw [Category.assoc, overPullbackMap_fst, Category.assoc, genericFibreIso_inv_fst,
      ← Category.assoc (genericFibreIso q).inv.hom.hom.left, genericFibreIso_inv_fst]
    change Spec.map (CommRingCat.ofHom q.inclusion.toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) =
      Spec.map (CommRingCat.ofHom g.toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom p.inclusion.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext h)
  · exact (Over.w _).trans (Over.w _).symm

end GenericNaturality

section GroupAlgebraFibre

variable (R S) (M : Type u) [CommGroup M]

theorem groupAlgebraInclusion_eq_scalarTensor (x : MonoidAlgebra R M) :
    groupAlgebraInclusion R S M x = MonoidAlgebra.scalarTensorEquiv R S (1 ⊗ₜ[R] x) := by
  let e := MonoidAlgebra.scalarTensorEquiv R S (M := M)
  have h : groupAlgebraInclusion R S M = (e.toAlgHom.restrictScalars R).comp includeRight := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp [groupAlgebraInclusion, e, MonoidAlgebra.of, MonoidAlgebra.scalarTensorEquiv_tmul]
    · ext
  exact DFunLike.congr_fun h x

theorem groupAlgebraInclusion_of (m : M) :
    groupAlgebraInclusion R S M (MonoidAlgebra.of R M m) = MonoidAlgebra.of S M m := by
  simp [groupAlgebraInclusion]

@[simp]
theorem groupAlgebraInclusion_single_one (m : M) :
    groupAlgebraInclusion R S M (MonoidAlgebra.single m 1) = MonoidAlgebra.single m 1 :=
  groupAlgebraInclusion_of R S M m

def groupAlgebraFibre :
    GenericFibre R S (MonoidAlgebra R M) (MonoidAlgebra S M) where
  inclusion := groupAlgebraInclusion R S M
  baseChange := IsBaseChange.of_equiv (MonoidAlgebra.scalarTensorEquiv R S (M := M)).toLinearEquiv
    (fun x => (groupAlgebraInclusion_eq_scalarTensor R S M x).symm)
  comul := by
    have e : (tensorComparison R S (groupAlgebraInclusion R S M)
        (groupAlgebraInclusion R S M)).comp (Bialgebra.comulAlgHom R (MonoidAlgebra R M)) =
        ((Bialgebra.comulAlgHom S (MonoidAlgebra S M)).restrictScalars R).comp
          (groupAlgebraInclusion R S M) := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        simp [tensorComparison]
      · ext
    exact DFunLike.congr_fun e
  counit := by
    have e : (Algebra.ofId R S).comp (Bialgebra.counitAlgHom R (MonoidAlgebra R M)) =
        ((Bialgebra.counitAlgHom S (MonoidAlgebra S M)).restrictScalars R).comp
          (groupAlgebraInclusion R S M) := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        simp
      · ext
    exact DFunLike.congr_fun e
  antipode := by
    have e : (groupAlgebraInclusion R S M).comp (HopfAlgebra.antipodeAlgHom R (MonoidAlgebra R M)) =
        ((HopfAlgebra.antipodeAlgHom S (MonoidAlgebra S M)).restrictScalars R).comp
          (groupAlgebraInclusion R S M) := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        simp [MonoidAlgebra.antipode_single]
      · ext
    exact DFunLike.congr_fun e

theorem groupAlgebraInclusion_characterMap (f : M →* M) (x : MonoidAlgebra R M) :
    groupAlgebraInclusion R S M (MonoidAlgebra.mapDomainBialgHom R f x) =
      MonoidAlgebra.mapDomainBialgHom S f (groupAlgebraInclusion R S M x) := by
  have e : (groupAlgebraInclusion R S M).comp (MonoidAlgebra.mapDomainBialgHom R f).toAlgHom =
      ((MonoidAlgebra.mapDomainBialgHom S f).toAlgHom.restrictScalars R).comp
        (groupAlgebraInclusion R S M) := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp
    · ext
  exact DFunLike.congr_fun e x

end GroupAlgebraFibre

section MatrixBaseChange

def matrixBaseChangeIso (m : ℕ) :
    (Over.pullback (scalarSpec R S)).obj (matrixScheme R m) ≅ matrixScheme S m :=
  spectrumBaseChangeIso ≪≫ (algSpec (CommRingCat.of S)).mapIso
    (CommAlgCat.isoMk (matrixCoordinatesScalarEquiv (R := R) (S := S) m)).symm.op

@[reassoc]
theorem matrixBaseChangeIso_inv_fst (m : ℕ) :
    (matrixBaseChangeIso (R := R) (S := S) m).inv.left ≫
      pullback.fst (matrixScheme R m).hom (scalarSpec R S) =
      Spec.map (CommRingCat.ofHom (matrixCoordinateMap R S m)) := by
  change Spec.map (CommRingCat.ofHom (matrixCoordinatesScalarEquiv (R := R) (S := S) m).toRingHom) ≫
      (spectrumBaseChangeIso (R := R) (S := S) (A := matrixCoordinates R m)).inv.left ≫
        pullback.fst _ _ = _
  rw [spectrumBaseChangeIso_inv_fst, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (matrixCoordinatesScalarEquiv_one_tmul m))

@[reassoc]
theorem matrixBaseChangeIso_hom_project (m : ℕ) :
    (matrixBaseChangeIso (R := R) (S := S) m).hom.left ≫
      Spec.map (CommRingCat.ofHom (matrixCoordinateMap R S m)) =
      pullback.fst (matrixScheme R m).hom (scalarSpec R S) := by
  rw [← matrixBaseChangeIso_inv_fst, ← Category.assoc]
  simp only [← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp]

theorem matrixBaseChange_isPullback (m : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (matrixCoordinateMap R S m))) (matrixScheme S m).hom
      (matrixScheme R m).hom (scalarSpec R S) := by
  let F := Over.forget (Spec (CommRingCat.of S))
  refine (IsPullback.of_hasPullback (matrixScheme R m).hom (scalarSpec R S)).of_iso'
    (F.mapIso (matrixBaseChangeIso (R := R) (S := S) m).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change (matrixBaseChangeIso (R := R) (S := S) m).inv.left ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (matrixCoordinateMap R S m)) ≫ 𝟙 _
    simpa only [Category.comp_id] using matrixBaseChangeIso_inv_fst (R := R) (S := S) m
  · change (matrixBaseChangeIso (R := R) (S := S) m).inv.left ≫ pullback.snd _ _ =
        (matrixScheme S m).hom ≫ 𝟙 _
    rw [Category.comp_id]
    exact Over.w (matrixBaseChangeIso (R := R) (S := S) m).inv

end MatrixBaseChange

end

section

section CoordinateGroups

variable {R B C N : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing N]
  [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R N]

def coordinateHom (f : HopfSpectrum R C ⟶ HopfSpectrum R B) : B →ₐc[R] C :=
  ((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage f).unop.hom

@[simp]
theorem spectrum_coordinateHom (f : HopfSpectrum R C ⟶ HopfSpectrum R B) :
    spectrumOfHopfHom (coordinateHom f) = f :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of R)).map_preimage f


theorem spectrumOfHopfHom_injective :
    Function.Injective (fun f : B →ₐc[R] C => spectrumOfHopfHom f) := by
  intro f g h
  let ff := hopfSpec.fullyFaithful (R := CommRingCat.of R)
  have e : (CommHopfAlgCat.ofHom f).op = (CommHopfAlgCat.ofHom g).op :=
    ff.map_injective h
  exact congrArg (fun a : op (CommHopfAlgCat.of R C) ⟶ op (CommHopfAlgCat.of R B) =>
    a.unop.hom) e

theorem fullKernel_of_spectrumPullback (q : B →ₐc[R] C) (j : C →ₐc[R] N)
    (hj : Function.Surjective j)
    (h : IsPullback (spectrumOfHopfHom j).hom.hom (toUnit (HopfSpectrum R N).X)
      (spectrumOfHopfHom q).hom.hom η[(HopfSpectrum R B).X]) : IsFullKernel q j := by
  let q' := CommRingCat.ofHom q.toAlgHom.toRingHom
  let j' := CommRingCat.ofHom j.toAlgHom.toRingHom
  let ε := Bialgebra.counitAlgHom R B
  let e' := CommRingCat.ofHom ε.toRingHom
  let unit := CommRingCat.ofHom (algebraMap R N)
  have hs : IsPullback (Spec.map j') (Spec.map unit) (Spec.map q') (Spec.map e') :=
    h.map (Over.forget (Spec (CommRingCat.of R)))
  have hp : IsPushout e' q' unit j' :=
    (IsPullback.of_map_of_faithful Scheme.Spec hs).unop
  apply (CentralCoverSpreading.isFullKernel_iff_affine_points q j).mpr
  refine ⟨hj, fun b => (ConcreteCategory.congr_hom hp.w b).symm, ?_⟩
  intro T _ _ f hf
  let f' := CommRingCat.ofHom f.toRingHom
  let a := CommRingCat.ofHom (algebraMap R T)
  have hf' : e' ≫ a = q' ≫ f' := CommRingCat.hom_ext (RingHom.ext fun b => (hf b).symm)
  let l := hp.desc a f' hf'
  let g : N →ₐ[R] T := { l.hom with
    commutes' := fun r => ConcreteCategory.congr_hom (hp.inl_desc a f' hf') r }
  refine ⟨g, AlgHom.ext (fun c => ConcreteCategory.congr_hom (hp.inr_desc a f' hf') c), ?_⟩
  intro g' hg
  apply AlgHom.ext
  intro n
  obtain ⟨c, rfl⟩ := hj n
  exact (DFunLike.congr_fun hg c).trans
    (ConcreteCategory.congr_hom (hp.inr_desc a f' hf') c).symm

end CoordinateGroups

set_option backward.isDefEq.respectTransparency false in
theorem hopfKernelCentral {k C M : Type u} [Field k] [CommRing C] [HopfAlgebra k C] [CommGroup M]
    (j : C →ₐc[k] MonoidAlgebra k M)
    (h : Centralizes (𝟙 (HopfSpectrum k C)) (spectrumOfHopfHom j).hom.hom) :
    Specs.IntegralCentralQuotient.IsCentral j := by
  let N := MonoidAlgebra k M
  let U := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (C ⊗[k] N)))
  let a : C →ₐ[k] C ⊗[k] N := includeLeft
  let b : N →ₐ[k] C ⊗[k] N := includeRight
  let c := b.comp j.toAlgHom
  let V := (HopfSpectrum k C).X
  let v : U ⟶ V := spectrumOfAlgHom a
  let w : U ⟶ V := spectrumOfAlgHom c
  have hComm := ((centralizes_iff _ _).mp h U (spectrumOfAlgHom b) v).eq.symm
  have hs : v * w = w * v := by
    have hw : w = spectrumOfAlgHom b ≫ (spectrumOfHopfHom j).hom.hom :=
      spectrumOfAlgHom_comp j.toAlgHom b
    rw [hw]
    change (v ≫ 𝟙 V) * _ = _ * (v ≫ 𝟙 V) at hComm
    simpa only [Category.comp_id] using hComm
  let f := Spec.mapMulEquiv (R := k) (S := C) (T := C ⊗[k] N)
  have hc : WithConv.toConv a * WithConv.toConv c = WithConv.toConv c * WithConv.toConv a := by
    apply f.injective
    rw [map_mul, map_mul]
    exact hs
  have he := congrArg WithConv.ofConv hc
  rw [eval_comul, eval_comul] at he
  have hl : Algebra.TensorProduct.lift a c (fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.map (AlgHom.id k C) j.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [Algebra.TensorProduct.map_tmul]
    simp [a, b, c]
    rfl
  have hr : Algebra.TensorProduct.lift c a (fun _ _ => Commute.all _ _) =
      (Algebra.TensorProduct.comm k N C).toAlgHom.comp
        (Algebra.TensorProduct.map j.toAlgHom (AlgHom.id k C)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
    simp [a, b, c, mul_comm]
  unfold Specs.IntegralCentralQuotient.IsCentral Specs.IntegralCentralQuotient.rightCoaction
  rw [hl, hr, AlgHom.comp_assoc] at he
  exact he

section CoverCoordinates

variable {k : Type u} [Field k] {G H : AffineAlgebraicGroup k}
  {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}

structure CoverCoordinates (T : SplitCoverData G H q N) {m : ℕ} (i : MatrixEmbedding G m) where
  target : HopfAlgebraCategory k
  source : HopfAlgebraCategory k
  targetFiniteType : Algebra.FiniteType k target
  sourceFiniteType : Algebra.FiniteType k source
  targetIso : HopfSpectrum k target ≅ G.val
  sourceIso : HopfSpectrum k source ≅ H.val
  kernelIso : HopfSpectrum k (KernelCoordinates k T.exponents) ≅ N.group
  sourceTorusIso : HopfSpectrum k (TorusCoordinates k T.indices) ≅ T.sourceTorus.group
  targetTorusIso : HopfSpectrum k (TorusCoordinates k T.indices) ≅ T.targetTorus.group
  diagram : Diagram k target source T.exponents
  coverFinite : letI := diagram.cover.toAlgHom.toAlgebra; Module.Finite target source
  coverFaithfullyFlat : letI := diagram.cover.toAlgHom.toAlgebra; Module.FaithfullyFlat target source
  coverAgrees : spectrumOfHopfHom diagram.cover ≫ targetIso.hom = sourceIso.hom ≫ q
  kernelAgrees : spectrumOfHopfHom diagram.kernel ≫ sourceIso.hom = kernelIso.hom ≫ N.inclusion
  sourceTorusAgrees : spectrumOfHopfHom diagram.sourceTorus ≫ sourceIso.hom =
    sourceTorusIso.hom ≫ T.sourceTorus.inclusion
  targetTorusAgrees : spectrumOfHopfHom diagram.targetTorus ≫ targetIso.hom =
    targetTorusIso.hom ≫ T.targetTorus.inclusion
  torusMapAgrees : integralPowerMap k T.exponents ≫ targetTorusIso.hom =
    sourceTorusIso.hom ≫ T.restriction
  matrix : matrixCoordinates k m →ₐ[k] target
  matrixSurj : Function.Surjective matrix
  matrixAgrees : Spec.map (CommRingCat.ofHom matrix.toRingHom) =
    targetIso.hom.hom.hom.left ≫ i.inclusion.left

abbrev underlyingGroup (R : Type u) [CommRing R] :=
  Grp.forget (OverBase R) ⋙ Over.forget (Spec (CommRingCat.of R))

set_option backward.isDefEq.respectTransparency false in
theorem property_of_groupIso {R : Type u} [CommRing R]
    {G₁ G₂ H₁ H₂ : Grp (OverBase R)} {q₁ : H₁ ⟶ G₁} {q₂ : H₂ ⟶ G₂}
    (eH : H₁ ≅ H₂) (eG : G₁ ≅ G₂) (h : q₁ ≫ eG.hom = eH.hom ≫ q₂)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hp : P q₂.hom.hom.left) :
    P q₁.hom.hom.left := by
  let F := underlyingGroup R
  have he := congrArg F.map h
  rw [Functor.map_comp, Functor.map_comp] at he
  change F.map q₁ ≫ F.map eG.hom = F.map eH.hom ≫ F.map q₂ at he
  change P (F.map q₁)
  change P (F.map q₂) at hp
  exact (P.cancel_right_of_respectsIso _ (F.map eG.hom)).mp (he.symm ▸
    (P.cancel_left_of_respectsIso (F.map eH.hom) _).mpr hp)

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
theorem coverCoordinates (hq : IsCentralIsogeny q) (hN : IsSchemeKernel q N)
    (T : SplitCoverData G H q N) {m : ℕ} (i : MatrixEmbedding G m) : Nonempty (CoverCoordinates T i) := by
  obtain ⟨B, hB, ⟨eG⟩⟩ := groupPresentation G
  obtain ⟨C, hC, ⟨eH⟩⟩ := groupPresentation H
  obtain ⟨eT, eS, hPow, ⟨eN⟩⟩ := splitCoverSchemeCoordinates T
  let q₀ := coordinateHom (eH.hom ≫ q ≫ eG.inv)
  let j := coordinateHom (eN.inv ≫ N.inclusion ≫ eH.inv)
  let t := coordinateHom (eT.inv ≫ T.sourceTorus.inclusion ≫ eH.inv)
  let s := coordinateHom (eS.inv ≫ T.targetTorus.inclusion ≫ eG.inv)
  have hq₀ : spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ q := by rw [show spectrumOfHopfHom q₀ = _ from spectrum_coordinateHom _]; simp
  have hj : spectrumOfHopfHom j ≫ eH.hom = eN.inv ≫ N.inclusion := by rw [show spectrumOfHopfHom j = _ from spectrum_coordinateHom _]; simp
  have ht : spectrumOfHopfHom t ≫ eH.hom = eT.inv ≫ T.sourceTorus.inclusion := by rw [show spectrumOfHopfHom t = _ from spectrum_coordinateHom _]; simp
  have hs : spectrumOfHopfHom s ≫ eG.hom = eS.inv ≫ T.targetTorus.inclusion := by rw [show spectrumOfHopfHom s = _ from spectrum_coordinateHom _]; simp
  have hp : integralPowerMap k T.exponents ≫ eS.inv = eT.inv ≫ T.restriction := by
    rw [← cancel_epi eT.hom, ← cancel_mono eS.hom]
    simpa using hPow.symm
  have htorus : t.comp q₀ = (Specs.CentralCoverSpreading.powerPullback k T.exponents).comp s := by
    apply spectrumOfHopfHom_injective
    change spectrumOfHopfHom (t.comp q₀) =
      spectrumOfHopfHom ((Specs.CentralCoverSpreading.powerPullback k T.exponents).comp s)
    rw [spectrumOfHopfHom_comp, spectrumOfHopfHom_comp]
    change spectrumOfHopfHom t ≫ spectrumOfHopfHom q₀ =
      integralPowerMap k T.exponents ≫ spectrumOfHopfHom s
    rw [← cancel_mono eG.hom, Category.assoc, Category.assoc, hs, hq₀,
      ← Category.assoc (spectrumOfHopfHom t), ← Category.assoc (integralPowerMap k T.exponents),
      ht, hp, Category.assoc, Category.assoc, T.restricts.1]
  let F := Grp.forget (OverBase k)
  have hpb : IsPullback (spectrumOfHopfHom j).hom.hom (toUnit _)
      (spectrumOfHopfHom q₀).hom.hom η[(HopfSpectrum k B).X] := by
    refine hN.of_iso' (F.mapIso eN.symm) (F.mapIso eH) (Iso.refl _) (F.mapIso eG) ?_ ?_ ?_ ?_
    · exact (congrArg F.map hj).symm
    · exact toUnit_unique _ _
    · exact (congrArg F.map hq₀).symm
    · change (𝟙 _) ≫ η[G.val.X] = η[(HopfSpectrum k B).X] ≫ eG.hom.hom.hom
      rw [Category.id_comp, IsMonHom.one_hom]
  have hclosed {D : Type u} [CommRing D] [HopfAlgebra k D] (a : B →ₐc[k] D)
      {L : GroupScheme k} (f : L ⟶ G.val) (e : HopfSpectrum k D ≅ L)
      (h : spectrumOfHopfHom a ≫ eG.hom = e.hom ≫ f)
      (hf : IsClosedImmersion f.hom.hom.left) : Function.Surjective a :=
    (hopfMapClosedImmersion k (CommHopfAlgCat.ofHom a)).mp
      (property_of_groupIso e eG h @IsClosedImmersion hf)
  have hjc : Function.Surjective j :=
    (hopfMapClosedImmersion k (CommHopfAlgCat.ofHom j)).mp
      (property_of_groupIso eN.symm eH hj @IsClosedImmersion N.isClosedImmersion)
  have htc : Function.Surjective t :=
    (hopfMapClosedImmersion k (CommHopfAlgCat.ofHom t)).mp
      (property_of_groupIso eT.symm eH ht @IsClosedImmersion T.sourceTorus.isClosedImmersion)
  have hcent : Centralizes (𝟙 (HopfSpectrum k C)) (spectrumOfHopfHom j).hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro U a b
    have h := (centralizes_iff _ _).mp (kernel_is_central hq hN) U
      (a ≫ eN.inv.hom.hom) (b ≫ eH.hom.hom.hom)
    change Commute (a ≫ (spectrumOfHopfHom j).hom.hom) b
    have hj' : (spectrumOfHopfHom j).hom.hom ≫ eH.hom.hom.hom =
        eN.inv.hom.hom ≫ N.inclusion.hom.hom := congrArg F.map hj
    change Commute (a ≫ eN.inv.hom.hom ≫ N.inclusion.hom.hom)
      (b ≫ eH.hom.hom.hom ≫ 𝟙 H.val.X) at h
    simp only [Category.comp_id] at h
    unfold Commute SemiconjBy at h ⊢
    apply (cancel_mono eH.hom.hom.hom).mp
    simpa only [MonObj.mul_comp, Category.assoc, hj'] using h
  let D : Diagram k B C T.exponents := {
    cover := q₀
    sourceTorus := t
    targetTorus := s
    kernel := j
    sourceTorusClosed := htc
    targetTorusClosed := hclosed s T.targetTorus.inclusion eS.symm hs T.targetTorus.isClosedImmersion
    torusSquare := htorus
    kernelFull := fullKernel_of_spectrumPullback q₀ j hjc hpb
    kernelCentral := hopfKernelCentral j hcent }
  have hfin := property_of_groupIso eH eG hq₀ @IsFinite hq.1
  have hflat := property_of_groupIso eH eG hq₀ @Flat hq.2.1
  have hsurj := property_of_groupIso eH eG hq₀ @Surjective hq.2.2.1
  let b : (op (CommAlgCat.of k B)) ⟶ (op (CommAlgCat.of k (matrixCoordinates k m))) :=
    (algSpec.fullyFaithful (R := CommRingCat.of k)).preimage
      (eG.hom.hom.hom ≫ i.inclusion)
  let f := b.unop.hom
  have hm : Spec.map (CommRingCat.ofHom f.toRingHom) =
      eG.hom.hom.hom.left ≫ i.inclusion.left :=
    congrArg (fun z => z.left) ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage
      (eG.hom.hom.hom ≫ i.inclusion))
  have hmat : Function.Surjective f := by
    let r := CommRingCat.ofHom f.toRingHom
    have hclosed : IsClosedImmersion (Spec.map r) := by
      rw [hm]
      exact MorphismProperty.RespectsIso.precomp @IsClosedImmersion
        ((underlyingGroup k).map eG.hom) i.inclusion.left i.closed
    letI := hclosed
    have hs := (Spec.map r).app_surjective ⊤ (isAffineOpen_top _)
    have e : (Scheme.ΓSpecIso _).inv ≫ (Spec.map r).appTop ≫ (Scheme.ΓSpecIso _).hom = r := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    change Function.Surjective r
    rw [← e]
    exact (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.surjective.comp
      (hs.comp (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.surjective)
  letI : Algebra B C := q₀.toAlgHom.toAlgebra
  refine ⟨⟨B, C, hB, hC, eG, eH, eN.symm, eT.symm, eS.symm, D, ?_, ?_, hq₀, hj, ht, hs,
    hp, f, hmat, hm⟩⟩
  · exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp hfin)
  · exact RingHom.faithfullyFlat_algebraMap_iff.mp ((flat_and_surjective_SpecMap_iff _).mp ⟨hflat, hsurj⟩)

end CoverCoordinates

end

section

set_option backward.isDefEq.respectTransparency false

attribute [local instance] IntegralDiagram.targetRing IntegralDiagram.sourceRing
  IntegralDiagram.targetHopf IntegralDiagram.sourceHopf

section LocalizedModels

variable {A R E : Type u} [CommRing A] [CommRing R] [Field E] [Algebra A R] [Algebra A E]
    [Algebra R E] [IsScalarTower A R E]
    {G H : AffineAlgebraicGroup E} {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}
    {T : SplitCoverData G H q N} {m : ℕ} {i : MatrixEmbedding G m}

def affineModelOfHopf (R B : Type u) [CommRing R] [CommRing B] [HopfAlgebra R B]
    (h : Algebra.FinitePresentation R B) : AffineModel R := by
  refine ⟨HopfSpectrum R B, inferInstanceAs (IsAffine (Spec (CommRingCat.of B))), ?_⟩
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R B)))
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr (RingHom.finitePresentation_algebraMap.mpr h)

def genericAmbient (C : CoverCoordinates T i) :
    E ⊗[A] matrixCoordinates A m →ₐ[E] C.target :=
  C.matrix.comp (matrixCoordinatesScalarEquiv (R := A) (S := E) m).toAlgHom

variable (C : CoverCoordinates T i)
    [Algebra R C.target] [Algebra R C.source] [IsScalarTower R E C.target] [IsScalarTower R E C.source]

def integralMatrixCoordinates (D : IntegralDiagram C.diagram (genericAmbient (A := A) C) R) :
    matrixCoordinates R m →ₐ[R] D.target :=
  D.ambientMap.comp (matrixCoordinatesScalarEquiv (R := A) (S := R) m).symm.toAlgHom

theorem integralMatrixCoordinates_agree (D : IntegralDiagram C.diagram (genericAmbient (A := A) C) R)
    (x : matrixCoordinates R m) :
    D.genericTarget.inclusion (integralMatrixCoordinates C D x) =
      C.matrix (matrixCoordinateMap R E m x) := by
  let e := matrixCoordinatesScalarEquiv (R := A) (S := R) m
  letI : Algebra A C.target := ((algebraMap R C.target).comp (algebraMap A R)).toAlgebra
  letI : IsScalarTower A R C.target := IsScalarTower.of_algebraMap_eq' rfl
  let f : matrixCoordinates R m →ₐ[R] matrixCoordinates E m :=
    { matrixCoordinateMap R E m with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R E (matrixCoordinates E m)]
        change matrixCoordinateMap R E m (algebraMap R (matrixCoordinates R m) r) =
          algebraMap E (matrixCoordinates E m) (algebraMap R E r)
        rw [IsScalarTower.algebraMap_apply R (MvPolynomial (ULift.{u} (Fin m) × ULift.{u} (Fin m)) R) (matrixCoordinates R m),
          matrixCoordinateMap_algebraMap,
          IsScalarTower.algebraMap_apply E (MvPolynomial (ULift.{u} (Fin m) × ULift.{u} (Fin m)) E) (matrixCoordinates E m)]
        exact congrArg (algebraMap (MvPolynomial (ULift.{u} (Fin m) × ULift.{u} (Fin m)) E) (matrixCoordinates E m))
          (MvPolynomial.map_C (algebraMap R E) r) }
  have hf (a) : f a = matrixCoordinateMap R E m a := rfl
  let g := (C.matrix.restrictScalars R).comp f
  have eq : D.genericTarget.inclusion.comp D.ambientMap = g.comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro y
    change D.genericTarget.inclusion (D.ambientMap (1 ⊗ₜ[A] y)) = C.matrix (f (e (1 ⊗ₜ[A] y)))
    rw [D.ambientAgrees, hf, show e (1 ⊗ₜ[A] y) = matrixCoordinateMap A R m y from
      matrixCoordinatesScalarEquiv_one_tmul m y, ← RingHom.comp_apply, matrixCoordinateMap_comp]
    change C.matrix (matrixCoordinatesScalarEquiv (R := A) (S := E) m (1 ⊗ₜ[A] y)) = _
    rw [matrixCoordinatesScalarEquiv_one_tmul]
  have h := DFunLike.congr_fun eq (e.symm x)
  change D.genericTarget.inclusion (integralMatrixCoordinates C D x) = C.matrix (f (e (e.symm x))) at h
  rwa [e.apply_symm_apply, hf] at h

theorem integralMatrix_generic (D : IntegralDiagram C.diagram (genericAmbient (A := A) C) R) :
    ((genericFibreIso D.genericTarget) ≪≫ C.targetIso).hom.hom.hom.left ≫ i.inclusion.left ≫
        Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E m)) =
      pullback.fst (HopfSpectrum R D.target).X.hom (scalarSpec R E) ≫
        (spectrumOfAlgHom (integralMatrixCoordinates C D)).left := by
  let F := underlyingGroup E
  let e := genericFibreIso D.genericTarget
  rw [← cancel_epi (F.map e.inv)]
  change F.map e.inv ≫ F.map (e.hom ≫ C.targetIso.hom) ≫ i.inclusion.left ≫ _ = _
  have he : F.map e.inv ≫ F.map (e.hom ≫ C.targetIso.hom) = F.map C.targetIso.hom := by
    rw [← F.map_comp, e.inv_hom_id_assoc]
  rw [← Category.assoc (F.map e.inv), he, ← Category.assoc (F.map e.inv)]
  change (C.targetIso.hom.hom.hom.left ≫ i.inclusion.left ≫
      Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E m))) =
    (e.inv.hom.hom.left ≫ pullback.fst (HopfSpectrum R D.target).X.hom (scalarSpec R E)) ≫ _
  rw [← Category.assoc, ← C.matrixAgrees, genericFibreIso_inv_fst]
  change Spec.map (CommRingCat.ofHom C.matrix.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E m)) =
    Spec.map (CommRingCat.ofHom D.genericTarget.inclusion.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (integralMatrixCoordinates C D).toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (integralMatrixCoordinates_agree C D)).symm

set_option maxHeartbeats 650000 in
def integralModelOfDiagram [IsDomain R] [IsFractionRing R E]
    (D : IntegralDiagram C.diagram (genericAmbient (A := A) C) R) :
    IntegralModel (R := R) T i := by
  let B := D.target
  let W := D.source
  let U := TorusCoordinates R T.indices
  let Z := KernelCoordinates R T.exponents
  let q₀ := spectrumOfHopfHom D.diagram.cover
  let j₀ := spectrumOfHopfHom D.diagram.kernel
  let t₀ := spectrumOfHopfHom D.diagram.sourceTorus
  let s₀ := spectrumOfHopfHom D.diagram.targetTorus
  let eT := groupAlgebraFibre R E (ULift.{u} (Multiplicative (T.indices → ℤ)))
  let eN := groupAlgebraFibre R E (ULift.{u} (∀ a, Multiplicative (ZMod (T.exponents a))))
  let jm := spectrumOfAlgHom (integralMatrixCoordinates C D)
  letI : Algebra B W := D.diagram.cover.toAlgHom.toAlgebra
  have hf : IsFinite q₀.hom.hom.left :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr D.coverFinite)
  have hff : Flat q₀.hom.hom.left ∧ Surjective q₀.hom.hom.left :=
    (flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr D.coverFaithfullyFlat)
  have hp : LocallyOfFinitePresentation q₀.hom.hom.left :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr D.coverPresentation)
  have hclosed : IsClosedImmersion j₀.hom.hom.left :=
    IsClosedImmersion.spec_of_surjective _ D.diagram.kernelFull.1
  have hk := CentralCoverSpreading.fullKernel_isPullback _ _ D.diagram.kernelFull
  have hkScheme := hk.map (Over.forget (Spec (CommRingCat.of R)))
  have hflat : Flat (HopfSpectrum R B).X.hom :=
    show Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) from
      Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr D.targetFlat)
  refine {
    target := affineModelOfHopf R B D.targetPresentation
    targetFlat := hflat
    source := affineModelOfHopf R W D.sourcePresentation
    kernel := affineModelOfHopf R Z D.kernelPresentation
    kernelFinite := MorphismProperty.of_isPullback hkScheme hf
    kernelFlat := MorphismProperty.of_isPullback hkScheme hff.1
    sourceTorus := affineModelOfHopf R U D.torusPresentation
    targetTorus := affineModelOfHopf R U D.torusPresentation
    map := q₀
    kernelInclusion := j₀
    sourceTorusInclusion := t₀
    targetTorusInclusion := s₀
    torusMap := integralPowerMap R T.exponents
    torsor := finiteKernelTorsorOfKernel q₀ j₀ hf hff.1 hff.2 hp hclosed hk
    kernelCentral := central_translation D.diagram.kernel D.diagram.kernelCentral (fst _ _) (snd _ _)
    sourceTorusClosed := IsClosedImmersion.spec_of_surjective _ D.diagram.sourceTorusClosed
    targetTorusClosed := IsClosedImmersion.spec_of_surjective _ D.diagram.targetTorusClosed
    torusCompatibility := ?_
    splitSourceTorus := Iso.refl _
    splitTargetTorus := Iso.refl _
    splitTorusMap := by simp
    splitKernel := Iso.refl _
    genericTarget := genericFibreIso D.genericTarget ≪≫ C.targetIso
    genericSource := genericFibreIso D.genericSource ≪≫ C.sourceIso
    genericKernel := genericFibreIso eN ≪≫ C.kernelIso
    genericSourceTorus := genericFibreIso eT ≪≫ C.sourceTorusIso
    genericTargetTorus := genericFibreIso eT ≪≫ C.targetTorusIso
    genericMap := ?_
    genericKernelInclusion := ?_
    genericSourceTorusInclusion := ?_
    genericTargetTorusInclusion := ?_
    genericTorusMap := ?_
    matrixInclusion := jm
    matrixClosed := IsClosedImmersion.spec_of_surjective _
      (D.ambientClosed.comp (matrixCoordinatesScalarEquiv (R := A) (S := R) m).symm.surjective)
    genericMatrix := integralMatrix_generic C D
    matrixClosure := genericFibreImage (E := E) _ hflat jm.left }
  · exact (spectrumOfHopfHom_comp _ _).symm.trans
      ((congrArg spectrumOfHopfHom D.diagram.torusSquare).trans (spectrumOfHopfHom_comp _ _))
  · have e := genericFibreIso_naturality_assoc D.genericTarget D.genericSource
      D.diagram.cover C.diagram.cover D.coverAgrees C.targetIso.hom
    change (scalarExtension R E).map q₀ ≫ (genericFibreIso D.genericTarget).hom ≫ C.targetIso.hom = _
      at e
    change (scalarExtension R E).map q₀ ≫ (genericFibreIso D.genericTarget).hom ≫ C.targetIso.hom =
      ((genericFibreIso D.genericSource).hom ≫ C.sourceIso.hom) ≫ q
    exact e.trans ((congrArg ((genericFibreIso D.genericSource).hom ≫ ·) C.coverAgrees).trans
      (Category.assoc _ C.sourceIso.hom q).symm)
  · have e := genericFibreIso_naturality_assoc D.genericSource eN D.diagram.kernel C.diagram.kernel
      (fun x => D.kernelAgrees x) C.sourceIso.hom
    change (scalarExtension R E).map j₀ ≫ (genericFibreIso D.genericSource).hom ≫ C.sourceIso.hom = _
      at e
    change (scalarExtension R E).map j₀ ≫ (genericFibreIso D.genericSource).hom ≫ C.sourceIso.hom =
      ((genericFibreIso eN).hom ≫ C.kernelIso.hom) ≫ N.inclusion
    exact e.trans ((congrArg ((genericFibreIso eN).hom ≫ ·) C.kernelAgrees).trans
      (Category.assoc _ C.kernelIso.hom N.inclusion).symm)
  · have e := genericFibreIso_naturality_assoc D.genericSource eT D.diagram.sourceTorus
      C.diagram.sourceTorus (fun x => D.sourceTorusAgrees x) C.sourceIso.hom
    change (scalarExtension R E).map t₀ ≫ (genericFibreIso D.genericSource).hom ≫ C.sourceIso.hom = _
      at e
    change (scalarExtension R E).map t₀ ≫ (genericFibreIso D.genericSource).hom ≫ C.sourceIso.hom =
      ((genericFibreIso eT).hom ≫ C.sourceTorusIso.hom) ≫ T.sourceTorus.inclusion
    exact e.trans ((congrArg ((genericFibreIso eT).hom ≫ ·) C.sourceTorusAgrees).trans
      (Category.assoc _ C.sourceTorusIso.hom T.sourceTorus.inclusion).symm)
  · have e := genericFibreIso_naturality_assoc D.genericTarget eT D.diagram.targetTorus
      C.diagram.targetTorus (fun x => D.targetTorusAgrees x) C.targetIso.hom
    change (scalarExtension R E).map s₀ ≫ (genericFibreIso D.genericTarget).hom ≫ C.targetIso.hom = _
      at e
    change (scalarExtension R E).map s₀ ≫ (genericFibreIso D.genericTarget).hom ≫ C.targetIso.hom =
      ((genericFibreIso eT).hom ≫ C.targetTorusIso.hom) ≫ T.targetTorus.inclusion
    exact e.trans ((congrArg ((genericFibreIso eT).hom ≫ ·) C.targetTorusAgrees).trans
      (Category.assoc _ C.targetTorusIso.hom T.targetTorus.inclusion).symm)
  · change (scalarExtension R E).map (integralPowerMap R T.exponents) ≫
        (genericFibreIso eT).hom ≫ C.targetTorusIso.hom =
      ((genericFibreIso eT).hom ≫ C.sourceTorusIso.hom) ≫ T.restriction
    have e := genericFibreIso_naturality_assoc eT eT
      (MonoidAlgebra.mapDomainBialgHom R (powerOnLiftedCharacters T.exponents))
      (MonoidAlgebra.mapDomainBialgHom E (powerOnLiftedCharacters T.exponents))
      (groupAlgebraInclusion_characterMap _ _ _ _) C.targetTorusIso.hom
    exact e.trans ((congrArg ((genericFibreIso eT).hom ≫ ·) C.torusMapAgrees).trans
      (Category.assoc _ C.sourceTorusIso.hom T.restriction).symm)

end LocalizedModels

end

section

set_option backward.isDefEq.respectTransparency false

section ModelsBaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

def affineModelBaseChange (M : AffineModel R) : AffineModel S := by
  letI : IsAffine M.val.X.left := M.property.1
  letI : IsAffineHom M.val.X.hom := isAffineHom_of_isAffine M.val.X.hom
  letI : LocallyOfFinitePresentation M.val.X.hom := M.property.2
  refine ⟨(scalarExtension R S).obj M.val, ?_, ?_⟩
  · letI : IsAffineHom (pullback.snd M.val.X.hom (scalarSpec R S)) :=
      MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ (isAffineHom_of_isAffine M.val.X.hom)
    exact isAffine_of_isAffineHom (pullback.snd M.val.X.hom (scalarSpec R S))
  · exact inferInstanceAs (LocallyOfFinitePresentation (pullback.snd M.val.X.hom (scalarSpec R S)))

theorem kernelSquareBaseChange {G H Z : Grp (OverBase R)} (q : H ⟶ G) (j : Z ⟶ H)
    (h : IsPullback j.hom.hom (toUnit Z.X) q.hom.hom η[G.X]) :
    let F := scalarExtension R S
    IsPullback (F.map j).hom.hom (toUnit (F.obj Z).X) (F.map q).hom.hom η[(F.obj G).X] := by
  let P := Over.pullback (scalarSpec R S)
  let F := P.mapGrp
  let e := Functor.Monoidal.εIso P
  refine (h.map P).of_iso' (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_
  · change (𝟙 _) ≫ P.map j.hom.hom = P.map j.hom.hom ≫ 𝟙 _
    simp
  · apply (cancel_mono e.inv).mp
    exact toUnit_unique _ _
  · change (𝟙 _) ≫ P.map q.hom.hom = P.map q.hom.hom ≫ 𝟙 _
    simp
  · change e.hom ≫ P.map η[G.X] = η[(F.obj G).X] ≫ 𝟙 _
    rw [Category.comp_id]
    rfl

def matrixInclusionBaseChange {G : OverBase R} {m : ℕ} (j : G ⟶ matrixScheme R m) :
    (Over.pullback (scalarSpec R S)).obj G ⟶ matrixScheme S m :=
  (Over.pullback (scalarSpec R S)).map j ≫ (matrixBaseChangeIso (R := R) (S := S) m).hom

@[reassoc]
theorem matrixInclusionBaseChange_project {G : OverBase R} {m : ℕ} (j : G ⟶ matrixScheme R m) :
    (matrixInclusionBaseChange (S := S) j).left ≫
      Spec.map (CommRingCat.ofHom (matrixCoordinateMap R S m)) =
      pullback.fst G.hom (scalarSpec R S) ≫ j.left := by
  change (((Over.pullback (scalarSpec R S)).map j).left ≫
    (matrixBaseChangeIso (R := R) (S := S) m).hom.left) ≫ _ = _
  rw [Category.assoc, matrixBaseChangeIso_hom_project, overPullbackMap_fst]

theorem matrixInclusionBaseChange_closed {G : OverBase R} {m : ℕ} (j : G ⟶ matrixScheme R m)
    (h : IsClosedImmersion j.left) : IsClosedImmersion (matrixInclusionBaseChange (S := S) j).left := by
  change IsClosedImmersion (((Over.pullback (scalarSpec R S)).map j).left ≫
    (matrixBaseChangeIso (R := R) (S := S) m).hom.left)
  exact MorphismProperty.RespectsIso.postcomp @IsClosedImmersion
    ((Over.forget _).map (matrixBaseChangeIso (R := R) (S := S) m).hom) _
    (property_overPullbackMap (scalarSpec R S) j @IsClosedImmersion h)

theorem matrixEmbeddingScalarExtension : MatrixEmbeddingScalarExtension.{u} := by
  intro k E _ _ _ G m i
  exact ⟨⟨matrixInclusionBaseChange (S := E) i.inclusion,
    matrixInclusionBaseChange_closed i.inclusion i.closed⟩,
    matrixInclusionBaseChange_project i.inclusion⟩

end ModelsBaseChange

end

section OverTower

variable {X Y Z : Scheme.{u}} (g : Y ⟶ Z) (f : X ⟶ Y) {h : X ⟶ Z} (w : f ≫ g = h)

def overPullbackComparison (V : Over Z) :
    ((Over.pullback g ⋙ Over.pullback f).obj V).left ≅ ((Over.pullback h).obj V).left :=
  pullbackLeftPullbackSndIso V.hom g f ≪≫ pullback.congrHom rfl w

set_option backward.isDefEq.respectTransparency false in
theorem overPullbackComparison_fst (V : Over Z) :
    (overPullbackComparison g f w V).hom ≫ pullback.fst V.hom h =
      pullback.fst ((Over.pullback g).obj V).hom f ≫ pullback.fst V.hom g := by
  subst h
  simp [overPullbackComparison, pullback.congrHom, Over.pullback_obj_hom]

set_option backward.isDefEq.respectTransparency false in
theorem overPullbackComparison_snd (V : Over Z) :
    (overPullbackComparison g f w V).hom ≫ ((Over.pullback h).obj V).hom =
      ((Over.pullback g ⋙ Over.pullback f).obj V).hom := by
  subst h
  simp [overPullbackComparison, pullback.congrHom, Over.pullback_obj_hom]

set_option backward.isDefEq.respectTransparency false in
def overPullbackCompositeIso :
    Over.pullback g ⋙ Over.pullback f ≅ Over.pullback h :=
  NatIso.ofComponents
    (fun V => Over.isoMk (overPullbackComparison g f w V) (overPullbackComparison_snd g f w V))
    (by
      intro U V a
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · change (((Over.pullback g ⋙ Over.pullback f).map a).left ≫
            (overPullbackComparison g f w V).hom) ≫ pullback.fst V.hom h =
          ((overPullbackComparison g f w U).hom ≫
            ((Over.pullback h).map a).left) ≫ pullback.fst V.hom h
        rw [Category.assoc, overPullbackComparison_fst, ← Category.assoc,
          Functor.comp_map, overPullbackMap_fst, Category.assoc, overPullbackMap_fst,
          Category.assoc, overPullbackMap_fst, ← Category.assoc (overPullbackComparison g f w U).hom,
          overPullbackComparison_fst, Category.assoc]
      · exact (Over.w _).trans (Over.w _).symm)

end OverTower

theorem compositeMapGrpIso_hom_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (e : F ⋙ G ≅ H) (X : Grp C) :
    ((Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso e).hom.app X).hom.hom =
      e.hom.app X.X := by
  let P := Grp.forget E
  change P.map ((Functor.mapGrpCompIso (F := F) (G := G)).inv.app X ≫
    (Functor.mapGrpNatIso e).hom.app X) = _
  rw [P.map_comp]
  change ((Functor.mapGrpCompIso (F := F) (G := G)).inv.app X).hom.hom ≫
    ((Functor.mapGrpNatIso e).hom.app X).hom.hom = _
  rw [Functor.mapGrpCompIso_inv_app_hom_hom, Functor.mapGrpNatIso_hom_app_hom_hom]
  exact Category.id_comp _

section GroupTower

variable {R S U : Type u} [CommRing R] [CommRing S] [CommRing U] [Algebra R S] [Algebra R U]
  [Algebra S U] [IsScalarTower R S U]

def scalarExtensionTowerIso :
    scalarExtension R S ⋙ scalarExtension S U ≅ scalarExtension R U :=
  Functor.mapGrpCompIso.symm ≪≫ Functor.mapGrpNatIso
    (overPullbackCompositeIso (scalarSpec R S) (scalarSpec S U) scalarSpec_tower)

theorem scalarExtensionTowerIso_hom_fst (G : Grp (OverBase R)) :
    ((scalarExtensionTowerIso (R := R) (S := S) (U := U)).hom.app G).hom.hom.left ≫
      pullback.fst G.X.hom (scalarSpec R U) =
      pullback.fst ((scalarExtension R S).obj G).X.hom (scalarSpec S U) ≫
        pullback.fst G.X.hom (scalarSpec R S) := by
  let e := overPullbackCompositeIso (scalarSpec R S) (scalarSpec S U)
    (scalarSpec_tower (R := R) (S := S) (U := U))
  have eq : ((scalarExtensionTowerIso (R := R) (S := S) (U := U)).hom.app G).hom.hom =
      e.hom.app G.X := compositeMapGrpIso_hom_hom _ _ _ e G
  exact (congrArg (fun a => a.left ≫ pullback.fst G.X.hom (scalarSpec R U)) eq).trans
    (overPullbackComparison_fst (scalarSpec R S) (scalarSpec S U) scalarSpec_tower G.X)

end GroupTower

set_option backward.isDefEq.respectTransparency false in
theorem kernelCentralBaseChange {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {H Z : Grp (OverBase R)} (j : Z ⟶ H)
    (h : Commute (fst H.X Z.X) (snd H.X Z.X ≫ j.hom.hom)) :
    let F := scalarExtension R S
    Commute (fst (F.obj H).X (F.obj Z).X) (snd (F.obj H).X (F.obj Z).X ≫ (F.map j).hom.hom) := by
  let P := Over.pullback (scalarSpec R S)
  letI : MonObj (P.obj H.X) := Functor.monObjObj (F := P) H.X
  have mapMul {U : OverBase R} (a b : U ⟶ H.X) :
      P.map (a * b) = (P.map a : P.obj U ⟶ P.obj H.X) * P.map b := by
    change P.map (lift a b ≫ μ[H.X]) =
      lift (P.map a) (P.map b) ≫ Functor.LaxMonoidal.μ P H.X H.X ≫ P.map μ[H.X]
    rw [P.map_comp, ← Category.assoc, Functor.Monoidal.lift_μ]
  have e := congrArg (fun f => Functor.LaxMonoidal.μ P H.X Z.X ≫ P.map f) h.eq
  simp only [mapMul, MonObj.comp_mul, Functor.map_comp, Functor.Monoidal.μ_fst,
    Functor.Monoidal.μ_snd_assoc] at e
  exact e

section

set_option backward.isDefEq.respectTransparency false

section ModelsBaseChange

variable {R S E : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable [Field E] [Algebra R E] [Algebra S E] [IsScalarTower R S E]

section IntegralModelBaseChange

variable {G H : AffineAlgebraicGroup E} {q : H.val ⟶ G.val} {N : ClosedSubgroup H.val}
    {T : SplitCoverData G H q N} {m : ℕ} {i : MatrixEmbedding G m}

theorem integralMatrix_baseChange (M : IntegralModel (R := R) T i) :
    let F := scalarExtension R S
    let t := (scalarExtensionTowerIso (R := R) (S := S) (U := E)).app M.target.val
    (t ≪≫ M.genericTarget).hom.hom.hom.left ≫ i.inclusion.left ≫
        Spec.map (CommRingCat.ofHom (matrixCoordinateMap S E m)) =
      pullback.fst (F.obj M.target.val).X.hom (scalarSpec S E) ≫
        (matrixInclusionBaseChange (S := S) M.matrixInclusion).left := by
  let F := scalarExtension R S
  let t := (scalarExtensionTowerIso (R := R) (S := S) (U := E)).app M.target.val
  let j := matrixInclusionBaseChange (S := S) M.matrixInclusion
  let g := (t ≪≫ M.genericTarget).hom.hom.hom
  change g.left ≫ i.inclusion.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap S E m)) =
    pullback.fst (F.obj M.target.val).X.hom (scalarSpec S E) ≫ j.left
  apply (matrixBaseChange_isPullback (R := R) (S := S) m).hom_ext
  · simp only [Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, matrixCoordinateMap_comp,
      matrixInclusionBaseChange_project]
    change (t.hom.hom.hom.left ≫ M.genericTarget.hom.hom.hom.left) ≫
      i.inclusion.left ≫ Spec.map (CommRingCat.ofHom (matrixCoordinateMap R E m)) = _
    rw [Category.assoc, M.genericMatrix, ← Category.assoc]
    have h := scalarExtensionTowerIso_hom_fst (R := R) (S := S) (U := E) M.target.val
    exact (congrArg (· ≫ M.matrixInclusion.left) h).trans (Category.assoc _ _ _)
  · simp only [Category.assoc]
    rw [(matrixBaseChange_isPullback (R := S) (S := E) m).w]
    have h : j.left ≫ (matrixScheme S m).hom = (F.obj M.target.val).X.hom := j.w
    rw [h, Over.w_assoc, Over.w_assoc]
    exact pullback.condition.symm

set_option maxHeartbeats 650000 in
def integralModelBaseChange [IsDomain S] [IsFractionRing S E] (M : IntegralModel (R := R) T i) :
    IntegralModel (R := S) T i := by
  let F := scalarExtension R S
  let P := Over.pullback (scalarSpec R S)
  let t := scalarExtensionTowerIso (R := R) (S := S) (U := E)
  let hT := groupAlgebraFibre R S (ULift.{u} (Multiplicative (T.indices → ℤ)))
  let hN := groupAlgebraFibre R S (ULift.{u} (∀ a, Multiplicative (ZMod (T.exponents a))))
  let qS := F.map M.map
  let jS := F.map M.kernelInclusion
  let mS := matrixInclusionBaseChange (S := S) M.matrixInclusion
  have prop {G H : Grp (OverBase R)} {f : G ⟶ H}
      (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange] (h : Q f.hom.hom.left) :
      Q (F.map f).hom.hom.left := property_overPullbackMap (scalarSpec R S) _ Q h
  have hflat : Flat (F.obj M.target.val).X.hom :=
    MorphismProperty.pullback_snd (P := @Flat) _ _ M.targetFlat
  have agrees {A B : Grp (OverBase R)} {C D : GroupScheme E}
      {f : A ⟶ B} {g : C ⟶ D}
      {eA : (scalarExtension R E).obj A ≅ C} {eB : (scalarExtension R E).obj B ≅ D}
      (h : (scalarExtension R E).map f ≫ eB.hom = eA.hom ≫ g) :
      (scalarExtension S E).map (F.map f) ≫ (t.app B ≪≫ eB).hom =
        (t.app A ≪≫ eA).hom ≫ g := by
    change (F ⋙ scalarExtension S E).map f ≫ t.hom.app B ≫ eB.hom =
      (t.hom.app A ≫ eA.hom) ≫ g
    rw [t.hom.naturality_assoc, h, Category.assoc]
  refine {
    target := affineModelBaseChange M.target
    targetFlat := hflat
    source := affineModelBaseChange M.source
    kernel := affineModelBaseChange M.kernel
    kernelFinite := MorphismProperty.pullback_snd (P := @IsFinite) _ _ M.kernelFinite
    kernelFlat := MorphismProperty.pullback_snd (P := @Flat) _ _ M.kernelFlat
    sourceTorus := affineModelBaseChange M.sourceTorus
    targetTorus := affineModelBaseChange M.targetTorus
    map := qS
    kernelInclusion := jS
    sourceTorusInclusion := F.map M.sourceTorusInclusion
    targetTorusInclusion := F.map M.targetTorusInclusion
    torusMap := F.map M.torusMap
    torsor := finiteKernelTorsorOfKernel qS jS (prop _ M.torsor.finite) (prop _ M.torsor.flat)
      (prop _ M.torsor.surjective) (prop _ M.torsor.finitePresentation) (prop _ M.torsor.closed)
      (kernelSquareBaseChange (S := S) M.map M.kernelInclusion M.torsor.kernel)
    kernelCentral := kernelCentralBaseChange (S := S) M.kernelInclusion M.kernelCentral
    sourceTorusClosed := prop _ M.sourceTorusClosed
    targetTorusClosed := prop _ M.targetTorusClosed
    torusCompatibility := by rw [← F.map_comp, ← F.map_comp, M.torusCompatibility]
    splitSourceTorus := F.mapIso M.splitSourceTorus ≪≫ genericFibreIso hT
    splitTargetTorus := F.mapIso M.splitTargetTorus ≪≫ genericFibreIso hT
    splitTorusMap := ?_
    splitKernel := F.mapIso M.splitKernel ≪≫ genericFibreIso hN
    genericTarget := t.app M.target.val ≪≫ M.genericTarget
    genericSource := t.app M.source.val ≪≫ M.genericSource
    genericKernel := t.app M.kernel.val ≪≫ M.genericKernel
    genericSourceTorus := t.app M.sourceTorus.val ≪≫ M.genericSourceTorus
    genericTargetTorus := t.app M.targetTorus.val ≪≫ M.genericTargetTorus
    genericMap := agrees M.genericMap
    genericKernelInclusion := agrees M.genericKernelInclusion
    genericSourceTorusInclusion := agrees M.genericSourceTorusInclusion
    genericTargetTorusInclusion := agrees M.genericTargetTorusInclusion
    genericTorusMap := agrees M.genericTorusMap
    matrixInclusion := mS
    matrixClosed := matrixInclusionBaseChange_closed _ M.matrixClosed
    genericMatrix := integralMatrix_baseChange (S := S) M
    matrixClosure := genericFibreImage (E := E) _ hflat mS.left }
  change F.map M.torusMap ≫ F.map M.splitTargetTorus.hom ≫ (genericFibreIso hT).hom =
    (F.map M.splitSourceTorus.hom ≫ (genericFibreIso hT).hom) ≫ integralPowerMap S T.exponents
  rw [← F.map_comp_assoc, M.splitTorusMap, F.map_comp, Category.assoc]
  have e := genericFibreIso_naturality hT hT
    (MonoidAlgebra.mapDomainBialgHom R (powerOnLiftedCharacters T.exponents))
    (MonoidAlgebra.mapDomainBialgHom S (powerOnLiftedCharacters T.exponents))
    (groupAlgebraInclusion_characterMap _ _ _ _)
  rw [e, Category.assoc]

end IntegralModelBaseChange
end ModelsBaseChange

set_option maxHeartbeats 700000 in
theorem integralModels : IntegralModels.{u, v} := by
  intro E _ F B hB G H q N hq hN T m i
  obtain ⟨A, _, _, _, _, S, hSf, hBS, hA⟩ := dedekindIntegralBase F B hB
  obtain ⟨C⟩ := coverCoordinates hq hN T i
  letI := C.targetFiniteType
  letI := C.sourceFiniteType
  letI := matrixCoordinates_finitePresentation A m
  letI := T.finiteIndices
  let ambient := genericAmbient (A := A) C
  have hambient : Function.Surjective ambient :=
    C.matrixSurj.comp (matrixCoordinatesScalarEquiv (R := A) (S := E) m).surjective
  obtain ⟨d, hd, rE, hARE, ⟨D⟩⟩ := CentralCoverSpreading.centralCoverSpreading
    A E C.target C.source (matrixCoordinates A m) T.indices T.exponents T.positiveExponents
      C.diagram ambient hambient C.coverFinite C.coverFaithfullyFlat
  let R := Localization.Away d
  letI : IsDomain R := Localization.Away.isDomain hd
  letI : Algebra R E := rE
  letI : IsScalarTower A R E := hARE
  letI : IsFractionRing R E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) R E
  letI : Algebra R C.target := ((algebraMap E C.target).comp (algebraMap R E)).toAlgebra
  letI : Algebra R C.source := ((algebraMap E C.source).comp (algebraMap R E)).toAlgebra
  letI : IsScalarTower R E C.target := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R E C.source := IsScalarTower.of_algebraMap_eq' rfl
  let M := integralModelOfDiagram C D
  obtain ⟨S', hS'f, hSS', f, hf⟩ := integralLocalization F S hSf hA d hd
  let R' := integersOutside F S'
  letI : Algebra R R' := f.toAlgebra
  letI : IsScalarTower R R' E := IsScalarTower.of_algebraMap_eq' hf.symm
  have hA' (a : A) : algebraMap A E a ∈ R' := by
    apply Subring.mem_iInf.mpr
    intro w
    exact (Subring.mem_iInf.mp (hA a)) ⟨w.val, fun hw => w.property (hSS' hw)⟩
  letI : IsFractionRing R' E := fraction_ring_of_containing_integers R' hA'
  exact ⟨S', hS'f, hBS.trans hSS', ⟨integralModelBaseChange (S := R') M⟩⟩

end

set_option backward.isDefEq.respectTransparency false in
/-- The central cover and its integral models for the chosen matrix
realization of the target over the global field. -/
theorem globalCoverWithModels : GlobalCoverWithModels.{u, v} := by
  intro K _ D G hG m i
  obtain ⟨H, q, N, hH, hsc, hq, hN, hmt, had, htriv,
    E, hE, hKE, hfin, hgal, hc, hGE, hHE, hqE, hNE, ⟨T⟩⟩ := coverExists G hG
  let G' := baseChangedAlgebraicGroup E G
  let H' := baseChangedAlgebraicGroup E H
  let q' := (groupBaseChange K E).map q
  let N' : ClosedSubgroup H'.val := ⟨_, (groupBaseChange K E).map N.inclusion, hc⟩
  have localKernel : IsTrivialSubgroup N' ↔ IsTrivialSubgroup N := by
    rw [kernel_trivial_iff_isIso (G := G') (H := H') (q := q') hqE hNE,
      kernel_trivial_iff_isIso hq hN]
    exact ⟨isIso_of_scalarExtension E q, fun h => by
      let := h
      exact Functor.map_isIso (groupBaseChange K E) q⟩
  have factors : (∃ a, 1 < T.exponents a) ↔
      ¬ Specs.SimplyConnectedLattice.GeometricallySimplyConnected G :=
    T.nontrivialFactors.symm.trans ((not_congr localKernel).trans (not_congr htriv))
  obtain ⟨D'⟩ := globalFieldExtension (E := E) D
  obtain ⟨j, hj⟩ := matrixEmbeddingScalarExtension (E := E) i
  exact ⟨H, q, N, hH, hsc, hq, hN, hmt, had, htriv, E, hE, hKE, hfin, hgal,
    hc, T, D', j, hGE, hHE, hqE, hNE, factors, hj,
    fun B hB => integralModels D' B hB G' H' q' N' hqE hNE T j⟩

end

end LinearAlgebraicGroups.Arithmetic.CentralCover
