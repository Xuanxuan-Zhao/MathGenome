import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.GenericCocharacterMinimalParabolic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerSplitSubtorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
import Batteries.Tactic.OpenPrivate
import Mathlib.RingTheory.Flat.Equalizer

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent

open LinearAlgebraicGroups.Specs
open ExceptionalTwistedTraceComparison (PointCocycle Twist)
open AutomorphismSequence (AdjointQuotient)
open RelativeFormComparison (IsInduced)

/-- Recover the scheme trivialization inducing the actual relative point-functor
trivialization of the inner twist. -/
theorem schemeTrivialization {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a) :
    ∃ j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj T.group.val,
      IsInduced F K j T.trivialization := by
  obtain ⟨e, he⟩ := Descent.RelativeFormComparison.schemeIsomorphismComparison (S := K)
    G.val T.group.val
  exact ⟨e.symm T.trivialization, (he _ _).mpr (e.apply_symm_apply _)⟩

open IntegralSemisimpleModel (fibre integerAlgebra Integers IntegralGroup Model splitTorus)
open ExceptionalMarkedRootDescent (MarkedFibre)
open Pinning (BasedRootDatum)
open Specs.ExceptionalInnerStandardTorusDescent (IsMarkedTrivialization)

attribute [local instance] integerAlgebra

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackComp_fst {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Over Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫
        pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
      pullback.fst A.hom (f ≫ g) := by
  have h := conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
    ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g)) (Over.mapComp f g).inv A
  have h' := congrArg CommaMorphism.left h
  simp only [Adjunction.comp_counit_app, Over.mapPullbackAdj_counit_app, Functor.comp_map,
    Functor.comp_obj, Over.map_map_left, Over.comp_left,
    Over.mapComp_inv_app_left] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
private theorem fibreTowerComparison {F K : Type u} [Field F] [Field K] [Algebra F K]
    : ∃ e : fibre K ≅ fibre F ⋙ groupBaseChange F K, ∀ A : IntegralGroup.{u},
      (e.app A).hom.hom.hom.left ≫ pullback.fst ((fibre F).obj A).X.hom (fieldSpecMap F K) ≫
        pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F))) =
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} K))) := by
  let f := fieldSpecMap F K
  let g := Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F))
  have hfg : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    exact map_intCast (algebraMap F K) z.down
  suffices h : ∀ (r : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of Integers.{u})), f ≫ g = r →
      ∃ e : (Over.pullback r).mapGrp ≅ fibre F ⋙ groupBaseChange F K, ∀ A : IntegralGroup.{u},
        (e.app A).hom.hom.hom.left ≫ pullback.fst ((fibre F).obj A).X.hom f ≫ pullback.fst A.X.hom g =
          pullback.fst A.X.hom r by exact h _ hfg
  intro r hr
  subst r
  let e := Functor.mapGrpNatIso (Over.pullbackComp f g) ≪≫ Functor.mapGrpCompIso
  refine ⟨e, fun A => ?_⟩
  change (((Over.pullbackComp f g).hom.app A.X).left ≫ 𝟙 _) ≫
      pullback.fst (pullback.snd A.X.hom g) f ≫ pullback.fst A.X.hom g = _
  rw [Category.comp_id]
  exact pullbackComp_fst f g A.X

private noncomputable def markedReferenceIso {F K : Type u} [Field F] [Field K] [Algebra F K]
    (d : fibre K ≅ fibre F ⋙ groupBaseChange F K)
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    {G : AffineAlgebraicGroup F} (iG : G.val ≅ (fibre F).obj M.group) :
    C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj G.val :=
  C.groupIso.symm ≪≫ d.app M.group ≪≫ (groupBaseChange F K).mapIso iG.symm

private noncomputable def markedReferenceTorusIso {F K : Type u} [Field F] [Field K] [Algebra F K]
    (d : fibre K ≅ fibre F ⋙ groupBaseChange F K)
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K) :
    C.realization.pinned.pair.T.group ≅ (groupBaseChange F K).obj ((fibre F).obj (splitTorus D)) :=
  C.torusIso.symm ≪≫ d.app (splitTorus D)

set_option backward.isDefEq.respectTransparency false in
private theorem markedTrivializationOfTower {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    {G H : AffineAlgebraicGroup F} (iG : G.val ≅ (fibre F).obj M.group)
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (d : fibre K ≅ fibre F ⋙ groupBaseChange F K)
    (hd : (d.app M.group).hom.hom.hom.left ≫
        pullback.fst ((fibre F).obj M.group).X.hom (fieldSpecMap F K) ≫
        pullback.fst M.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} F))) =
      pullback.fst M.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} K)))) :
    let f := markedReferenceIso d C iG ≪≫ j
    let fT := markedReferenceTorusIso d C
    IsMarkedTrivialization C iG j f ∧
      C.realization.pinned.pair.T.inclusion ≫ f.hom =
        fT.hom ≫ (groupBaseChange F K).map ((fibre F).map M.torus ≫ iG.inv) ≫ j.hom := by
  let e := d.app M.group
  have he := hd
  let v := (groupBaseChange F K).mapIso iG.symm
  let f := markedReferenceIso d C iG ≪≫ j
  let fT := markedReferenceTorusIso d C
  change IsMarkedTrivialization C iG j f ∧ _
  refine ⟨?_, ?_⟩
  swap
  · have ht : C.realization.pinned.pair.T.inclusion ≫ C.groupIso.inv =
        C.torusIso.inv ≫ (fibre K).map M.torus := by
      rw [← cancel_mono C.groupIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.assoc, C.torus_comm, Iso.inv_hom_id_assoc]
    have hn : (fibre K).map M.torus ≫ e.hom = (d.app (splitTorus D)).hom ≫
        (groupBaseChange F K).map ((fibre F).map M.torus) := d.hom.naturality _
    change C.realization.pinned.pair.T.inclusion ≫ C.groupIso.inv ≫ e.hom ≫ v.hom ≫ j.hom =
      (C.torusIso.inv ≫ (d.app (splitTorus D)).hom) ≫
        (groupBaseChange F K).map ((fibre F).map M.torus ≫ iG.inv) ≫ j.hom
    rw [Functor.map_comp]
    change _ = (C.torusIso.inv ≫ (d.app (splitTorus D)).hom) ≫
      (groupBaseChange F K).map ((fibre F).map M.torus) ≫ v.hom ≫ j.hom
    calc
      _ = (C.realization.pinned.pair.T.inclusion ≫ C.groupIso.inv) ≫
          e.hom ≫ v.hom ≫ j.hom := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [ht, Category.assoc C.torusIso.inv, ← Category.assoc ((fibre K).map M.torus), hn]
        simp only [Category.assoc]
  have hproj : v.hom.hom.hom.left ≫ pullback.fst G.val.X.hom (fieldSpecMap F K) =
      pullback.fst ((fibre F).obj M.group).X.hom (fieldSpecMap F K) ≫ iG.inv.hom.hom.left :=
    pullback.lift_fst _ _ _
  have hi : iG.inv.hom.hom.left ≫ iG.hom.hom.hom.left = 𝟙 _ :=
    congrArg (fun m => m.hom.hom.left) iG.inv_hom_id
  have hcancel : f.hom ≫ j.inv = C.groupIso.inv ≫ e.hom ≫ v.hom := by
    simp [f, markedReferenceIso, e, v]
  unfold IsMarkedTrivialization
  rw [hcancel]
  change (C.groupIso.inv.hom.hom.left ≫ e.hom.hom.hom.left ≫ v.hom.hom.hom.left) ≫
      pullback.fst G.val.X.hom (fieldSpecMap F K) ≫ iG.hom.hom.hom.left ≫
        pullback.fst M.group.X.hom _ = _
  let pG : ((groupBaseChange F K).obj G.val).X.left ⟶ G.val.X.left :=
    pullback.fst G.val.X.hom (fieldSpecMap F K)
  let pF : ((fibre F).obj M.group).X.left ⟶ M.group.X.left :=
    pullback.fst M.group.X.hom _
  let pFK : ((groupBaseChange F K).obj ((fibre F).obj M.group)).X.left ⟶
      ((fibre F).obj M.group).X.left :=
    pullback.fst ((fibre F).obj M.group).X.hom (fieldSpecMap F K)
  let pK : ((fibre K).obj M.group).X.left ⟶ M.group.X.left :=
    pullback.fst M.group.X.hom _
  change v.hom.hom.hom.left ≫ pG = pFK ≫ iG.inv.hom.hom.left at hproj
  change e.hom.hom.hom.left ≫ pFK ≫ pF = pK at he
  change (C.groupIso.inv.hom.hom.left ≫ e.hom.hom.hom.left ≫ v.hom.hom.hom.left) ≫
      pG ≫ iG.hom.hom.hom.left ≫ pF = C.groupIso.inv.hom.hom.left ≫ pK
  calc
    _ = C.groupIso.inv.hom.hom.left ≫ e.hom.hom.hom.left ≫
        (v.hom.hom.hom.left ≫ pG) ≫ iG.hom.hom.hom.left ≫ pF := by
      simp only [Category.assoc]
    _ = C.groupIso.inv.hom.hom.left ≫ e.hom.hom.hom.left ≫
        pFK ≫ (iG.inv.hom.hom.left ≫ iG.hom.hom.hom.left) ≫ pF := by
      rw [hproj]
      simp only [Category.assoc]
    _ = _ := by rw [hi, Category.id_comp, he]

/-- The comparison with the marked split fibre respects the projection
to the original integral model and the marked torus inclusion. -/
theorem markedTrivialization {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    {G H : AffineAlgebraicGroup F} (iG : G.val ≅ (fibre F).obj M.group)
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val) :
    ∃ (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val)
      (fT : C.realization.pinned.pair.T.group ≅ (groupBaseChange F K).obj ((fibre F).obj (splitTorus D))),
      IsMarkedTrivialization C iG j f ∧
      C.realization.pinned.pair.T.inclusion ≫ f.hom =
        fT.hom ≫ (groupBaseChange F K).map ((fibre F).map M.torus ≫ iG.inv) ≫ j.hom := by
  obtain ⟨d, hd⟩ := fibreTowerComparison (F := F) (K := K)
  exact ⟨_, _, markedTrivializationOfTower C iG j d (hd M.group)⟩

open ExceptionalAffineBruhat (SplitLevel)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)

open private conjugates_of_normalizes from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

/-- A marked normalizer section induces the scheme automorphism of the standard
torus given by conjugation. -/
theorem markedNormalizerConjugation {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)} (Y : SplitLevel K c p p' e)
    (g : 𝟙_ (SchemeOver K) ⟶ Y.sc_fibre.realization.pinned.pair.G.val.X)
    (hg : markedGroundPoint Y.sc_fibre g ∈ Y.sc.N) :
    let P := Y.sc_fibre.realization.pinned.pair
    ∃ a : P.T.group ≅ P.T.group,
      (a.hom ≫ P.T.inclusion).hom.hom =
        (toUnit P.T.group.X ≫ g) * P.T.inclusion.hom.hom *
          (toUnit P.T.group.X ≫ g)⁻¹ :=
  conjugates_of_normalizes _ ((Y.sc_points.1 g).mp hg)

open ExceptionalValuedTorusNormalizer (FibreNormalizer)

/-- The linear part of the adjoint affine action comes from the Weyl label
of a normalizer section in the marked integral model. -/
theorem adjointAffineLinearPart {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)} (Y : SplitLevel K c p p' e)
    (n : Y.ad.N) :
    ∃ C : FibreNormalizer M' K, letI := C.torusComm
      ∃ m : 𝟙_ (SchemeOver K) ⟶ C.identification.normalizer.group.X,
      C.point m = (n : ExceptionalAffineBruhat.FieldPoints M' K) ∧
      (Y.ad.affine n).linear = (C.label m).val.coweightEquiv.symm.baseChange ℤ ℚ E.Y E.Y := by
  obtain ⟨C, hC, _⟩ := Y.ad_points.2.1.2
  let _ := C.torusComm
  obtain ⟨m, hm, hlabel⟩ := hC n
  refine ⟨C, m, hm, ?_⟩
  change C.label m = Y.ad.localIwahori.normalizer.label n at hlabel
  rw [hlabel]
  have h (x : ℚ ⊗[ℤ] E.Y) := Y.ad_points.2.2.2.2.2.2.1 n x
  apply LinearEquiv.ext
  intro x
  have hl := (Y.ad.affine n).map_vadd (0 : ℚ ⊗[ℤ] E.Y) x
  rw [vadd_eq_add, add_zero, vadd_eq_add, h x, h 0, LinearEquiv.map_zero, zero_add] at hl
  exact (add_left_inj _).mp hl.symm

/-- The rational cocharacters obtained from the integral fixed lattice
are exactly the fixed subspace after extension to ℚ. -/
theorem rationalFixedLattice {Y : Type u} [AddCommGroup Y]
    (w : Y ≃ₗ[ℤ] Y) :
    let L := w.baseChange ℤ ℚ Y Y
    let I := LinearMap.ker (w.toLinearMap - LinearMap.id)
    Function.Injective (I.subtype.baseChange ℚ) ∧
      LinearMap.range (I.subtype.baseChange ℚ) = LinearMap.ker (L.toLinearMap - LinearMap.id) := by
  dsimp only
  constructor
  · exact Module.Flat.lTensor_preserves_injective_linearMap
      _ Subtype.val_injective
  · rw [← LinearMap.baseChange_id (A := ℚ), LinearEquiv.coe_baseChange,
      ← LinearMap.baseChange_sub]
    exact (Module.Flat.ker_lTensor_eq ℚ ℚ (w.toLinearMap - LinearMap.id)).symm

open CharacterDescent (Character Cocharacter)
open Specs.GeometricRadicals (IsSplitTorus)
open ExceptionalAffineRootSystems (ApartmentRoots)
open Specs.ExceptionalInnerStandardTorusDescent (markedCharacter markedCocharacterMap)

private theorem character_trivial_iff_pairing {K : Type u} [Field K] {H : GroupScheme K}
    (hH : IsSplitTorus H) (χ : Character H) :
    χ.hom.hom = 1 ↔ ∀ y : Cocharacter H, CharacterPairing.pairing H χ y = 0 := by
  obtain ⟨comm, _, _, _, _, P, perf, hP⟩ :=
    _root_.LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing H hH
  have h1 : χ.hom.hom = 1 ↔ χ = 1 := by
    constructor
    · intro h
      apply Grp.hom_ext
      exact h
    · rintro rfl
      rfl
  rw [h1]
  constructor
  · rintro rfl y
    rw [← hP]
    exact (P.map_zero ▸ rfl : P (0 : Additive (Character H)) (Additive.ofMul y) = 0)
  · intro h
    have hzero : P (Additive.ofMul χ) = 0 := LinearMap.ext fun y => (hP χ y.toMul).trans (h y.toMul)
    let _ := perf
    exact (LinearMap.IsPerfPair.bijective_left P).1 (hzero.trans P.map_zero.symm)

private theorem markedPairing {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M K) {H : GroupScheme K} [IsCommMonObj H.X]
    (s : H ⟶ C.realization.pinned.pair.T.group) (i : D.I) (y : Cocharacter H) :
    D.datum.root' i (markedCocharacterMap C s (Additive.ofMul y)) =
      CharacterPairing.pairing H (s ≫ markedCharacter C i) y := by
  let δ := C.realization.datumIso.val
  let _ := C.realization.attached.comm
  let P := C.realization.attached.datum
  change D.datum.toLinearMap (D.datum.root i) (δ.coweightEquiv (Additive.ofMul (y ≫ s))) = _
  exact (δ.toLinearMap_weightEquiv (D.datum.root i) (Additive.ofMul (y ≫ s))).symm.trans
    ((P.pairing_eq _ _).trans (by
      unfold CharacterPairing.pairing Specs.CharacterDescent.compositionPairing
      exact congrArg (Function.invFun (CharacterPairing.powerMorphism (k := K)))
        (Category.assoc y s (markedCharacter C i))))

/-- Root restriction on a split subtorus is detected by annihilation
of the image of its rational cocharacters in the marked apartment. -/
theorem markedRootRestriction {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M K) {H : GroupScheme K} [IsCommMonObj H.X] (hH : IsSplitTorus H)
    (s : H ⟶ C.realization.pinned.pair.T.group) (i : D.I) :
    let A := ApartmentRoots.split D.datum ℚ
    let W := LinearMap.range ((markedCocharacterMap C s).baseChange ℚ)
    (s ≫ markedCharacter C i).hom.hom = 1 ↔ ∀ x ∈ W, A.root i x = 0 := by
  dsimp only
  rw [character_trivial_iff_pairing hH]
  let V := markedCocharacterMap C s
  let q := (ApartmentRoots.split D.datum ℚ).root i
  change (∀ y : Cocharacter H, CharacterPairing.pairing H (s ≫ markedCharacter C i) y = 0) ↔
    ∀ x ∈ LinearMap.range (V.baseChange ℚ), q x = 0
  have ht (y : Additive (Cocharacter H)) :
      q (V.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] y)) =
        (CharacterPairing.pairing H (s ≫ markedCharacter C i) y.toMul : ℚ) := by
    rw [LinearMap.baseChange_tmul]
    exact (RootData.extendFunctional_one_tmul ℚ _ (V y)).trans
      (congrArg (fun n : ℤ => (n : ℚ)) (markedPairing C s i y.toMul))
  constructor
  · intro h x hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    have he : q.comp (V.baseChange ℚ) = 0 := by
      ext y
      change q (V.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] y)) = 0
      rw [ht, h, Int.cast_zero]
    exact DFunLike.congr_fun he z
  · intro h y
    have hy := h _ (LinearMap.mem_range_self (V.baseChange ℚ) ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul y))
    rw [ht] at hy
    exact_mod_cast hy

open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open private gm_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

/-- The scalar extension comparison for the multiplicative group preserves
the unit represented by every test point. -/
theorem unitComparison (F K : Type u) [Field F] [Field K] [Algebra F K] :
    ∃ e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters)),
      IsUnitComparison F K e :=
  gm_baseChange F K

open private twistGroups twistGroupBaseChangeIso descend_stable_subgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags

private theorem fixedByGenerator {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] {σ : Gal(K/F)} (hσ : Subgroup.zpowers σ = ⊤)
    {x : K} (hx : σ x = x) : x ∈ Set.range (algebraMap F K) := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).mpr
  let S : Subgroup Gal(K/F) :=
    { carrier := {τ | τ x = x}
      one_mem' := rfl
      mul_mem' := fun {s t} hs ht => show s (t x) = x from
        (congrArg s ht).trans hs
      inv_mem' := fun {s} hs => s.injective ((s.apply_symm_apply x).trans hs.symm) }
  have hS : Subgroup.zpowers σ ≤ S := Subgroup.zpowers_le.mpr hx
  rw [hσ] at hS
  exact fun τ => hS (Subgroup.mem_top τ)

/-- A split torus subgroup stable under a generator of finite Galois descent
is the base change of a torus subgroup with the same inclusion. -/
theorem descendStableTorus {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] {σ : Gal(K/F)} (hσ : Subgroup.zpowers σ = ⊤)
    (G : AffineAlgebraicGroup F) (T : ClosedSubgroup ((groupBaseChange F K).obj G.val))
    (hT : IsSplitTorus T.group)
    (d : (twistGroups σ).obj T.group ≅ T.group)
    (hd : d.hom ≫ T.inclusion =
      (twistGroups σ).map T.inclusion ≫ ((twistGroupBaseChangeIso σ).app G.val).hom) :
    ∃ (U : ClosedSubgroup G.val) (e : (groupBaseChange F K).obj U.group ≅ T.group),
      Specs.GeometricRadicals.IsTorus U.group ∧
      e.hom ≫ T.inclusion = (groupBaseChange F K).map U.inclusion := by
  obtain ⟨U, e, he⟩ := descend_stable_subgroup σ (fun x hx => fixedByGenerator hσ hx) G T d hd
  obtain ⟨r, ⟨i⟩⟩ := hT
  exact ⟨U, e, ⟨K, inferInstance, inferInstance, inferInstance, r, ⟨e ≪≫ i⟩⟩, he⟩

open Specs.AutomorphismSequence (groupSections innerAut restrictAut)
open Specs.ExceptionalTwistedTraceComparison (InnerMap ActsByConjugation)

/-- The inner action projects to conjugation on the adjoint group on every
scheme family. The lift is taken over a faithfully flat cover of the family. -/
theorem innerAction_projects {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    {Q : AdjointQuotient G} {inn : InnerMap Q} (hinn : ActsByConjugation inn)
    {S : SchemeOver F} (q : S ⟶ Q.quotient.val.X) (U : Over S)
    (x : U.left ⟶ G.val.X) :
    let a := (inn.app (op S) ⟨q⟩).asIso
    ((a.hom.app (op U)).hom x) ≫ Q.projection.hom.hom =
      (U.hom ≫ q) * (x ≫ Q.projection.hom.hom) * (U.hom ≫ q)⁻¹ := by
  intro a
  let f := Q.projection.hom.hom
  let qU := U.hom ≫ q
  let V := pullback f qU
  let z : V ⟶ G.val.X := pullback.fst _ _
  let p : V ⟶ U.left := pullback.snd _ _
  have hz : z ≫ f = p ≫ qU := pullback.condition
  have hp : IsPullback z.left p.left f.left qU.left :=
    (IsPullback.of_hasPullback f qU).map (Over.forget _)
  let _ : Flat p.left := MorphismProperty.of_isPullback (P := @Flat) hp Q.fppf.1
  let _ : Surjective p.left :=
    MorphismProperty.of_isPullback (P := (@Surjective : MorphismProperty Scheme.{u})) hp Q.fppf.2.1
  let _ : Epi p.left := Flat.epi_of_flat_of_surjective _
  let _ : Epi p := Over.epi_of_epi_left _
  let W : Over S := Over.mk (p ≫ U.hom)
  let v : W ⟶ U := Over.homMk p rfl
  let B : Over V := Over.mk (𝟙 V)
  have hres := ConcreteCategory.congr_hom (inn.naturality (p ≫ U.hom).op)
    (ULift.up q : (groupSections Q.quotient.val).obj (op S))
  change inn.app (op V) ⟨(p ≫ U.hom) ≫ q⟩ =
    restrictAut (p ≫ U.hom) (inn.app (op S) ⟨q⟩) at hres
  rw [Category.assoc, ← hz, hinn] at hres
  have hW := congrArg (fun b => (b.asIso.hom.app (op B)).hom (p ≫ x)) hres
  have hW' : (𝟙 V ≫ z) * (p ≫ x) * (𝟙 V ≫ z)⁻¹ =
      (a.hom.app (op W)).hom (p ≫ x) := hW
  have hnat := ConcreteCategory.congr_hom (a.hom.naturality v.op) x
  change (a.hom.app (op W)).hom (p ≫ x) = p ≫ (a.hom.app (op U)).hom x at hnat
  let y : U.left ⟶ G.val.X := (a.hom.app (op U)).hom x
  have hy : p ≫ y = z * (p ≫ x) * z⁻¹ := by
    have hw : z * (p ≫ x) * z⁻¹ = (a.hom.app (op W)).hom (p ≫ x) := by
      simpa only [Category.id_comp] using hW'
    exact hnat.symm.trans hw.symm
  change y ≫ f = qU * (x ≫ f) * qU⁻¹
  apply (cancel_epi p).mp
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc p y, hy,
    MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hz, Category.assoc p x]

open Specs.RelativeFormComparison (fieldTest)
open private relativeSchemeIso relativeSchemeIso_natural relativeSectionEquiv
  relativeSectionGroupEquiv relativeSection_natural
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private geometricSectionsEquiv geometricSectionsEquiv_left conjugationIso conjugation comp_conjugation
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags

set_option backward.isDefEq.respectTransparency false in
/-- The scheme automorphism attached to a relative inner automorphism
commutes with the adjoint projection and conjugation by its point. -/
theorem innerSchemeProjection {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G} {inn : InnerMap Q}
    (hinn : ActsByConjugation inn) (q : fieldTest F K ⟶ Q.quotient.val.X) :
    ∃ α : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj G.val,
      IsInduced F K α (inn.app (op (fieldTest F K)) ⟨q⟩).asIso ∧
      let qK := (geometricSectionsEquiv K Q.quotient.val).symm q
      α.hom ≫ (groupBaseChange F K).map Q.projection =
        (groupBaseChange F K).map Q.projection ≫ (conjugationIso qK).hom := by
  let S := fieldTest F K
  let a := (inn.app (op S) ⟨q⟩).asIso
  let α := relativeSchemeIso a
  let qK := (geometricSectionsEquiv K Q.quotient.val).symm q
  have hqK : qK.left ≫ pullback.fst Q.quotient.val.X.hom (fieldSpecMap F K) = q.left :=
    (geometricSectionsEquiv_left Q.quotient.val qK).symm.trans
      (congrArg Over.Hom.left ((geometricSectionsEquiv K Q.quotient.val).apply_symm_apply q))
  refine ⟨α, ?_, ?_⟩
  · intro U x
    have h := relativeSchemeIso_natural a U ((relativeSectionEquiv U G.val.X).symm x)
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Over.Hom.left h.symm
  · dsimp only
    let X := ((groupBaseChange F K).obj G.val).X
    let U := (Over.iteratedSliceBackward S).obj X
    let xK : (Over.iteratedSliceForward S).obj U ⟶ X :=
      Over.homMk (𝟙 X.left) (Category.id_comp _)
    let x := relativeSectionEquiv U G.val.X xK
    let W := (Over.iteratedSliceForward S).obj U
    let f := (groupBaseChange F K).map Q.projection
    let H := Q.quotient.val
    let φ := relativeSectionGroupEquiv U H
    have hq : φ (toUnit W ≫ qK) = U.hom ≫ q := by
      apply Over.OverMorphism.ext
      change ((toUnit W).left ≫ qK.left) ≫ pullback.fst H.X.hom (fieldSpecMap F K) =
        U.hom.left ≫ q.left
      rw [Category.assoc, hqK]
      rfl
    have hx := innerAction_projects hinn q U x
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    suffices h : xK ≫ α.hom.hom.hom ≫ f.hom.hom =
        xK ≫ f.hom.hom ≫ (conjugationIso qK).hom.hom.hom by
      have hh := congrArg Over.Hom.left h
      change 𝟙 X.left ≫ (α.hom.hom.hom ≫ f.hom.hom).left =
        𝟙 X.left ≫ (f.hom.hom ≫ (conjugationIso qK).hom.hom.hom).left at hh
      exact (Category.id_comp _).symm.trans (hh.trans (Category.id_comp _))
    apply φ.injective
    calc
      _ = ((a.hom.app (op U)).hom x) ≫ Q.projection.hom.hom := by
        change relativeSectionEquiv U H.X (xK ≫ α.hom.hom.hom ≫ f.hom.hom) = _
        calc
          _ = relativeSectionEquiv U H.X ((xK ≫ α.hom.hom.hom) ≫ f.hom.hom) :=
            congrArg (relativeSectionEquiv U H.X) (Category.assoc _ _ _).symm
          _ = relativeSectionEquiv U G.val.X (xK ≫ α.hom.hom.hom) ≫ Q.projection.hom.hom :=
            relativeSection_natural U Q.projection.hom.hom _
          _ = _ := congrArg (· ≫ Q.projection.hom.hom) (relativeSchemeIso_natural a U xK)
      _ = _ := by
        change _ = φ (xK ≫ f.hom.hom ≫ conjugation qK)
        rw [← Category.assoc, comp_conjugation, map_mul, map_mul, map_inv, hq]
        change _ = (U.hom ≫ q) * relativeSectionEquiv U H.X (xK ≫ f.hom.hom) * _
        exact hx.trans (congrArg (fun z => (U.hom ≫ q) * z * (U.hom ≫ q)⁻¹)
          (relativeSection_natural U Q.projection.hom.hom xK).symm)

open Specs.AutomorphismSequence (relativePoints restrictIso)
open Specs.RelativeFormComparison (fieldMap transportedAut)
open private scalarIso twistBaseChangeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private schemeIsoEquiv schemeIsoEquiv_trans induced_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison

set_option backward.isDefEq.respectTransparency false in
private theorem restrictSchemeIsInduced {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G H : GroupScheme F} (σ : Gal(K/F))
    {j : (groupBaseChange F K).obj G ≅ (groupBaseChange F K).obj H}
    {i : relativePoints G (fieldTest F K) ≅ relativePoints H (fieldTest F K)}
    (hj : IsInduced F K j i) :
    IsInduced F K (((twistGroupBaseChangeIso σ.symm).app G).symm ≪≫
      (twistGroups σ.symm).mapIso j ≪≫ (twistGroupBaseChangeIso σ.symm).app H)
      (restrictIso (fieldMap F K σ) i) := by
  intro U x
  let U' : Over (fieldTest F K) := (Over.map (fieldMap F K σ)).obj U
  let p₁ := pullback.fst G.X.hom (fieldSpecMap F K)
  let p₂ := pullback.snd G.X.hom (fieldSpecMap F K)
  let q₁ := pullback.fst H.X.hom (fieldSpecMap F K)
  let d := ((twistGroupBaseChangeIso σ.symm).app G).inv.hom.hom.left
  let e := ((twistGroupBaseChangeIso σ.symm).app H).hom.hom.hom.left
  have hd₁ : d ≫ p₁ = p₁ := pullback.lift_fst _ _ _
  have hd₂ : d ≫ p₂ = p₂ ≫ (fieldMap F K σ).left := pullback.lift_snd _ _ _
  have he₁ : e ≫ q₁ = q₁ := pullback.lift_fst _ _ _
  let x₀ := pullback.lift x.left U.hom.left
    ((Over.w x).trans (Over.w U.hom).symm)
  let x₁ := pullback.lift x.left U'.hom.left
    ((Over.w x).trans (Over.w U'.hom).symm)
  have h : x₀ ≫ d = x₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hd₁]
      exact (pullback.lift_fst ..).trans (pullback.lift_fst ..).symm
    · rw [Category.assoc, hd₂, ← Category.assoc]
      exact (congrArg (· ≫ (fieldMap F K σ).left) (pullback.lift_snd ..)).trans
        (pullback.lift_snd ..).symm
  change ((i.hom.app (op U')).hom x).left = x₀ ≫ (d ≫ j.hom.hom.hom.left ≫ e) ≫ q₁
  have hx := hj U' x
  change ((i.hom.app (op U')).hom x).left = x₁ ≫ j.hom.hom.hom.left ≫ q₁ at hx
  rw [hx, ← h]
  simp only [Category.assoc, he₁]

/-- In scheme coordinates the actual twist cocycle is the ratio between
the coefficient conjugate of the trivialization and the trivialization itself. -/
theorem twistTrivializationRelation {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a) (σ : Gal(K/F))
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj T.group.val)
    (hj : IsInduced F K j T.trivialization)
    (α : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj G.val)
    (hα : IsInduced F K α (T.inner.app (op (fieldTest F K)) ⟨a.val σ⟩).asIso) :
    (twistGroups σ.symm).map j.hom ≫ ((twistGroupBaseChangeIso σ.symm).app T.group.val).hom =
      ((twistGroupBaseChangeIso σ.symm).app G.val).hom ≫ α.hom ≫ j.hom := by
  let DG := (twistGroupBaseChangeIso σ.symm).app G.val
  let DH := (twistGroupBaseChangeIso σ.symm).app T.group.val
  let j' := DG.symm ≪≫ (twistGroups σ.symm).mapIso j ≪≫ DH
  have hj' := (induced_iff j' _).mp (restrictSchemeIsInduced σ hj)
  have hj0 := (induced_iff j _).mp hj
  have hα0 := (induced_iff α _).mp hα
  have he : j' ≪≫ j.symm = α := by
    apply (schemeIsoEquiv K G.val G.val).injective
    rw [schemeIsoEquiv_trans, hj', hα0]
    have hs : schemeIsoEquiv K _ _ j.symm = T.trivialization.symm := by
      apply Iso.ext
      have h := schemeIsoEquiv_trans j j.symm
      rw [hj0, Iso.self_symm_id] at h
      have hr : schemeIsoEquiv K G.val G.val (Iso.refl _) = Iso.refl _ := by
        apply (induced_iff _ _).mp
        intro U x
        exact (Category.comp_id x.left).symm.trans
          ((pullback.lift_fst ..).symm.trans (Category.id_comp _).symm)
      rw [hr] at h
      have hh := congrArg Iso.hom h
      apply (cancel_epi T.trivialization.hom).mp
      exact hh.symm.trans T.trivialization.hom_inv_id.symm
    rw [hs, ← T.cocycle_eq]
    rfl
  have h := congrArg Iso.hom he
  change (DG.inv ≫ (twistGroups σ.symm).map j.hom ≫ DH.hom) ≫ j.inv = α.hom at h
  apply (cancel_mono j.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h' := congrArg (DG.hom ≫ ·) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h'

open Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open Specs.CentralIsogenies (IsTorusRestriction)
open private factor_group_through_subgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

set_option backward.isDefEq.respectTransparency false in
/-- An automorphism over an adjoint automorphism preserving the adjoint torus
preserves the source torus under a central cover with kernel in that torus. -/
theorem centralPreimageStable {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (T : ClosedSubgroup G.val) (S : ClosedSubgroup H.val) (f : G.val ⟶ H.val)
    (fT : T.group ⟶ S.group) (hf : IsTorusRestriction f fT)
    (Z : ClosedSubgroup G.val) (hZ : IsSchemeKernel f Z) (hZT : IsSubgroupOf Z T)
    (α : G.val ≅ G.val) (β : H.val ≅ H.val) (b : S.group ≅ S.group)
    (h : α.hom ≫ f = f ≫ β.hom) (hb : b.hom ≫ S.inclusion = S.inclusion ≫ β.hom) :
    ∃ a : T.group ≅ T.group, a.hom ≫ T.inclusion = T.inclusion ≫ α.hom := by
  let _ : IsAffine G.val.X.left := G.property.1
  let _ := T.isClosedImmersion
  let _ : IsAffine T.group.X.left := isAffine_of_isAffineHom T.inclusion.hom.hom.left
  have hpre := (ExceptionalIwahoriImageComparison.centralTorusAndNormalizerPreimages
    G H T S f fT hf Z hZ hZT).1
  have lift (α₁ : G.val ≅ G.val) (β₁ : H.val ≅ H.val) (b₁ : S.group ≅ S.group)
      (h₁ : α₁.hom ≫ f = f ≫ β₁.hom)
      (hb₁ : b₁.hom ≫ S.inclusion = S.inclusion ≫ β₁.hom) :
      ∃ a₁ : T.group ⟶ T.group, a₁ ≫ T.inclusion = T.inclusion ≫ α₁.hom := by
    have he : (fT ≫ b₁.hom) ≫ S.inclusion = (T.inclusion ≫ α₁.hom) ≫ f := by
      simp only [Category.assoc, hb₁, h₁, ← reassoc_of% hf.1]
    have hh : FactorsThrough S ((T.inclusion ≫ α₁.hom).hom.hom ≫ f.hom.hom) :=
      ⟨(fT ≫ b₁.hom).hom.hom, congrArg (fun g => g.hom.hom) he⟩
    obtain ⟨t, ht⟩ := (hpre T.group.X _).mp hh
    exact factor_group_through_subgroup T _ t ht
  have hinv : α.inv ≫ f = f ≫ β.inv := by
    apply (cancel_mono β.hom).mp
    rw [Category.assoc, ← h, ← Category.assoc, α.inv_hom_id, Category.id_comp, Category.assoc, β.inv_hom_id, Category.comp_id]
  have hbinv : b.inv ≫ S.inclusion = S.inclusion ≫ β.inv := by
    apply (cancel_mono β.hom).mp
    rw [Category.assoc, ← hb, ← Category.assoc, b.inv_hom_id, Category.id_comp, Category.assoc, β.inv_hom_id, Category.comp_id]
  obtain ⟨a, ha⟩ := lift α β b h hb
  obtain ⟨d, hd⟩ := lift α.symm β.symm b.symm hinv hbinv
  change d ≫ T.inclusion = T.inclusion ≫ α.inv at hd
  let _ : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  let _ : Mono T.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono T.inclusion.hom.hom›
  refine ⟨⟨a, d, (cancel_mono T.inclusion).mp ?_, (cancel_mono T.inclusion).mp ?_⟩, ha⟩
  · rw [Category.assoc, hd, ← Category.assoc, ha, Category.assoc,
      α.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, ha, ← Category.assoc, hd, Category.assoc,
      α.inv_hom_id, Category.comp_id, Category.id_comp]

open private pushSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.OrderedRootProducts
open Specs.ExceptionalInnerSplitSubtorus (coefficientChange)

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the subgroup comparison with the descent operator
follows from equivariance of its closed inclusion. -/
theorem descendedSubgroupEquivariant {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : GroupScheme F} (U : ClosedSubgroup G)
    (T : ClosedSubgroup ((groupBaseChange F K).obj G))
    (σ : Gal(K/F)) (d : (twistGroups σ).obj T.group ≅ T.group)
    (hd : d.hom ≫ T.inclusion =
      (twistGroups σ).map T.inclusion ≫ ((twistGroupBaseChangeIso σ).app G).hom)
    (e : (groupBaseChange F K).obj U.group ≅ T.group)
    (he : e.hom ≫ T.inclusion = (groupBaseChange F K).map U.inclusion) :
    (twistGroups σ).map e.hom ≫ d.hom =
      ((twistGroupBaseChangeIso σ).app U.group).hom ≫ e.hom := by
  let D := twistGroupBaseChangeIso σ
  let B := groupBaseChange F K
  let C := twistGroups σ
  let _ := T.isClosedImmersion
  let _ : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  let _ : Mono T.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono T.inclusion.hom.hom›
  apply (cancel_mono T.inclusion).mp
  change (C.map e.hom ≫ d.hom) ≫ T.inclusion =
    ((D.app U.group).hom ≫ e.hom) ≫ T.inclusion
  rw [Category.assoc, hd, ← Category.assoc (C.map e.hom), ← Functor.map_comp, he,
    Category.assoc, he]
  exact D.hom.naturality U.inclusion

set_option backward.isDefEq.respectTransparency false in
/-- A reference torus preserved by the linear inner action descends through
the actual twist trivialization. The semilinear part comes from the reference
torus being defined over the ground field. -/
theorem descendTorusThroughTwist {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K]
    {G : AffineAlgebraicGroup F} {Q : AdjointQuotient G}
    {a : PointCocycle (S := K) Q.quotient.val} (T : Twist a) (σ : Gal(K/F))
    (hσ : Subgroup.zpowers σ = ⊤)
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj T.group.val)
    (hj : IsInduced F K j T.trivialization)
    (α : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj G.val)
    (hα : IsInduced F K α (T.inner.app (op (fieldTest F K)) ⟨a.val σ⟩).asIso)
    (A : GroupScheme F) (m : A ⟶ G.val)
    (U : ClosedSubgroup ((groupBaseChange F K).obj G.val)) (hU : IsSplitTorus U.group)
    (u : U.group ≅ (groupBaseChange F K).obj A)
    (hu : u.hom ≫ (groupBaseChange F K).map m = U.inclusion)
    (b : U.group ≅ U.group) (hb : b.hom ≫ U.inclusion = U.inclusion ≫ α.hom) :
    ∃ (V : ClosedSubgroup T.group.val) (v : (groupBaseChange F K).obj V.group ≅ U.group),
      Specs.GeometricRadicals.IsTorus V.group ∧
      v.hom ≫ U.inclusion ≫ j.hom = (groupBaseChange F K).map V.inclusion ∧
      (v ≪≫ u).hom.hom.hom.left ≫ coefficientChange σ.symm A ≫
          (u.symm ≪≫ b ≪≫ u).hom.hom.hom.left =
        coefficientChange σ.symm V.group ≫ (v ≪≫ u).hom.hom.hom.left := by
  let σ' := σ.symm
  let C := twistGroups σ'
  let D := twistGroupBaseChangeIso σ'
  let U' := pushSubgroup j U
  let d := C.mapIso u ≪≫ D.app A ≪≫ u.symm ≪≫ b
  have hDA : C.map ((groupBaseChange F K).map m) ≫ (D.app G.val).hom =
      (D.app A).hom ≫ (groupBaseChange F K).map m := D.hom.naturality _
  have h₁ := twistTrivializationRelation T σ j hj α hα
  change C.map j.hom ≫ (D.app T.group.val).hom =
    (D.app G.val).hom ≫ α.hom ≫ j.hom at h₁
  have hd : d.hom ≫ U'.inclusion = C.map U'.inclusion ≫ (D.app T.group.val).hom := by
    change (C.map u.hom ≫ (D.app A).hom ≫ u.inv ≫ b.hom) ≫ (U.inclusion ≫ j.hom) =
      C.map (U.inclusion ≫ j.hom) ≫ (D.app T.group.val).hom
    rw [Functor.map_comp]
    simp only [Category.assoc, reassoc_of% hb, h₁]
    have hi : u.inv ≫ U.inclusion = (groupBaseChange F K).map m := by
      rw [← hu, Iso.inv_hom_id_assoc]
    have hm := congrArg C.map hu
    rw [Functor.map_comp] at hm
    rw [reassoc_of% hi, ← reassoc_of% hDA, reassoc_of% hm]
  obtain ⟨V, v, hV, hv⟩ := descendStableTorus (σ := σ') (Subgroup.zpowers_inv.trans hσ)
    T.group U' hU d hd
  refine ⟨V, v, hV, hv, ?_⟩
  have heq := congrArg (fun k => k.hom.hom.left)
    (descendedSubgroupEquivariant V U' σ' d hd v hv)
  change v.hom.hom.hom.left ≫
      (u.hom.hom.hom.left ≫ coefficientChange σ' A ≫ u.inv.hom.hom.left ≫ b.hom.hom.hom.left) =
    coefficientChange σ' V.group ≫ v.hom.hom.hom.left at heq
  change (v.hom.hom.hom.left ≫ u.hom.hom.hom.left) ≫ coefficientChange σ' A ≫
      (u.inv.hom.hom.left ≫ b.hom.hom.hom.left ≫ u.hom.hom.hom.left) =
    coefficientChange σ' V.group ≫ (v.hom.hom.hom.left ≫ u.hom.hom.hom.left)
  simpa only [Category.assoc] using congrArg (· ≫ u.hom.hom.hom.left) heq

open Specs.BorelsAndChambers (subgroupRoots)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open private basedIso_pos_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
open private base_isPos_iff_subgroupRoots from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting
open private kBorel_smooth_connected subgroupOf_limit_of_rootSigns
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option backward.isDefEq.respectTransparency false in
/-- The marked positive Borel is contained in the limit subgroup of a
cocharacter whose marked vector lies in the closed dominant chamber. -/
theorem dominantMarkedBorel {K : Type u} [Field K] {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M K) (c : Cocharacter C.realization.pinned.pair.T.group)
    (J : LimitDecomposition (c ≫ C.realization.pinned.pair.T.inclusion))
    (h : let P := C.realization.pinned.pair
      let _ := C.realization.attached.comm
      ∀ i, D.base.IsPos i →
        0 ≤ (ApartmentRoots.split D.datum ℚ).root i
          ((1 : ℚ) ⊗ₜ[ℤ] markedCocharacterMap C (𝟙 P.T.group) (Additive.ofMul c))) :
    IsSubgroupOf C.realization.pinned.pair.B J.parabolic := by
  let P := C.realization.pinned.pair
  let _ := C.realization.attached.comm
  let e := C.realization.datumIso
  obtain ⟨hs, hc⟩ := kBorel_smooth_connected P.G P.B P.borel
  apply subgroupOf_limit_of_rootSigns P.G P.reductive P.T P.B P.split P.maximal hs hc P.containsTorus c J
  intro α hα
  let i := e.val.indexEquiv.symm α
  have hi : e.val.indexEquiv i = α := e.val.indexEquiv.apply_symm_apply _
  have hp : D.base.IsPos i := (basedIso_pos_iff e i).mpr (hi.symm ▸
    (base_isPos_iff_subgroupRoots C.realization.attached α).mpr hα)
  have hχ : markedCharacter C i = α.val := by
    have h₁ : e.val.weightEquiv (D.datum.root i) =
        C.realization.attached.datum.rootDatum.root (e.val.indexEquiv i) :=
      e.val.toHom.root_weightMap_apply _ _ _
    have h₂ := C.realization.attached.datum.root_eq α
    exact congrArg Additive.toMul (h₁.trans (congrArg _ hi) |>.trans h₂)
  have hpair := markedPairing C (𝟙 P.T.group) i c
  rw [Category.id_comp, hχ] at hpair
  have h₀ := h i hp
  change 0 ≤ RootData.extendFunctional ℚ (D.datum.root' i)
    ((1 : ℚ) ⊗ₜ[ℤ] markedCocharacterMap C (𝟙 P.T.group) (Additive.ofMul c)) at h₀
  rw [RootData.extendFunctional_one_tmul, hpair] at h₀
  exact_mod_cast h₀


open IntegralSemisimpleModel (forgetFibrePoint)

set_option backward.isDefEq.respectTransparency false in
private theorem markedSectionComparison {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    {G : AffineAlgebraicGroup F} (iG : G.val ≅ (fibre F).obj M.group)
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj G.val)
    (hf : IsMarkedTrivialization C iG (Iso.refl _) f)
    (q : fieldTest F K ⟶ G.val.X) :
    markedGroundPoint C ((geometricSectionsEquiv K G.val).symm q ≫ f.inv.hom.hom) =
      forgetFibrePoint M.group (CommAlgCat.of F K) (q ≫ iG.hom.hom.hom) := by
  let qK := (geometricSectionsEquiv K G.val).symm q
  have hqK : qK.left ≫ pullback.fst G.val.X.hom (fieldSpecMap F K) = q.left :=
    (geometricSectionsEquiv_left G.val qK).symm.trans
      (congrArg Over.Hom.left ((geometricSectionsEquiv K G.val).apply_symm_apply q))
  let p : (testSpec K).obj (op (CommAlgCat.of K K)) ⟶ 𝟙_ (SchemeOver K) := toUnit _
  have hp : p.left = 𝟙 _ :=
    ((Category.comp_id p.left).symm.trans (Over.w p)).trans (Spec.map_id _)
  have hf₀ : f.hom.hom.hom.left ≫ pullback.fst G.val.X.hom (fieldSpecMap F K) ≫
      iG.hom.hom.hom.left ≫ pullback.fst M.group.X.hom _ =
        C.groupIso.inv.hom.hom.left ≫ pullback.fst M.group.X.hom _ := by
    simpa only [IsMarkedTrivialization, Iso.refl_inv, Category.comp_id] using hf
  apply Over.OverMorphism.ext
  change ((p.left ≫ qK.left ≫ f.inv.hom.hom.left) ≫ C.groupIso.inv.hom.hom.left) ≫
      pullback.fst M.group.X.hom _ =
    (q.left ≫ iG.hom.hom.hom.left) ≫ pullback.fst M.group.X.hom _
  have hInv : f.inv.hom.hom.left ≫ f.hom.hom.hom.left = 𝟙 _ :=
    congrArg (fun g => g.hom.hom.left) f.inv_hom_id
  simp only [Category.assoc, hp, Category.id_comp]
  rw [← hf₀, reassoc_of% hInv]
  exact (reassoc_of% hqK) _

set_option backward.isDefEq.respectTransparency false in
private theorem markedProjectionComparison {F K : Type u} [Field F] [Field K] [Algebra F K]
    (d : fibre K ≅ fibre F ⋙ groupBaseChange F K)
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (C : MarkedFibre M K) (C' : MarkedFibre M' K)
    {G H : AffineAlgebraicGroup F} (q : G.val ⟶ H.val)
    (iG : G.val ≅ (fibre F).obj M.group) (iH : H.val ≅ (fibre F).obj M'.group)
    (c : MarkedCentralCover M M')
    (hq : q ≫ iH.hom = iG.hom ≫ (fibre F).map c.map) :
    (markedReferenceIso d C iG).hom ≫ (groupBaseChange F K).map q =
      (C.groupIso.inv ≫ (fibre K).map c.map ≫ C'.groupIso.hom) ≫
        (markedReferenceIso d C' iH).hom := by
  have hq' : iG.inv ≫ q = (fibre F).map c.map ≫ iH.inv := by
    apply (cancel_mono iH.hom).mp
    rw [Category.assoc, hq, Iso.inv_hom_id_assoc, Category.assoc, iH.inv_hom_id, Category.comp_id]
  let B := groupBaseChange F K
  have hmap : B.map iG.inv ≫ B.map q = B.map ((fibre F).map c.map) ≫ B.map iH.inv := by
    rw [← Functor.map_comp, ← Functor.map_comp, hq']
  have hd : (fibre K).map c.map ≫ (d.app M'.group).hom =
      (d.app M.group).hom ≫ B.map ((fibre F).map c.map) := d.hom.naturality _
  change ((C.groupIso.inv ≫ (d.app M.group).hom) ≫ B.map iG.inv) ≫ B.map q =
    (C.groupIso.inv ≫ (fibre K).map c.map ≫ C'.groupIso.hom) ≫
      ((C'.groupIso.inv ≫ (d.app M'.group).hom) ≫ B.map iH.inv)
  rw [Category.assoc (C.groupIso.inv ≫ (d.app M.group).hom), hmap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hd]


set_option backward.isDefEq.respectTransparency false in
private theorem conjugationIso_natural {K : Type u} [Field K] {G H : GroupScheme K}
    (f : G ⟶ H) (x : 𝟙_ (SchemeOver K) ⟶ G.X) :
    (conjugationIso x).hom ≫ f = f ≫ (conjugationIso (x ≫ f.hom.hom)).hom := by
  apply Grp.hom_ext
  change conjugation x ≫ f.hom.hom = f.hom.hom ≫ conjugation (x ≫ f.hom.hom)
  rw [comp_conjugation]
  unfold conjugation
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.id_comp, Category.assoc]

open Specs.GeometricRadicals (IsTorus IsMaximalTorus baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open private groupBaseChangeTowerIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter
open private maximal_of_square from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private splitTorus_baseChange isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private factor_of_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

private theorem torus_splits_over_algClosed {F L : Type u} [Field F] [Field L] [Algebra F L]
    [IsAlgClosed L] {T : GroupScheme F} (hT : IsTorus T) :
    IsSplitTorus ((groupBaseChange F L).obj T) := by
  obtain ⟨E, _, _, _, r, ⟨t⟩⟩ := hT
  let f : E →ₐ[F] L := IsAlgClosed.lift
  let _ : Algebra E L := f.toRingHom.toAlgebra
  let _ : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (f.commutes a).symm)
  obtain ⟨u⟩ := splitTorus_baseChange (k := E) L r
  exact ⟨r, ⟨((groupBaseChangeTowerIso (k := F) (K := E) (L := L)).app T).symm ≪≫
    (groupBaseChange E L).mapIso t ≪≫ u⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Geometric maximality of the marked torus implies maximality of the
torus over the ground field, by reflecting containment along scalar extension. -/
theorem maximalTorusOfComparison {F K : Type u} [Field F] [Field K] [Algebra F K]
    {G : GroupScheme F} {H : GroupScheme K} (U : ClosedSubgroup G)
    (hU : IsTorus U.group) (T : ClosedSubgroup H) (hT : IsGeometricallyMaximal T)
    (f : H ≅ (groupBaseChange F K).obj G)
    (uK : (groupBaseChange F K).obj U.group ≅ T.group)
    (hu : uK.hom ≫ T.inclusion ≫ f.hom = (groupBaseChange F K).map U.inclusion) :
    IsMaximalTorus U := by
  let L := AlgebraicClosure K
  let B := groupBaseChange F K
  let C := groupBaseChange K L
  obtain ⟨hTc, hTm⟩ := hT
  let TL := baseChangedSubgroup L T hTc
  let UK := baseChangedSubgroup K U (_root_.LinearAlgebraicGroups.baseChangeClosedSubgroup F K
    U.inclusion U.isClosedImmersion)
  let UL := baseChangedSubgroup L UK (_root_.LinearAlgebraicGroups.baseChangeClosedSubgroup K L
    UK.inclusion UK.isClosedImmersion)
  have hUeq : uK.inv ≫ UK.inclusion = T.inclusion ≫ f.hom := by
    change uK.inv ≫ B.map U.inclusion = _
    rw [← hu, Iso.inv_hom_id_assoc]
  have hUL : IsMaximalTorus UL := by
    apply maximal_of_square (C.mapIso f) TL UL (C.mapIso uK.symm) _ hTm
    change C.map uK.inv ≫ C.map UK.inclusion = C.map T.inclusion ≫ C.map f.hom
    rw [← C.map_comp, ← C.map_comp, hUeq]
  refine ⟨hU, ?_⟩
  intro S hS hUS
  obtain ⟨w, hw⟩ := hUS
  let SK := baseChangedSubgroup K S (_root_.LinearAlgebraicGroups.baseChangeClosedSubgroup F K
    S.inclusion S.isClosedImmersion)
  let SL := baseChangedSubgroup L SK (_root_.LinearAlgebraicGroups.baseChangeClosedSubgroup K L
    SK.inclusion SK.isClosedImmersion)
  let d := groupBaseChangeTowerIso (k := F) (K := K) (L := L)
  have hSL : IsTorus SL.group := by
    obtain ⟨r, ⟨g⟩⟩ := torus_splits_over_algClosed (L := L) hS
    exact isTorus_of_split ⟨r, ⟨d.app S.group ≪≫ g⟩⟩
  have hUSL : IsSubgroupOf UL SL := ⟨(B ⋙ C).map w, by
    change (B ⋙ C).map w ≫ (B ⋙ C).map S.inclusion = (B ⋙ C).map U.inclusion
    rw [← Functor.map_comp, hw]⟩
  obtain ⟨z, hz⟩ := hUL.2 SL hSL hUSL
  change z ≫ (B ⋙ C).map U.inclusion = (B ⋙ C).map S.inclusion at hz
  let D := groupBaseChange F L
  let z' := (d.app S.group).inv ≫ z ≫ (d.app U.group).hom
  have hz' : z' ≫ D.map U.inclusion = D.map S.inclusion := by
    have hU' := d.hom.naturality U.inclusion
    have hS' := d.hom.naturality S.inclusion
    change (B ⋙ C).map U.inclusion ≫ (d.app G).hom = (d.app U.group).hom ≫ D.map U.inclusion at hU'
    change (B ⋙ C).map S.inclusion ≫ (d.app G).hom = (d.app S.group).hom ≫ D.map S.inclusion at hS'
    simp only [z', Category.assoc, ← hU']
    calc
      _ = (d.app S.group).inv ≫ (z ≫ (B ⋙ C).map U.inclusion) ≫ (d.app G).hom := by
        simp only [Category.assoc]
      _ = (d.app S.group).inv ≫ (B ⋙ C).map S.inclusion ≫ (d.app G).hom :=
        congrArg (fun i => (d.app S.group).inv ≫ i ≫ (d.app G).hom) hz
      _ = _ := by rw [hS', Iso.inv_hom_id_assoc]
  let _ := U.isClosedImmersion
  obtain ⟨i, hi⟩ := factor_of_baseChange L S.inclusion.hom.hom U.inclusion.hom.hom
    z'.hom.hom (congrArg (fun g => g.hom.hom) hz')
  exact factor_group_through_subgroup U S.inclusion i hi

open Specs.ExceptionalAffineBuilding (lengthZeroNormalizer)
open private conjugates_iff_iso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags

open Specs.IntegralSemisimpleModel (torusPoint)
open Specs.CharacterPairing (characterValue pairing)
open private fibrePointsEquiv forgetFibrePoint_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private noncomputable def latticeCharacter {K : Type u} [Field K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K) (x : D.X) :
    Character C.realization.pinned.pair.T.group :=
  Additive.toMul (C.realization.datumIso.val.weightEquiv x)

set_option backward.isDefEq.respectTransparency false in
private theorem latticeCharacterPairing {K : Type u} [Field K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K) (x : D.X)
    (y : Cocharacter C.realization.pinned.pair.T.group) :
    D.datum.toLinearMap x (C.realization.datumIso.val.coweightEquiv (Additive.ofMul y)) =
      pairing C.realization.pinned.pair.T.group (latticeCharacter C x) y := by
  let _ := C.realization.attached.comm
  let d := C.realization.datumIso.val
  exact (d.toLinearMap_weightEquiv x (Additive.ofMul y)).symm.trans
    (C.realization.attached.datum.pairing_eq _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem centralTorusPullback {K : Type u} [Field K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (C : MarkedFibre M K) (C' : MarkedFibre M' K)
    (x : E.X) :
    let fT := C.torusIso.inv ≫ (fibre K).map c.torusMap ≫ C'.torusIso.hom
    fT ≫ latticeCharacter C' x = latticeCharacter C (c.pullCharacter x) := by
  let P := C.realization.pinned.pair
  let P' := C'.realization.pinned.pair
  let f := C.groupIso.inv ≫ (fibre K).map c.map ≫ C'.groupIso.hom
  let fT := C.torusIso.inv ≫ (fibre K).map c.torusMap ≫ C'.torusIso.hom
  change fT ≫ latticeCharacter C' x = _
  obtain ⟨φ, hφ, hφi⟩ := ExceptionalValuedTorusNormalizer.markedFibreTorusCoordinates
    D M C.realization C.groupIso C.torusIso C.torus_comm C.torus_eval
  obtain ⟨ψ, hψ, hψi⟩ := ExceptionalValuedTorusNormalizer.markedFibreTorusCoordinates
    E M' C'.realization C'.groupIso C'.torusIso C'.torus_comm C'.torus_eval
  apply _root_.LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters P.split
  intro R t
  obtain ⟨v, rfl⟩ := (φ R).surjective t
  let χ := c.pullCharacter.toAddMonoidHom.toMultiplicative
  let w := v.comp χ
  have hT : fT ≫ P'.T.inclusion = P.T.inclusion ≫ f := (c.fibre K C C').2.1.1
  have hpic : (fT ≫ P'.T.inclusion ≫ C'.groupIso.inv).hom.hom =
      (P.T.inclusion ≫ C.groupIso.inv ≫ (fibre K).map c.map).hom.hom := by
    apply congrArg (fun i : P.T.group ⟶ (fibre K).obj M'.group => i.hom.hom)
    rw [← Category.assoc fT, hT]
    simp [f, Category.assoc]
  have ht : φ R v ≫ fT.hom.hom = ψ R w := by
    let _ := P'.T.isClosedImmersion
    let _ : Mono P'.T.inclusion.hom.hom := Over.mono_of_mono_left _
    let _ : IsIso C'.groupIso.inv.hom.hom := inferInstanceAs
      (IsIso ((Grp.forget (SchemeOver K)).map C'.groupIso.inv))
    apply (cancel_mono P'.T.inclusion.hom.hom).mp
    apply (cancel_mono C'.groupIso.inv.hom.hom).mp
    apply (fibrePointsEquiv M'.group R).injective
    change forgetFibrePoint M'.group R (((φ R v ≫ fT.hom.hom) ≫ P'.T.inclusion.hom.hom) ≫
      C'.groupIso.inv.hom.hom) = forgetFibrePoint M'.group R
        ((ψ R w ≫ P'.T.inclusion.hom.hom) ≫ C'.groupIso.inv.hom.hom)
    simp only [Category.assoc, ← Grp.comp_hom_hom, hpic]
    change forgetFibrePoint M'.group R
      ((φ R v ≫ P.T.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom) ≫ ((fibre K).map c.map).hom.hom) =
      forgetFibrePoint M'.group R (ψ R w ≫ P'.T.inclusion.hom.hom ≫ C'.groupIso.inv.hom.hom)
    rw [forgetFibrePoint_comp, hφi, hψi]
    exact c.marking.2.2 _ v
  calc
    _ = characterValue (latticeCharacter C' x) R (φ R v ≫ fT.hom.hom) := by
      unfold characterValue
      rw [Grp.comp_hom_hom, Category.assoc]
    _ = (w (Multiplicative.ofAdd x) : R) := by
      rw [ht]
      exact hψ R w x
    _ = _ := (hφ R v (c.pullCharacter x)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The central cover induces the marked pushforward on the integral
cocharacter lattices of the actual split tori. -/
theorem markedCentralCocharacter {K : Type u} [Field K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (C : MarkedFibre M K) (C' : MarkedFibre M' K)
    (y : Cocharacter C.realization.pinned.pair.T.group) :
    let fT := C.torusIso.inv ≫ (fibre K).map c.torusMap ≫ C'.torusIso.hom
    let _ := C.realization.attached.comm
    let _ := C'.realization.attached.comm
    C'.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ fT)) =
      c.pushCocharacter (C.realization.datumIso.val.coweightEquiv (Additive.ofMul y)) := by
  let fT := C.torusIso.inv ≫ (fibre K).map c.torusMap ≫ C'.torusIso.hom
  let _ := C.realization.attached.comm
  let _ := C'.realization.attached.comm
  dsimp only
  apply E.datum.toLinearMap.flip.toPerfPair.injective
  ext x
  change E.datum.toLinearMap x
    (C'.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ fT))) =
    E.datum.toLinearMap x (c.pushCocharacter (C.realization.datumIso.val.coweightEquiv (Additive.ofMul y)))
  rw [← c.pairing, latticeCharacterPairing, latticeCharacterPairing]
  have h := centralTorusPullback c C C' x
  change fT ≫ latticeCharacter C' x = latticeCharacter C (c.pullCharacter x) at h
  exact congrArg (Function.invFun (CharacterPairing.powerMorphism (k := K)))
    ((Category.assoc y fT (latticeCharacter C' x)).trans (congrArg (y ≫ ·) h))

/-- A finite-index character restriction makes the dual pushforward injective. -/
theorem markedCentralCocharacter_injective {D E : BasedRootDatum.{u}}
    {M : Model D} {M' : Model E} (c : MarkedCentralCover M M') :
    Function.Injective c.pushCocharacter := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm ?_ bot_le
  intro y hy
  change y = 0
  have hzero := LinearMap.mem_ker.mp hy
  apply D.datum.toLinearMap.flip.toPerfPair.injective
  ext x
  let χ := c.pullCharacter.toAddMonoidHom.toMultiplicative
  let _ : Finite (Multiplicative D.X ⧸ χ.range) := c.characterIndex
  let p := QuotientGroup.mk' χ.range
  let z := Multiplicative.ofAdd x
  let n := orderOf (p z)
  have hn : 0 < n := orderOf_pos _
  have hp : p (z ^ n) = 1 := by rw [p.map_pow, pow_orderOf_eq_one]
  obtain ⟨w, hw⟩ := (QuotientGroup.eq_one_iff _).mp hp
  have hw' : c.pullCharacter w.toAdd = n • x := congrArg Multiplicative.toAdd hw
  have hx : n • D.datum.toLinearMap x y = 0 := by
    calc
      _ = D.datum.toLinearMap (n • x) y := by
        rw [map_nsmul]
        rfl
      _ = _ := by rw [← hw', c.pairing, hzero, LinearMap.map_zero]
  change D.datum.toLinearMap x y = D.datum.toLinearMap x 0
  rw [LinearMap.map_zero]
  exact (nsmul_eq_zero_iff_right hn.ne').mp hx


open Specs.IntegralSemisimpleModel (TorusValues)
open private labelConjugation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open private torusValues_weylConjugation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private groundSectionsEquiv groundSectionsEquiv_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

set_option backward.isDefEq.respectTransparency false in
private theorem markedNormalizerCharacter {K : Type u} [Field K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    (F : FibreNormalizer M K)
    (g : 𝟙_ (SchemeOver K) ⟶ C.realization.pinned.pair.G.val.X)
    (b : C.realization.pinned.pair.T.group ≅ C.realization.pinned.pair.T.group)
    (hb : b.hom ≫ C.realization.pinned.pair.T.inclusion =
      C.realization.pinned.pair.T.inclusion ≫ (conjugationIso g).hom)
    (m : let _ := F.torusComm; 𝟙_ (SchemeOver K) ⟶ F.identification.normalizer.group.X)
    (hm : markedGroundPoint C g = F.point m) (x : D.X) :
    b.hom ≫ latticeCharacter C x =
      latticeCharacter C ((F.label m).val.weightEquiv.symm x) := by
  let _ := F.torusComm
  let P := C.realization.pinned.pair
  let P' := F.realization.pinned.pair
  let J := F.identification
  let w := F.label m
  let actionOnCharacters := w.val.weightEquiv.symm.toLinearMap.toAddMonoidHom.toMultiplicative
  let g' : 𝟙_ (SchemeOver K) ⟶ P'.G.val.X := m ≫ J.normalizer.inclusion.hom.hom
  let j := C.groupIso.symm ≪≫ F.fibreIso
  have hj : j.hom.hom.hom ≫ F.fibreIso.inv.hom.hom = C.groupIso.inv.hom.hom :=
    congrArg (fun i : P.G.val ⟶ (fibre K).obj M.group => i.hom.hom)
      (by
        change (C.groupIso.inv ≫ F.fibreIso.hom) ≫ F.fibreIso.inv = C.groupIso.inv
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  have hg : g ≫ j.hom.hom.hom = g' := by
    let _ : IsIso F.fibreIso.inv.hom.hom := inferInstanceAs
      (IsIso ((Grp.forget (SchemeOver K)).map F.fibreIso.inv))
    apply (cancel_mono F.fibreIso.inv.hom.hom).mp
    apply (groundSectionsEquiv ((fibre K).obj M.group)).injective
    apply (fibrePointsEquiv M.group (CommAlgCat.of K K)).injective
    simp only [groundSectionsEquiv_apply, Category.assoc, hj]
    change markedGroundPoint C g = forgetFibrePoint M.group (CommAlgCat.of K K)
      (toUnit _ ≫ m ≫ J.normalizer.inclusion.hom.hom ≫ F.fibreIso.inv.hom.hom)
    exact hm.trans (F.point_eq m)
  obtain ⟨ψ, hψ, hψi⟩ := ExceptionalValuedTorusNormalizer.markedFibreTorusCoordinates
    D M C.realization C.groupIso C.torusIso C.torus_comm C.torus_eval
  have hτ (R : TestAlgebra K) (v : TorusValues D (CommAlgCat.of Integers.{u} R)) :
      ψ R v ≫ P.T.inclusion.hom.hom ≫ j.hom.hom.hom =
        F.torusValues R v ≫ P'.T.inclusion.hom.hom := by
    let _ : IsIso F.fibreIso.inv.hom.hom := inferInstanceAs
      (IsIso ((Grp.forget (SchemeOver K)).map F.fibreIso.inv))
    apply (cancel_mono F.fibreIso.inv.hom.hom).mp
    apply (fibrePointsEquiv M.group R).injective
    simp only [Category.assoc, hj]
    exact (hψi R v).trans (F.torusPoint_eq R v).symm
  let l := J.labelEquiv (F.labelIso w)
  let δ := J.image.conjugation l
  have hδ : δ.hom ≫ P'.T.inclusion = P'.T.inclusion ≫ (conjugationIso g').hom := by
    apply Grp.hom_ext
    have h := labelConjugation J.image l m (F.projection m)
    change (δ.hom ≫ P'.T.inclusion).hom.hom =
      (toUnit P'.T.group.X ≫ g') * P'.T.inclusion.hom.hom * (toUnit P'.T.group.X ≫ g')⁻¹ at h
    change (δ.hom ≫ P'.T.inclusion).hom.hom = P'.T.inclusion.hom.hom ≫ conjugation g'
    rw [comp_conjugation]
    exact h
  have hI : (conjugationIso g).hom ≫ j.hom = j.hom ≫ (conjugationIso g').hom := by
    rw [conjugationIso_natural, hg]
  have hB : b.hom ≫ P.T.inclusion ≫ j.hom =
      (P.T.inclusion ≫ j.hom) ≫ (conjugationIso g').hom := by
    rw [← Category.assoc b.hom, hb, Category.assoc, hI, Category.assoc]
  have hBV := congrArg (fun z : P.T.group ⟶ P'.G.val => z.hom.hom) hB
  have hδV := congrArg (fun z : P'.T.group ⟶ P'.G.val => z.hom.hom) hδ
  have hEq (R : TestAlgebra K) (v : TorusValues D (CommAlgCat.of Integers.{u} R)) :
      ψ R v ≫ b.hom.hom.hom = ψ R (v.comp actionOnCharacters) := by
    let _ := P.T.isClosedImmersion
    let _ : Mono P.T.inclusion.hom.hom := Over.mono_of_mono_left _
    let _ : IsIso j.hom.hom.hom := inferInstanceAs
      (IsIso ((Grp.forget (SchemeOver K)).map j.hom))
    apply (cancel_mono P.T.inclusion.hom.hom).mp
    apply (cancel_mono j.hom.hom.hom).mp
    have h₁ := congrArg (ψ R v ≫ ·) hBV
    change ψ R v ≫ (b.hom.hom.hom ≫ P.T.inclusion.hom.hom ≫ j.hom.hom.hom) =
      ψ R v ≫ ((P.T.inclusion.hom.hom ≫ j.hom.hom.hom) ≫ (conjugationIso g').hom.hom.hom) at h₁
    calc
      _ = (ψ R v ≫ P.T.inclusion.hom.hom ≫ j.hom.hom.hom) ≫ (conjugationIso g').hom.hom.hom := by
        simpa only [Category.assoc] using h₁
      _ = (F.torusValues R v ≫ P'.T.inclusion.hom.hom) ≫ (conjugationIso g').hom.hom.hom :=
        congrArg (· ≫ (conjugationIso g').hom.hom.hom) (hτ R v)
      _ = F.torusValues R (v.comp actionOnCharacters) ≫ P'.T.inclusion.hom.hom := by
        have hh := torusValues_weylConjugation F R w v
        change F.torusValues R (v.comp actionOnCharacters) = F.torusValues R v ≫ δ.hom.hom.hom at hh
        change δ.hom.hom.hom ≫ P'.T.inclusion.hom.hom =
          P'.T.inclusion.hom.hom ≫ (conjugationIso g').hom.hom.hom at hδV
        rw [hh, Category.assoc, Category.assoc, hδV]
      _ = _ := by
        rw [Category.assoc]
        exact (hτ R (v.comp actionOnCharacters)).symm
  apply _root_.LinearAlgebraicGroups.RootData.CharacterPairing.characterValuesDetectCharacters P.split
  intro R t
  obtain ⟨v, rfl⟩ := (ψ R).surjective t
  calc
    _ = characterValue (latticeCharacter C x) R (ψ R v ≫ b.hom.hom.hom) := by
      unfold characterValue
      rw [Grp.comp_hom_hom, Category.assoc]
    _ = ((v.comp actionOnCharacters) (Multiplicative.ofAdd x) : R) := by
      rw [hEq]
      exact hψ R _ x
    _ = _ := (hψ R v (w.val.weightEquiv.symm x)).symm


set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by a section of the marked adjoint normalizer acts on
cocharacters by the integral Weyl operator underlying the affine linear part. -/
theorem markedAdjointCocharacterAction {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)} (Y : SplitLevel K c p p' e)
    (n : Y.ad.N)
    (g : 𝟙_ (SchemeOver K) ⟶ Y.ad_fibre.realization.pinned.pair.G.val.X)
    (hg : markedGroundPoint Y.ad_fibre g = (n : ExceptionalAffineBruhat.FieldPoints M' K))
    (b : Y.ad_fibre.realization.pinned.pair.T.group ≅ Y.ad_fibre.realization.pinned.pair.T.group)
    (hb : b.hom ≫ Y.ad_fibre.realization.pinned.pair.T.inclusion =
      Y.ad_fibre.realization.pinned.pair.T.inclusion ≫ (conjugationIso g).hom) :
    let C := Y.ad_fibre
    let _ := C.realization.attached.comm
    ∃ w : E.Y ≃ₗ[ℤ] E.Y, (Y.ad.affine n).linear = w.baseChange ℤ ℚ E.Y E.Y ∧
      ∀ y : Cocharacter C.realization.pinned.pair.T.group,
        C.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ b.hom)) =
          w (C.realization.datumIso.val.coweightEquiv (Additive.ofMul y)) := by
  let C := Y.ad_fibre
  let _ := C.realization.attached.comm
  obtain ⟨N, m, hm, hn⟩ := adjointAffineLinearPart Y n
  let _ := N.torusComm
  let w := (N.label m).val
  refine ⟨w.coweightEquiv.symm, hn, fun y => ?_⟩
  apply E.datum.toLinearMap.flip.toPerfPair.injective
  ext x
  let z := C.realization.datumIso.val.coweightEquiv (Additive.ofMul y)
  change E.datum.toLinearMap x (C.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ b.hom))) =
    E.datum.toLinearMap x (w.coweightEquiv.symm z)
  have hdual : E.datum.toLinearMap x (w.coweightEquiv.symm z) =
      E.datum.toLinearMap (w.weightEquiv.symm x) z := by
    have hd := w.toLinearMap_weightEquiv (w.weightEquiv.symm x) (w.coweightEquiv.symm z)
    rw [w.weightEquiv.apply_symm_apply, w.coweightEquiv.apply_symm_apply] at hd
    exact hd
  rw [hdual, latticeCharacterPairing, latticeCharacterPairing]
  have hχ := markedNormalizerCharacter C N g b hb m (hg.trans hm.symm) x
  exact congrArg (Function.invFun (CharacterPairing.powerMorphism (k := K)))
    ((Category.assoc y b.hom (latticeCharacter C x)).trans (congrArg (y ≫ ·) hχ))

open Specs.CellHomomorphism (pullbackCharacters)
open Specs.CharacterDescent (StandardLattice)
open private split_torus_pullback from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.RankTwoLifting
open private common_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi

private theorem multiplicativeGroup_isSplitTorus (K : Type u) [Field K] :
    IsSplitTorus (specGroup (groupAlgebra K IntegerCharacters)) := by
  refine ⟨1, ?_⟩
  obtain ⟨e⟩ := _root_.LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) 1
  let a : StandardLattice.{u} 1 ≃* IntegerCharacters.{u} :=
    MulEquiv.funUnique (Fin 1) IntegerCharacters
  exact ⟨(hopfSpec (CommRingCat.of K)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv K K a)).op ≪≫ e⟩

set_option backward.isDefEq.respectTransparency false in
/-- The fixed split subtorus of a split torus under an automorphism,
with factorization for all fixed cocharacters and maps from split tori. -/
theorem fixedSplitSubtorus {K : Type u} [Field K] {T : GroupScheme K} (hT : IsSplitTorus T)
    (a : T ≅ T) :
    ∃ S : ClosedSubgroup T, IsSplitTorus S.group ∧ S.inclusion ≫ a.hom = S.inclusion ∧
      ∀ {R : GroupScheme K}, IsSplitTorus R → ∀ f : R ⟶ T, f ≫ a.hom = f →
        ∃ m : R ⟶ S.group, m ≫ S.inclusion = f := by
  let χ (t : Character T) := (a.hom ≫ t) / t
  have hχ {R : GroupScheme K} (hR : IsSplitTorus R) (f : R ⟶ T) :
      (∀ t, f ≫ χ t = 1) ↔ f ≫ a.hom = f := by
    constructor
    · intro h
      apply (split_torus_pullback hR hT).1
      apply MonoidHom.ext
      intro t
      have ht := h t
      change (pullbackCharacters f) ((a.hom ≫ t) / t) = 1 at ht
      rw [map_div, div_eq_one] at ht
      exact (Category.assoc f a.hom t).trans ht
    · intro h t
      change (pullbackCharacters f) ((a.hom ≫ t) / t) = 1
      rw [map_div, div_eq_one]
      exact (Category.assoc f a.hom t).symm.trans (congrArg (· ≫ t) h)
  obtain ⟨S, hS, hk, _, hfac⟩ := common_kernel hT χ
  exact ⟨S, hS, (hχ hS S.inclusion).mp hk,
    fun hR f hf => hfac hR f ((hχ hR f).mpr hf)⟩

/-- Factorization on cocharacters of the fixed split subtorus is exact. -/
theorem fixedSplitSubtorusCocharacters {K : Type u} [Field K] {T : GroupScheme K}
    (hT : IsSplitTorus T) (a : T ≅ T) :
    ∃ S : ClosedSubgroup T, IsSplitTorus S.group ∧ S.inclusion ≫ a.hom = S.inclusion ∧
      Function.Injective (fun y : Cocharacter S.group => y ≫ S.inclusion) ∧
      Set.range (fun y : Cocharacter S.group => y ≫ S.inclusion) =
        { y : Cocharacter T | y ≫ a.hom = y } := by
  obtain ⟨S, hS, ha, hf⟩ := fixedSplitSubtorus hT a
  let _ := S.isClosedImmersion
  let _ : Mono S.inclusion.hom.hom := Over.mono_of_mono_left _
  let _ : Mono S.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono S.inclusion.hom.hom›
  refine ⟨S, hS, ha, fun _ _ h => (cancel_mono S.inclusion).mp h, ?_⟩
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    change (c ≫ S.inclusion) ≫ a.hom = c ≫ S.inclusion
    rw [Category.assoc, ha]
  · exact hf (multiplicativeGroup_isSplitTorus K) y


open private splitTorus_hom_descends groupBaseChange_map_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.SplitToriConjugacy

set_option backward.isDefEq.respectTransparency false in
/-- Extension of coefficients on cocharacters is bijective for split tori. -/
theorem splitCocharactersBaseChange {F K : Type u} [Field F] [Field K] [Algebra F K]
    {S : GroupScheme F} (hS : IsSplitTorus S)
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters))) :
    Function.Bijective (fun y : Cocharacter S =>
      e.hom ≫ (groupBaseChange F K).map y) := by
  constructor
  · exact fun _ _ h => groupBaseChange_map_injective ((cancel_epi e.hom).mp h)
  · intro y
    obtain ⟨x, hx⟩ := splitTorus_hom_descends (K := K) (multiplicativeGroup_isSplitTorus F) hS
      (e.inv ≫ y)
    change (groupBaseChange F K).map x = e.inv ≫ y at hx
    refine ⟨x, ?_⟩
    change e.hom ≫ (groupBaseChange F K).map x = y
    rw [hx, Iso.hom_inv_id_assoc]

open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.BorelProper (IsParabolic)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)
open private limits_subgroups_extend map_limit_parabolic
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.RankOneFlag
open private limitIsParabolic from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private limitParabolic_transport from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.RationalCocharacter

set_option backward.isDefEq.respectTransparency false in
private theorem commutingSubtorusInLimit {F : Type u} [Field F]
    {G : GroupScheme F} (U : ClosedSubgroup G) (S : ClosedSubgroup U.group)
    [IsCommMonObj S.group.X] (c : Cocharacter S.group)
    (J : LimitDecomposition (c ≫ S.inclusion ≫ U.inclusion)) :
    IsSubgroupOf (subgroupOfSubgroup U S) J.parabolic := by
  let A := subgroupOfSubgroup U S
  have hc : Centralizes (c ≫ S.inclusion ≫ U.inclusion) A.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X t s
    let t' : X ⟶ S.group.X := t
    let s' : X ⟶ S.group.X := s ≫ c.hom.hom
    let i := (S.inclusion ≫ U.inclusion).hom.hom
    have h : Commute t' s' := Commute.all _ _
    have hi := h.map (IsMonHom.monoidHom i X)
    change Commute (t' ≫ i) (s' ≫ i) at hi
    change Commute (t' ≫ i) (s ≫ c.hom.hom ≫ i)
    simpa only [s', Category.assoc] using hi
  obtain ⟨p, hp⟩ := (J.centralizer_points A.group.X A.inclusion.hom.hom).mp hc
  obtain ⟨j, hj⟩ := factor_group_through_subgroup J.centralizer A.inclusion p hp
  exact ⟨j ≫ J.sectionMap, by rw [Category.assoc, J.section_in_G, hj]⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
/-- A cocharacter dominant in the conjugated marking defines a ground field
parabolic that contains the split subgroup and the adapted Borel after extension. -/
theorem adaptedBorelInParabolic {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K) (H : AffineAlgebraicGroup F)
    (hH : Specs.GeometricRadicals.IsReductive H)
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val)
    (U : ClosedSubgroup H.val) (S : ClosedSubgroup U.group) [IsCommMonObj S.group.X]
    (uK : (groupBaseChange F K).obj U.group ≅ C.realization.pinned.pair.T.group)
    (hu : uK.hom ≫ C.realization.pinned.pair.T.inclusion ≫ f.hom =
      (groupBaseChange F K).map U.inclusion)
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters)))
    (he : IsUnitComparison F K e)
    (g : 𝟙_ (SchemeOver K) ⟶ C.realization.pinned.pair.G.val.X)
    (a : C.realization.pinned.pair.T.group ≅ C.realization.pinned.pair.T.group)
    (ha : a.hom ≫ C.realization.pinned.pair.T.inclusion =
      C.realization.pinned.pair.T.inclusion ≫ (conjugationIso g).hom)
    (c : Cocharacter S.group)
    (hc : let P := C.realization.pinned.pair
      let _ := C.realization.attached.comm
      let θ := e.hom ≫ (groupBaseChange F K).map c ≫
        (groupBaseChange F K).map S.inclusion ≫ uK.hom ≫ a.hom
      ∀ i, D.base.IsPos i →
        0 ≤ (ApartmentRoots.split D.datum ℚ).root i
          ((1 : ℚ) ⊗ₜ[ℤ] markedCocharacterMap C (𝟙 P.T.group) (Additive.ofMul θ))) :
    let P := C.realization.pinned.pair
    ∃ J : LimitDecomposition (c ≫ S.inclusion ≫ U.inclusion),
      IsParabolic H J.parabolic ∧ IsSubgroupOf (subgroupOfSubgroup U S) J.parabolic ∧
      ∃ bK : P.B.group ⟶ (groupBaseChange F K).obj J.parabolic.group,
        let gb := toUnit P.B.group.X ≫ g
        (bK ≫ (groupBaseChange F K).map J.parabolic.inclusion ≫ f.inv).hom.hom =
          gb⁻¹ * P.B.inclusion.hom.hom * gb := by
  let P := C.realization.pinned.pair
  let B := groupBaseChange F K
  let ν := c ≫ S.inclusion ≫ U.inclusion
  let νK := e.hom ≫ B.map ν
  let θ := e.hom ≫ B.map c ≫ B.map S.inclusion ≫ uK.hom ≫ a.hom
  let I := conjugationIso g
  let transport := I.symm ≪≫ f
  let HK := Specs.Unipotent.baseChangedAlgebraicGroup K H
  obtain ⟨J⟩ := existsLimitDecomposition H ν
  obtain ⟨JK⟩ := existsLimitDecomposition HK νK
  obtain ⟨L⟩ := existsLimitDecomposition P.G (θ ≫ P.T.inclusion)
  have hθ : (θ ≫ P.T.inclusion) ≫ transport.hom = νK := by
    change (θ ≫ P.T.inclusion) ≫ I.inv ≫ f.hom = e.hom ≫ B.map (c ≫ S.inclusion ≫ U.inclusion)
    simp only [θ, Functor.map_comp, Category.assoc]
    rw [reassoc_of% ha, Iso.hom_inv_id_assoc, hu]
  have hmap : ∃ q : L.parabolic.group ⟶ JK.parabolic.group,
      q ≫ JK.parabolic.inclusion = L.parabolic.inclusion ≫ transport.hom := by
    rw [← limitParabolic_transport hθ.symm JK]
    exact map_limit_parabolic P.G.property.1 transport.hom L (hθ.symm ▸ JK)
  obtain ⟨q, hq⟩ := hmap
  obtain ⟨b, hb⟩ := dominantMarkedBorel C θ L hc
  have hJ := (limits_subgroups_extend H J e he JK).1.1
  obtain ⟨p, hp⟩ := hJ
  refine ⟨J, limitIsParabolic H hH ν J, commutingSubtorusInLimit U S c J, b ≫ q ≫ p, ?_⟩
  change p ≫ B.map J.parabolic.inclusion = JK.parabolic.inclusion at hp
  have hfinal : (b ≫ q ≫ p) ≫ B.map J.parabolic.inclusion ≫ f.inv =
      P.B.inclusion ≫ I.inv := by
    simp only [Category.assoc, reassoc_of% hp, reassoc_of% hq, reassoc_of% hb]
    change P.B.inclusion ≫ I.inv ≫ f.hom ≫ f.inv = _
    rw [f.hom_inv_id, Category.comp_id]
  rw [hfinal]
  change P.B.inclusion.hom.hom ≫ conjugation g⁻¹ = _
  rw [comp_conjugation]
  simp only [GrpObj.comp_inv, inv_inv]
  rfl

/-- The integral central map gives an isomorphism on rational
cocharacters of the two marked torus lattices. -/
theorem markedCentralRationalCocharacter_bijective {D E : BasedRootDatum.{u}}
    {M : Model D} {M' : Model E} (c : MarkedCentralCover M M')
    (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) :
    Function.Bijective (c.pushCocharacter.baseChange ℚ) := by
  let _ := D.finiteY
  let _ := E.finiteY
  have inj : Function.Injective (c.pushCocharacter.baseChange ℚ) :=
    Module.Flat.lTensor_preserves_injective_linearMap c.pushCocharacter
      (markedCentralCocharacter_injective c)
  exact ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e.finrank_eq).mp inj⟩

private theorem rationalFixedRange {X Y Z : Type u}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    (m : X →ₗ[ℤ] Y) (q : Y →ₗ[ℤ] Z) (w : Y →ₗ[ℤ] Y) (l : Z ≃ₗ[ℤ] Z)
    (hm : Function.Injective m) (hr : LinearMap.range m = LinearMap.ker (w - LinearMap.id))
    (hq : Function.Bijective (q.baseChange ℚ)) (hw : q.comp w = l.toLinearMap.comp q) :
    Function.Injective (m.baseChange ℚ) ∧
      LinearMap.range ((q.baseChange ℚ).comp (m.baseChange ℚ)) =
        LinearMap.ker ((l.baseChange ℤ ℚ Z Z).toLinearMap - LinearMap.id) := by
  let M := m.baseChange ℚ
  let Q := q.baseChange ℚ
  let W := w.baseChange ℚ
  let L := l.baseChange ℤ ℚ Z Z
  have hex := Module.Flat.lTensor_exact ℚ (LinearMap.exact_iff.mpr hr.symm)
  change Function.Exact M ((w - LinearMap.id).baseChange ℚ) at hex
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_id] at hex
  have hR : LinearMap.range M = LinearMap.ker (W - LinearMap.id) :=
    (LinearMap.exact_iff.mp hex).symm
  have hc : Q.comp W = L.toLinearMap.comp Q := by
    simpa only [Q, W, L, LinearMap.baseChange_comp, LinearEquiv.coe_baseChange] using
      congrArg (LinearMap.baseChange ℚ) hw
  have hcomm (y : ℚ ⊗[ℤ] Y) : Q (W y) = L (Q y) := DFunLike.congr_fun hc y
  refine ⟨Module.Flat.lTensor_preserves_injective_linearMap m hm, ?_⟩
  change LinearMap.range (Q.comp M) = LinearMap.ker (L.toLinearMap - LinearMap.id)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : M y ∈ LinearMap.ker (W - LinearMap.id) := hR ▸ LinearMap.mem_range_self M y
    change W (M y) - M y = 0 at hy
    change L (Q (M y)) - Q (M y) = 0
    rw [← hcomm, sub_eq_zero.mp hy, sub_self]
  · intro hx
    obtain ⟨y, rfl⟩ := hq.2 x
    change L (Q y) - Q y = 0 at hx
    have hy : W y = y := hq.1 ((hcomm y).trans (sub_eq_zero.mp hx))
    have hy' : y ∈ LinearMap.ker (W - LinearMap.id) := sub_eq_zero.mpr hy
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (hR.symm ▸ hy')
    exact ⟨z, congrArg Q hz⟩

private theorem markedCocharacterMap_apply {K : Type u} [Field K] {D : BasedRootDatum.{u}}
    {M : Model D} (C : MarkedFibre M K) {H : GroupScheme K} [IsCommMonObj H.X]
    (s : H ⟶ C.realization.pinned.pair.T.group) (y : Cocharacter H) :
    markedCocharacterMap C s (Additive.ofMul y) =
      C.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ s)) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem markedCocharacterRange {K : Type u} [Field K] {D E : BasedRootDatum.{u}}
    {M : Model D} {M' : Model E} (c : MarkedCentralCover M M')
    (C : MarkedFibre M K) {H : GroupScheme K} [IsCommMonObj H.X]
    (s : H ⟶ C.realization.pinned.pair.T.group)
    (b : C.realization.pinned.pair.T.group ≅ C.realization.pinned.pair.T.group)
    (hi : Function.Injective (fun y : Cocharacter H => y ≫ s))
    (hr : Set.range (fun y : Cocharacter H => y ≫ s) = {y | y ≫ b.hom = y})
    (w : E.Y ≃ₗ[ℤ] E.Y)
    (hw : ∀ y : Cocharacter C.realization.pinned.pair.T.group,
      c.pushCocharacter (C.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ b.hom))) =
        w (c.pushCocharacter (C.realization.datumIso.val.coweightEquiv (Additive.ofMul y))))
    (e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)) :
    Function.Injective ((markedCocharacterMap C s).baseChange ℚ) ∧
      LinearMap.range ((c.pushCocharacter.baseChange ℚ).comp ((markedCocharacterMap C s).baseChange ℚ)) =
        LinearMap.ker ((w.baseChange ℤ ℚ E.Y E.Y).toLinearMap - LinearMap.id) := by
  let _ := C.realization.attached.comm
  let d := C.realization.datumIso.val.coweightEquiv
  let m := markedCocharacterMap C s
  let a := (markedCocharacterMap C b.hom).comp d.symm.toLinearMap
  have ha (y : Cocharacter C.realization.pinned.pair.T.group) :
      a (d (Additive.ofMul y)) = d (Additive.ofMul (y ≫ b.hom)) := by
    rw [show a (d (Additive.ofMul y)) =
      markedCocharacterMap C b.hom (d.symm (d (Additive.ofMul y))) from rfl,
      d.symm_apply_apply]
    rfl
  have hcomm : c.pushCocharacter.comp a = w.toLinearMap.comp c.pushCocharacter := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := d.surjective x
    change c.pushCocharacter (a (d (Additive.ofMul y.toMul))) = w (c.pushCocharacter (d y))
    rw [ha]
    exact hw y.toMul
  have hinj : Function.Injective m := by
    intro x y hxy
    change d (Additive.ofMul (x.toMul ≫ s)) = d (Additive.ofMul (y.toMul ≫ s)) at hxy
    exact Additive.toMul.injective (hi (Additive.ofMul.injective (d.injective hxy)))
  have hR : LinearMap.range m = LinearMap.ker (a - LinearMap.id) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have hy : (y.toMul ≫ s) ≫ b.hom = y.toMul ≫ s :=
        (Set.ext_iff.mp hr _).mp ⟨y.toMul, rfl⟩
      change a (d (Additive.ofMul (y.toMul ≫ s))) - d (Additive.ofMul (y.toMul ≫ s)) = 0
      rw [ha, hy, sub_self]
    · intro hx
      obtain ⟨y, rfl⟩ := d.surjective x
      change a (d (Additive.ofMul y.toMul)) - d (Additive.ofMul y.toMul) = 0 at hx
      rw [ha] at hx
      have hy := Additive.ofMul.injective (d.injective (sub_eq_zero.mp hx))
      obtain ⟨z, hz⟩ := (Set.ext_iff.mp hr y.toMul).mpr hy
      exact ⟨Additive.ofMul z, congrArg (fun t => d (Additive.ofMul t)) hz⟩
  exact rationalFixedRange m c.pushCocharacter a w hinj hR
    (markedCentralRationalCocharacter_bijective c e) hcomm

open private cocharactersOfIso homToDual latticeCoordinates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

set_option backward.isDefEq.respectTransparency false in
private theorem splitCocharacterFinrank {K : Type u} [Field K]
    {S : GroupScheme K} [IsCommMonObj S.X] {r : ℕ}
    (i : S ≅ (StandardGroups.multiplicativePowerGroup K (ULift.{u} (Fin r))).val) :
    Module.finrank ℤ (Additive (Cocharacter S)) = r := by
  let M := StandardLattice.{u} r
  obtain ⟨d⟩ := _root_.LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  obtain ⟨_, e, _, _, _⟩ := _root_.LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing
    (k := K) r
  let L : Additive (Cocharacter S) ≃ₗ[ℤ] Module.Dual ℤ (Additive M) :=
    ((e.trans (cocharactersOfIso (d ≪≫ i.symm))).toAdditive.toIntLinearEquiv).symm.trans (homToDual M)
  let b := (Pi.basisFun ℤ (Fin r)).map (latticeCoordinates.{u} r).symm
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  rw [L.finrank_eq, Module.finrank_eq_card_basis b.dualBasis, Fintype.card_fin]

set_option backward.isDefEq.respectTransparency false in
private theorem splitRankOfRange {F K : Type u} [Field F] [Field K] [Algebra F K]
    {S : GroupScheme F} (hS : IsSplitTorus S) [IsCommMonObj ((groupBaseChange F K).obj S).X]
    {V : Type u} [AddCommGroup V] [Module ℚ V] (I : Submodule ℚ V)
    (m : (ℚ ⊗[ℤ] Additive (Cocharacter ((groupBaseChange F K).obj S))) →ₗ[ℚ] V)
    (hi : Function.Injective m) (hr : LinearMap.range m = I) :
    Nonempty (S ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin (Module.finrank ℚ I)))).val) := by
  obtain ⟨r, ⟨i⟩⟩ := hS
  obtain ⟨j⟩ := splitTorus_baseChange (k := F) K r
  let iK := (groupBaseChange F K).mapIso i ≪≫ j
  obtain ⟨_, _, _, hfree, _, _⟩ := _root_.LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing
    ((groupBaseChange F K).obj S) ⟨r, ⟨iK⟩⟩
  let _ := hfree
  have hdim : Module.finrank ℚ I = r := by
    rw [← hr, m.finrank_range_of_inj hi, Module.finrank_baseChange]
    exact splitCocharacterFinrank iK
  rw [hdim]
  exact ⟨i⟩

set_option backward.isDefEq.respectTransparency false in
private theorem largestMarkedSplitSubtorus {F K : Type u} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] (τ : Gal(K/F)) (hτ : Subgroup.zpowers τ = ⊤)
    (U : AffineAlgebraicGroup F) (A : GroupScheme F) (hA : IsSplitTorus A) (P : GroupScheme K)
    (uK : (groupBaseChange F K).obj U.val ≅ P) (v : P ≅ (groupBaseChange F K).obj A)
    (b : P ≅ P)
    (hv : (uK ≪≫ v).hom.hom.hom.left ≫ coefficientChange τ A ≫ (v.symm ≪≫ b ≪≫ v).hom.hom.hom.left =
      coefficientChange τ U.val ≫ (uK ≪≫ v).hom.hom.hom.left) :
    ∃ S : ClosedSubgroup U.val, IsSplitTorus S.group ∧
      (∀ R : ClosedSubgroup U.val, IsSplitTorus R.group → IsSubgroupOf R S) ∧
      let s := (groupBaseChange F K).map S.inclusion ≫ uK.hom
      Function.Injective (fun y : Cocharacter ((groupBaseChange F K).obj S.group) => y ≫ s) ∧
      Set.range (fun y : Cocharacter ((groupBaseChange F K).obj S.group) => y ≫ s) =
        {y | y ≫ b.hom = y} := by
  obtain ⟨S, hS, hmax, hi, hr⟩ :=
    ExceptionalInnerSplitSubtorus.largestSplitSubtorus F K τ hτ U A hA (uK ≪≫ v) (v.symm ≪≫ b ≪≫ v) hv
  let s := (groupBaseChange F K).map S.inclusion ≫ uK.hom
  have hs (y : Cocharacter ((groupBaseChange F K).obj S.group)) :
      (y ≫ s) ≫ v.hom = y ≫ (groupBaseChange F K).map S.inclusion ≫ (uK ≪≫ v).hom := by
    simp only [s, Iso.trans_hom, Category.assoc]
  have hb (y : Cocharacter P) :
      (y ≫ v.hom) ≫ (v.symm ≪≫ b ≪≫ v).hom = (y ≫ b.hom) ≫ v.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  have hinj : Function.Injective (fun y : Cocharacter ((groupBaseChange F K).obj S.group) => y ≫ s) :=
    fun y z h => hi ((hs y).symm.trans ((congrArg (· ≫ v.hom) h).trans (hs z)))
  refine ⟨S, hS, hmax, hinj, ?_⟩
  change Set.range (fun y : Cocharacter ((groupBaseChange F K).obj S.group) => y ≫ s) = _
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    have hz := (Set.ext_iff.mp hr ((z ≫ s) ≫ v.hom)).mp ⟨z, (hs z).symm⟩
    change ((z ≫ s) ≫ v.hom) ≫ (v.symm ≪≫ b ≪≫ v).hom = (z ≫ s) ≫ v.hom at hz
    rw [hb] at hz
    exact (cancel_mono v.hom).mp hz
  · intro hy
    change y ≫ b.hom = y at hy
    have hy' : (y ≫ v.hom) ≫ (v.symm ≪≫ b ≪≫ v).hom = y ≫ v.hom := by rw [hb, hy]
    obtain ⟨z, hz⟩ := (Set.ext_iff.mp hr (y ≫ v.hom)).mpr hy'
    exact ⟨z, (cancel_mono v.hom).mp ((hs z).trans hz)⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1100000 in
/-- The marked torus descends with the actual coefficient and Weyl actions. -/
private theorem descendMarkedStandardTorus {F K : Type u}
    [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
    {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)} (Y : SplitLevel K c p p' e)
    (G : AffineAlgebraicGroup F) (Q : AdjointQuotient G)
    (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group)
    (hi : Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map)
    (a : PointCocycle (S := K) Q.quotient.val) (T : Twist a)
    (σ : Gal(K/F)) (hσ : Subgroup.zpowers σ = ⊤)
    (n : Y.ad.N)
    (hn : (n : ExceptionalAffineBruhat.FieldPoints M' K) =
      forgetFibrePoint M'.group (CommAlgCat.of F K) (a.val σ ≫ iQ.hom.hom.hom)) :
    let C := Y.sc_fibre
    let P := C.realization.pinned.pair
    letI := C.realization.attached.comm
    let A := (fibre F).obj (splitTorus D)
    ∃ (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj T.group.val)
      (f : P.G.val ≅ (groupBaseChange F K).obj T.group.val)
      (U : ClosedSubgroup T.group.val) (uK : (groupBaseChange F K).obj U.group ≅ P.T.group)
      (v : P.T.group ≅ (groupBaseChange F K).obj A)
      (b : P.T.group ≅ P.T.group) (w : E.Y ≃ₗ[ℤ] E.Y),
      IsInduced F K j T.trivialization ∧ IsMarkedTrivialization C iG j f ∧
      IsMaximalTorus U ∧
      (uK.hom ≫ P.T.inclusion ≫ f.hom = (groupBaseChange F K).map U.inclusion) ∧
      ((uK ≪≫ v).hom.hom.hom.left ≫ coefficientChange σ.symm A ≫
        (v.symm ≪≫ b ≪≫ v).hom.hom.hom.left =
          coefficientChange σ.symm U.group ≫ (uK ≪≫ v).hom.hom.hom.left) ∧
      (Y.ad.affine n).linear = w.baseChange ℤ ℚ E.Y E.Y ∧
      ∀ y : Cocharacter P.T.group,
        c.pushCocharacter (C.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ b.hom))) =
          w (c.pushCocharacter (C.realization.datumIso.val.coweightEquiv (Additive.ofMul y))) := by
  let C := Y.sc_fibre
  let C' := Y.ad_fibre
  let P := C.realization.pinned.pair
  let P' := C'.realization.pinned.pair
  let _ := C.realization.attached.comm
  let _ := C'.realization.attached.comm
  let q := a.val σ
  let qK := (geometricSectionsEquiv K Q.quotient.val).symm q
  obtain ⟨j, hj⟩ := schemeTrivialization T
  obtain ⟨d, hd⟩ := fibreTowerComparison (F := F) (K := K)
  let s := markedReferenceIso d C iG
  let s' := markedReferenceIso d C' iQ
  let m := (fibre F).map M.torus ≫ iG.inv
  let v := markedReferenceTorusIso d C
  let f := s ≪≫ j
  have htf := (markedTrivializationOfTower C iG j d (hd M.group)).1
  change IsMarkedTrivialization C iG j f at htf
  have htq : IsMarkedTrivialization C' iQ (Iso.refl _) s' := by
    simpa only [Iso.trans_refl] using
      (markedTrivializationOfTower C' iQ (Iso.refl _) d (hd M'.group)).1
  have hv : v.hom ≫ (groupBaseChange F K).map m = P.T.inclusion ≫ s.hom := by
    have hs := (markedTrivializationOfTower C iG (Iso.refl _) d (hd M.group)).2
    change P.T.inclusion ≫ (s ≪≫ Iso.refl _).hom =
      v.hom ≫ (groupBaseChange F K).map m ≫ 𝟙 _ at hs
    simpa only [Iso.trans_refl, Category.comp_id] using hs.symm
  let t := qK ≫ s'.inv.hom.hom
  have ht : markedGroundPoint C' t = (n : ExceptionalAffineBruhat.FieldPoints M' K) :=
    (markedSectionComparison C' iQ s' htq q).trans hn.symm
  have htN : markedGroundPoint C' t ∈ Y.ad.N := ht.symm ▸ n.property
  obtain ⟨b', hb'⟩ := (conjugates_iff_iso t P'.T P'.T).mp
    (conjugates_of_normalizes _ ((Y.ad_points.1 t).mp htN))
  obtain ⟨α, hα, hproj⟩ := innerSchemeProjection (inn := T.inner) T.onLift q
  let β := conjugationIso t
  let π := C.groupIso.inv ≫ (fibre K).map c.map ≫ C'.groupIso.hom
  have hπ : s.hom ≫ (groupBaseChange F K).map Q.projection = π ≫ s'.hom :=
    markedProjectionComparison d C C' Q.projection iG iQ c hi
  have hβ : β.hom ≫ s'.hom = s'.hom ≫ (conjugationIso qK).hom := by
    rw [conjugationIso_natural]
    have he : t ≫ s'.hom.hom.hom = qK := by
      change qK ≫ s'.inv.hom.hom ≫ s'.hom.hom.hom = qK
      have hcancel : s'.inv.hom.hom ≫ s'.hom.hom.hom = 𝟙 _ :=
        congrArg (fun g => g.hom.hom) s'.inv_hom_id
      rw [hcancel, Category.comp_id]
    rw [he]
  let α₀ := s ≪≫ α ≪≫ s.symm
  have hcomm : α₀.hom ≫ π = π ≫ β.hom := by
    apply (cancel_mono s'.hom).mp
    change (s.hom ≫ α.hom ≫ s.inv) ≫ π ≫ s'.hom = (π ≫ β.hom) ≫ s'.hom
    rw [Category.assoc π β.hom, hβ, ← Category.assoc π, ← hπ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg (s.hom ≫ ·) hproj
  let πT := C.torusIso.inv ≫ (fibre K).map c.torusMap ≫ C'.torusIso.hom
  obtain ⟨_, hT, Z, hZ, hZT, _⟩ := c.fibre K C C'
  obtain ⟨b, hb⟩ := centralPreimageStable P.T P'.T π πT hT Z hZ hZT α₀ β b' hcomm hb'
  let U₀ := pushSubgroup s P.T
  have hb₀ : b.hom ≫ U₀.inclusion = U₀.inclusion ≫ α.hom := by
    change b.hom ≫ P.T.inclusion ≫ s.hom = (P.T.inclusion ≫ s.hom) ≫ α.hom
    rw [← Category.assoc, hb]
    simp only [Category.assoc]
    change P.T.inclusion ≫ s.hom ≫ α.hom ≫ s.inv ≫ s.hom = _
    rw [s.inv_hom_id, Category.comp_id]
  obtain ⟨U, uK, hU, hUK, hcoeff⟩ := descendTorusThroughTwist T σ hσ j hj α hα
    ((fibre F).obj (splitTorus D)) m U₀ P.split v hv b hb₀
  have hUcomp : uK.hom ≫ P.T.inclusion ≫ f.hom = (groupBaseChange F K).map U.inclusion := by
    change uK.hom ≫ P.T.inclusion ≫ (s.hom ≫ j.hom) = _
    change uK.hom ≫ (P.T.inclusion ≫ s.hom) ≫ j.hom = _ at hUK
    simpa only [Category.assoc] using hUK
  obtain ⟨w, hw, haction⟩ := markedAdjointCocharacterAction Y n t ht b' hb'
  have hbπ : b.hom ≫ πT = πT ≫ b'.hom := by
    let _ := P'.T.isClosedImmersion
    let _ : Mono P'.T.inclusion.hom.hom := Over.mono_of_mono_left _
    let _ : Mono P'.T.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono P'.T.inclusion.hom.hom›
    apply (cancel_mono P'.T.inclusion).mp
    have hπT : πT ≫ P'.T.inclusion = P.T.inclusion ≫ π := hT.1
    simp only [Category.assoc, hπT, reassoc_of% hb, hcomm, hb', reassoc_of% hπT, β]
  refine ⟨j, f, U, uK, v, b, w, hj, htf, maximalTorusOfComparison U hU P.T P.maximal f uK hUcomp,
    hUcomp, hcoeff, hw, ?_⟩
  intro y
  have hy : (y ≫ b.hom) ≫ πT = (y ≫ πT) ≫ b'.hom := by
    simp only [Category.assoc, hbπ]
  rw [← markedCentralCocharacter c C C' (y ≫ b.hom),
    ← markedCentralCocharacter c C C' y]
  change C'.realization.datumIso.val.coweightEquiv (Additive.ofMul ((y ≫ b.hom) ≫ πT)) =
    w (C'.realization.datumIso.val.coweightEquiv (Additive.ofMul (y ≫ πT)))
  rw [hy]
  exact haction (y ≫ πT)

open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (absoluteRoots)
open Specs.GeometricRadicals (IsReductive)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)

set_option backward.isDefEq.respectTransparency false in
private theorem markedMinimalParabolic {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M K)
    (H : AffineAlgebraicGroup F) (hH : IsReductive H)
    (S : ClosedSubgroup H.val) (hS : IsMaximalSplitTorus S)
    (c : Cocharacter S.group) (J : LimitDecomposition (c ≫ S.inclusion))
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val)
    [IsCommMonObj ((groupBaseChange F K).obj S.group).X]
    (s : (groupBaseChange F K).obj S.group ⟶ C.realization.pinned.pair.T.group)
    (hs : s ≫ C.realization.pinned.pair.T.inclusion ≫ f.hom =
      (groupBaseChange F K).map S.inclusion)
    (e : specGroup (groupAlgebra K IntegerCharacters) ≅
      (groupBaseChange F K).obj (specGroup (groupAlgebra F IntegerCharacters)))
    (he : IsUnitComparison F K e)
    (hc : ∀ i, (ApartmentRoots.split D.datum ℚ).root i
        ((1 : ℚ) ⊗ₜ[ℤ] markedCocharacterMap C s (Additive.ofMul
          (e.hom ≫ (groupBaseChange F K).map c))) = 0 →
      (s ≫ markedCharacter C i).hom.hom = 1) :
    IsMinimalParabolic H J.parabolic := by
  let P := C.realization.pinned.pair
  let d := C.realization.datumIso.val
  let _ := C.realization.attached.comm
  apply Relative.GenericCocharacterMinimalParabolic.genericCocharacterMinimality H hH S hS c J
    P.G P.reductive P.T P.split P.maximal f s hs e he
  intro χ hχ hpair
  let α : Root P.T := ⟨χ, hχ⟩
  obtain ⟨i, hi⟩ := d.indexEquiv.surjective α
  have hmark : markedCharacter C i = χ := by
    have h₁ : d.weightEquiv (D.datum.root i) = C.realization.attached.datum.rootDatum.root (d.indexEquiv i) :=
      d.toHom.root_weightMap_apply _ _ _
    have h₂ := C.realization.attached.datum.root_eq α
    exact congrArg Additive.toMul ((h₁.trans (congrArg _ hi)).trans h₂)
  rw [← hmark] at hpair ⊢
  apply Grp.hom_ext
  apply hc i
  change RootData.extendFunctional ℚ (D.datum.root' i)
    ((1 : ℚ) ⊗ₜ[ℤ] markedCocharacterMap C s (Additive.ofMul
        (e.hom ≫ (groupBaseChange F K).map c))) = 0
  rw [RootData.extendFunctional_one_tmul, markedCocharacterMap_apply]
  have h := latticeCharacterPairing C (D.datum.root i) ((e.hom ≫ (groupBaseChange F K).map c) ≫ s)
  change D.datum.root' i (C.realization.datumIso.val.coweightEquiv (Additive.ofMul
    ((e.hom ≫ (groupBaseChange F K).map c) ≫ s))) =
      pairing P.T.group (markedCharacter C i) ((e.hom ≫ (groupBaseChange F K).map c) ≫ s) at h
  have hz : pairing P.T.group (markedCharacter C i) ((e.hom ≫ (groupBaseChange F K).map c) ≫ s) = 0 := by
    rw [Category.assoc]
    exact hpair
  simpa only [Int.cast_zero] using congrArg (fun z : ℤ => (z : ℚ)) (h.trans hz)

open Specs.ExceptionalInnerStandardTorusDescent (DescendedStandardTorus StandardTorusAndParabolic)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
/-- The actual Frobenius normalizer value determines the descended marked torus,
its largest split subtorus, and the adapted parabolic of a generic cocharacter.
The finite-level input already supplies the length-zero representative. -/
theorem descendedStandardTorus_conditional
    (_normalForm : Specs.ExceptionalStableAlcoves.ExceptionalAlcoveNormalForm.{u})
    (_scalingDenominator : Specs.ExceptionalStableAlcoves.IntegralScalingDenominator.{u})
    (_stableAlcoves : Specs.ExceptionalStableAlcoves.StableIncidentAlcoves.{u}) :
    DescendedStandardTorus.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ _unram D E M M' c degree b b' _ _ _ _ _ p p' e Y _ _
    G Q iG iQ hi a T σ hσ t ht
  let n : Y.ad.N := ⟨t, (Subgroup.mem_map.mp ht).choose_spec.2 ▸
    (Subgroup.mem_map.mp ht).choose.property⟩
  obtain ⟨j, f, U, uK, v, β, w, hj, hf, hU, hu, hcoeff, hL, haction⟩ :=
    descendMarkedStandardTorus Y G Q iG iQ hi a T σ hσ.1 n rfl
  let C := Y.sc_fibre
  let P := C.realization.pinned.pair
  let B := groupBaseChange F K
  let A := (fibre F).obj (splitTorus D)
  obtain ⟨CF⟩ := ExceptionalMarkedRootDescent.markedFibreExists M F
  obtain ⟨rA, ⟨iA⟩⟩ := CF.realization.pinned.pair.split
  have hA : IsSplitTorus A := ⟨rA, ⟨CF.torusIso ≪≫ iA⟩⟩
  obtain ⟨S, hS, hSmax, hs_inj, hs_range⟩ := largestMarkedSplitSubtorus σ.symm
    (Subgroup.zpowers_inv.trans hσ.1) (closedSubgroupAlgebraicGroup U) A hA P.T.group
    uK v β hcoeff
  have hSK : IsSplitTorus (B.obj S.group) := by
    obtain ⟨r, ⟨i⟩⟩ := hS
    obtain ⟨iK⟩ := splitTorus_baseChange (k := F) K r
    exact ⟨r, ⟨B.mapIso i ≪≫ iK⟩⟩
  obtain ⟨hScomm, _⟩ := _root_.LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing
    S.group hS
  obtain ⟨hSKcomm, _⟩ := _root_.LinearAlgebraicGroups.RootData.CharacterPairing.perfectCharacterPairing
    (B.obj S.group) hSK
  let _ := hScomm
  let _ := hSKcomm
  let _ := C.realization.attached.comm
  let sK := B.map S.inclusion ≫ uK.hom
  let V := (markedCocharacterMap C sK).baseChange ℚ
  let fixed := LinearMap.ker ((Y.ad.affine n).linear.toLinearMap - LinearMap.id)
  obtain ⟨hVinj, hVrange⟩ := markedCocharacterRange c C sK β hs_inj hs_range w haction e
  have hfixed : LinearMap.range ((c.pushCocharacter.baseChange ℚ).comp V) = fixed := by
    change _ = LinearMap.ker ((Y.ad.affine n).linear.toLinearMap - LinearMap.id)
    rw [hL]
    exact hVrange
  have hrank := splitRankOfRange hS fixed ((c.pushCocharacter.baseChange ℚ).comp V)
    ((markedCentralRationalCocharacter_bijective c e).1.comp hVinj) hfixed
  obtain ⟨e₀, he₀⟩ := unitComparison F K
  refine ⟨j, f, hj, hf, ?_⟩
  change StandardTorusAndParabolic c C f Y.sc.N (Y.ad.affine n).linear
  refine ⟨U, S, uK, hU, hu, hSmax, hrank, e₀, hSKcomm, he₀,
    splitCocharactersBaseChange hS e₀, hVinj, hfixed, ?_⟩
  intro g hg
  obtain ⟨d, hd⟩ := markedNormalizerConjugation Y g hg
  have hconj : d.hom ≫ P.T.inclusion = P.T.inclusion ≫ (conjugationIso g).hom := by
    apply Grp.hom_ext
    change (d.hom ≫ P.T.inclusion).hom.hom = P.T.inclusion.hom.hom ≫ conjugation g
    rw [comp_conjugation]
    exact hd
  let s := sK ≫ d.hom
  have hroot (i : D.I) := markedRootRestriction C hSK s i
  refine ⟨d, hd, hroot, ?_⟩
  intro cochar
  dsimp only
  intro hdom hgeneric
  let cocharK : Cocharacter (B.obj S.group) := e₀.hom ≫ B.map cochar
  let θ : Cocharacter P.T.group := e₀.hom ≫ B.map cochar ≫ B.map S.inclusion ≫ uK.hom ≫ d.hom
  have hθ : markedCocharacterMap C (𝟙 P.T.group) (Additive.ofMul θ) =
      markedCocharacterMap C s (Additive.ofMul cocharK) := by
    let k := C.realization.datumIso.val.coweightEquiv
    change k (Additive.ofMul (θ ≫ 𝟙 P.T.group)) = k (Additive.ofMul (cocharK ≫ s))
    simp only [Category.comp_id, θ, cocharK, s, sK, Category.assoc]
  have hdom' : ∀ i, D.base.IsPos i → 0 ≤ (ApartmentRoots.split D.datum ℚ).root i
      ((1 : ℚ) ⊗ₜ[ℤ] markedCocharacterMap C (𝟙 P.T.group) (Additive.ofMul θ)) := by
    intro i hi
    rw [hθ]
    exact hdom i hi
  obtain ⟨J, hJ, hSJ, bK, hbK⟩ := adaptedBorelInParabolic C T.group T.reductive
    f U S uK hu e₀ he₀ g d hconj cochar hdom'
  refine ⟨J, hJ, hSJ, ?_, bK, hbK⟩
  intro hmax
  let f' := (conjugationIso g).symm ≪≫ f
  have hs : s ≫ P.T.inclusion ≫ f'.hom = B.map (subgroupOfSubgroup U S).inclusion := by
    change s ≫ P.T.inclusion ≫ (conjugationIso g).inv ≫ f.hom = B.map (S.inclusion ≫ U.inclusion)
    simp only [s, sK, Category.assoc, Functor.map_comp, reassoc_of% hconj, Iso.hom_inv_id_assoc]
    exact congrArg (B.map S.inclusion ≫ ·) hu
  let _ : IsCommMonObj ((groupBaseChange F K).obj (subgroupOfSubgroup U S).group).X := hSKcomm
  exact markedMinimalParabolic C T.group T.reductive (subgroupOfSubgroup U S) hmax cochar J
    f' s hs e₀ he₀ (fun i hi => (hroot i).mpr (hgeneric i hi))

end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent

universe v8_closure_7f1ce73085811759_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalInnerStandardTorusDescent».«descendedStandardTorus» : _root_.«LinearAlgebraicGroups».«Specs».«ExceptionalInnerStandardTorusDescent».«DescendedStandardTorus».{v8_closure_7f1ce73085811759_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalInnerStandardTorusDescent».«descendedStandardTorus_conditional».{v8_closure_7f1ce73085811759_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«exceptionalAlcoveNormalForm».{v8_closure_7f1ce73085811759_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«integralScalingDenominator».{v8_closure_7f1ce73085811759_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalStableAlcoves».«stableIncidentAlcoves».{v8_closure_7f1ce73085811759_u0})
