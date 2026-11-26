import Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding
import LinearAlgebraicGroups.Flag.SmoothOrbit
import LinearAlgebraicGroups.Flag.RightQuotientSheaf
import LinearAlgebraicGroups.Affine.ChevalleyLine
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.QuotientEmbedding

open _root_.LinearAlgebraicGroups.Specs
open Specs.QuotientEmbedding (Presentation IsQuasiProjective)
open Specs.ProjectiveSpaces (projectiveSpace LineFamily changeLineSubmodule)
open Specs.PluckerEmbedding (matrixTransport)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private normalizedLine normalizedLine_span extendVector_tmul
  from LinearAlgebraicGroups.Flag.ProjectiveSpaces

open private matrixTransport_apply_basis from LinearAlgebraicGroups.Flag.PluckerEmbedding

variable {k : Type u} [Field k] {G M : GroupScheme k}

private def coordinateLine {I : Type u} [Fintype I] [DecidableEq I]
    (b : Module.Basis I k (I → k)) (i : I) :
    LineFamily k (I → k) (𝟙_ (SchemeOver k)) where
  line R _ := (normalizedLine k b i R ⟨1 ⊗ₜ[k] b i, by
    simp⟩).val
  compatible := by
    intro R T a p
    simp only [normalizedLine_span]
    change Submodule.span T {1 ⊗ₜ[k] b i} =
      changeLineSubmodule k (I → k) a (Submodule.span R {1 ⊗ₜ[k] b i})
    rw [ProjectiveSpaces.changeLineSubmodule_span, Set.image_singleton, extendVector_tmul, map_one]

private theorem coordinateLine_stabilizer {I : Type u} [Fintype I] [DecidableEq I]
    (b : Module.Basis I k (I → k)) (i : I) (R : TestAlgebra k)
    (g : Matrix.GeneralLinearGroup I R) :
    let L := (coordinateLine b i).line R (toUnit _)
    L.submodule.map (matrixTransport b R g).toLinearMap = L.submodule ↔
      StabilizesCoordinateLine g i := by
  let B := b.baseChange R
  simp only [coordinateLine, normalizedLine_span]
  rw [← Module.Basis.baseChange_apply]
  change (Submodule.span R {B i}).map (matrixTransport b R g).toLinearMap =
    Submodule.span R {B i} ↔ _
  let e := B.equivFun
  have hb (j : I) : e (B j) = Pi.single j 1 := by
    ext s
    simp [e, Pi.single_apply, eq_comm]
  have hcomm : e.toLinearMap.comp (matrixTransport b R g).toLinearMap =
      (Matrix.toLin' g.val).comp e.toLinearMap := by
    apply B.ext
    intro j
    change e (matrixTransport b R g (B j)) = Matrix.toLin' g.val (e (B j))
    rw [matrixTransport_apply_basis, map_sum, hb, Matrix.toLin'_apply, Matrix.mulVec_single_one]
    change (∑ l, e (g.val l j • B l)) = _
    simp only [map_smul, hb]
    ext s
    simp [Pi.single_apply, mul_ite]
  rw [← (Submodule.map_injective_of_injective e.injective).eq_iff,
    ← Submodule.map_comp, hcomm, Submodule.map_comp, Submodule.map_span, Set.image_singleton]
  change (Submodule.span R {e (B i)}).map _ = Submodule.span R {e (B i)} ↔ _
  rw [hb]
  rfl

private theorem subgroupSections_of_affine {A B : ClosedSubgroup G} (hG : IsAffine G.X.left)
    (h : ∀ (R : TestAlgebra k) (g : Points G.X R),
      g ∈ SubgroupSections A ((testSpec k).obj (op R)) ↔
      g ∈ SubgroupSections B ((testSpec k).obj (op R))) :
    ∀ (T : SchemeOver k) (g : T ⟶ G.X), g ∈ SubgroupSections A T ↔ g ∈ SubgroupSections B T := by
  letI := hG
  haveI := A.isClosedImmersion
  haveI := B.isClosedImmersion
  have ha : IsAffine A.group.X.left := isAffine_of_isAffineHom A.inclusion.hom.hom.left
  have hb : IsAffine B.group.X.left := isAffine_of_isAffineHom B.inclusion.hom.hom.left
  obtain ⟨R, ⟨e⟩⟩ := essImage_algSpec.mpr ha
  obtain ⟨S, ⟨d⟩⟩ := essImage_algSpec.mpr hb
  obtain ⟨a, ha⟩ := (h R.unop (e.hom ≫ A.inclusion.hom.hom)).mp ⟨e.hom, rfl⟩
  obtain ⟨b, hb⟩ := (h S.unop (d.hom ≫ B.inclusion.hom.hom)).mpr ⟨d.hom, rfl⟩
  change a ≫ B.inclusion.hom.hom = e.hom ≫ A.inclusion.hom.hom at ha
  change b ≫ A.inclusion.hom.hom = d.hom ≫ B.inclusion.hom.hom at hb
  intro T g
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v ≫ e.inv ≫ a, ?_⟩
    change (v ≫ e.inv ≫ a) ≫ B.inclusion.hom.hom = v ≫ A.inclusion.hom.hom
    simp [ha]
  · rintro ⟨v, rfl⟩
    refine ⟨v ≫ d.inv ≫ b, ?_⟩
    change (v ≫ d.inv ≫ b) ≫ A.inclusion.hom.hom = v ≫ B.inclusion.hom.hom
    simp [hb]

/-- Chevalley's line gives the locally closed projective orbit for a smooth ambient group. -/
theorem smoothQuotientEmbedding : Specs.QuotientEmbedding.SmoothQuotientEmbedding.{u} := by
  classical
  intro k _ G H hs
  obtain ⟨I, _, _, i, M, E, f, hf⟩ := chevalleyLine k G H
  let V := I → k
  let b := Pi.basisFun k I
  let ρ := ProjectiveSpaces.lineRepresentation k V
  let L := coordinateLine b i
  obtain ⟨a, P, haction, hstab⟩ := SmoothOrbit.linearProjectiveOrbit k V I b G M.val E f ρ L hs
  let x := (ρ.points _).symm L
  have hH : RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) := by
    intro T g
    exact (P.representsStabilizer T g).trans
      (subgroupSections_of_affine G.property.1 (B := H) (fun R z ↦
        (hstab R z).trans ((coordinateLine_stabilizer b i R _).trans (hf R z))) T g)
  let j := P.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x
  haveI := P.isOpen
  have hj : IsImmersion j.left := by
    change IsImmersion (P.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap a x).left.imageι)
    infer_instance
  haveI : Mono j := Over.mono_of_mono_left j
  have he : P.projection ≫ j = Specs.SmoothOrbit.orbitMap a x := by
    ext : 1
    change P.projection.left ≫
      (P.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap a x).left.imageι) = _
    rw [← Category.assoc, P.factors, Scheme.Hom.toImage_imageι]
  obtain ⟨e, he⟩ := SmoothOrbit.orbitQuotient k G.val _ _ a x j P.projection H
    inferInstance he P.flat P.surjective P.finitePresentation hH
  let Q : Presentation H :=
    { scheme := P.orbit
      quasiProjective := ⟨V, inferInstance, inferInstance, inferInstance, j, hj⟩
      projection := P.projection
      flat := P.flat
      surjective := P.surjective
      finitePresentation := P.finitePresentation
      quotientIso := e
      quotientProjection := he }
  exact ⟨V, inferInstance, inferInstance, inferInstance, a, x, P, Q, hH, ⟨Iso.refl _, by simp [Q]⟩,
    ⟨I, inferInstance, inferInstance, b, M.val, E, f, ρ, haction⟩⟩

private theorem generalLinear_smooth (k I : Type u) [Field k] [Fintype I] [DecidableEq I] :
    Smooth (StandardGroups.generalLinearGroup k I).val.X.hom := by
  let A := MvPolynomial (I × I) k
  let B := Specs.StandardGroups.GLCoordinates k I
  letI : Algebra.Smooth k A := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away
    (Specs.StandardGroups.genericDeterminant k I)
  letI : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  exact (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

private theorem smooth_of_generalLinearPoints {M : AffineAlgebraicGroup k}
    {I : Type u} [Fintype I] [DecidableEq I]
    (e : (groupPointsFunctor k).obj M.val ≅ Specs.StandardGroups.generalLinearPoints k I) :
    Smooth M.val.X.hom := by
  let L := StandardGroups.generalLinearGroup k I
  let E := e ≪≫ (StandardGroups.generalLinearGroupPointsIso (k := k) («ι» := I)).symm
  let F := groupPointsFunctor k
  let f := (groupHomEquiv M.val L.val M.property.1).symm E.hom
  let g := (groupHomEquiv L.val M.val L.property.1).symm E.inv
  have hf : F.map f = E.hom :=
    (groupHomEquiv M.val L.val M.property.1).apply_symm_apply E.hom
  have hg : F.map g = E.inv :=
    (groupHomEquiv L.val M.val L.property.1).apply_symm_apply E.inv
  have hfg : f ≫ g = 𝟙 _ := by
    apply (groupHomEquiv M.val M.val M.property.1).injective
    change F.map (f ≫ g) = F.map (𝟙 M.val)
    rw [F.map_comp, F.map_id, hf, hg, Iso.hom_inv_id]
  have hgf : g ≫ f = 𝟙 _ := by
    apply (groupHomEquiv L.val L.val L.property.1).injective
    change F.map (g ≫ f) = F.map (𝟙 L.val)
    rw [F.map_comp, F.map_id, hg, hf, Iso.inv_hom_id]
  let i : M.val ≅ L.val := ⟨f, g, hfg, hgf⟩
  haveI : IsIso f.hom.hom.left :=
    (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).mapIso i).isIso_hom
  haveI : Smooth L.val.X.hom := generalLinear_smooth k I
  rw [← Over.w f.hom.hom]
  infer_instance

private theorem representedProjection_apply {G : GroupScheme k} {H : ClosedSubgroup G}
    (Q : Presentation H) {T : SchemeOver k} (g : T ⟶ G.X) :
    Q.quotientIso.hom.hom.app (op T) (projectSection H g) = ULift.up (g ≫ Q.projection) :=
  congrArg (fun m => m.hom.app (op T) (ULift.up g)) Q.quotientProjection

private theorem projection_eq_iff {G : GroupScheme k} {H : ClosedSubgroup G}
    (Q : Presentation H) {T : SchemeOver k} (g h : T ⟶ G.X) :
    g ≫ Q.projection = h ≫ Q.projection ↔ g⁻¹ * h ∈ SubgroupSections H T := by
  change g ≫ Q.projection = h ≫ Q.projection ↔
    ∃ a : T ⟶ H.group.X, a ≫ H.inclusion.hom.hom = g⁻¹ * h
  rw [← rightQuotientProjectionEquality H g h]
  constructor
  · intro he
    apply (ConcreteCategory.bijective_of_isIso (Q.quotientIso.hom.hom.app (op T))).1
    rw [representedProjection_apply, representedProjection_apply, he]
  · intro he
    exact ULift.up.inj ((representedProjection_apply Q g).symm.trans
      ((congrArg (Q.quotientIso.hom.hom.app (op T)) he).trans (representedProjection_apply Q h)))

private theorem locallySurjective_of_fppf {X Y : SchemeOver k} (q : X ⟶ Y)
    [hflat : Flat q.left] [hsurj : Surjective q.left] [hfp : LocallyOfFinitePresentation q.left] :
    Presheaf.IsLocallySurjective (fppfOver k) ((fppfOver k).uliftYoneda.map q).hom := by
  constructor
  intro T z
  let z' : T ⟶ Y := z.down
  let f := pullback.snd q z'
  have hpb := (IsPullback.of_hasPullback q z').map (Over.forget _)
  haveI : Flat f.left := MorphismProperty.of_isPullback (P := @Flat) hpb hflat
  haveI : Surjective f.left := MorphismProperty.of_isPullback (P := @Surjective) hpb hsurj
  haveI : LocallyOfFinitePresentation f.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb hfp
  apply (fppfOver k).superset_covering (S := Sieve.generate (Presieve.singleton f))
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    refine ⟨ULift.up (pullback.fst q z'), ?_⟩
    change ULift.up (pullback.fst q z' ≫ q) = ULift.up (f ≫ z')
    exact congrArg ULift.up pullback.condition
  · rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0},
      ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
    change Sieve.generate (Presieve.ofArrows _ _) ∈ _
    rw [Presieve.ofArrows_pUnit]
    exact Precoverage.generate_mem_toGrothendieck f.left.singleton_mem_fppfPrecoverage

set_option backward.isDefEq.respectTransparency false in
private theorem represent_of_fppf {G : GroupScheme k} (H : ClosedSubgroup G)
    {Y : SchemeOver k} (q : G.X ⟶ Y)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hq : ∀ (T : SchemeOver k) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections H T) :
    ∃ e : rightQuotientSheaf H ≅ schemeFppfSheaf Y,
      rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q := by
  let p : rightCosetPresheaf H ⟶ (schemeFppfSheaf Y).obj :=
    { app T := ↾fun z ↦ Quotient.lift (fun g ↦ ULift.up (g ≫ q))
        (fun g h he ↦ congrArg ULift.up ((hq T.unop g h).2 (QuotientGroup.leftRel_apply.mp he))) z.down
      naturality := by
        intro T U f
        ext ⟨z⟩
        induction z using QuotientGroup.induction_on with
        | H g => exact congrArg ULift.up (Category.assoc f.unop g q) }
  have hp : rightCosetProjection H ≫ p = ((fppfOver k).uliftYoneda.map q).hom := by
    ext T ⟨g⟩
    rfl
  letI := locallySurjective_of_fppf q
  letI : Presheaf.IsLocallySurjective (fppfOver k) p :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hp
  letI : Presheaf.IsLocallyInjective (fppfOver k) p := by
    apply Presheaf.isLocallyInjective_of_injective
    rintro T ⟨a⟩ ⟨b⟩
    induction a using QuotientGroup.induction_on with
    | H g =>
      induction b using QuotientGroup.induction_on with
      | H h =>
        intro he
        exact congrArg ULift.up (QuotientGroup.eq.mpr ((hq T.unop g h).1 (ULift.up.inj he)))
  let φ : rightQuotientSheaf H ⟶ schemeFppfSheaf Y :=
    ⟨sheafifyLift (fppfOver k) p (schemeFppfSheaf Y).property⟩
  have hφ : toSheafify (fppfOver k) (rightCosetPresheaf H) ≫ φ.hom = p :=
    toSheafify_sheafifyLift _ _ _
  haveI : Sheaf.IsLocallySurjective φ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hφ
  haveI : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac (fppfOver k) p hφ
  haveI : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨inferInstance, inferInstance⟩
  refine ⟨asIso φ, ?_⟩
  apply (sheafToPresheaf _ _).map_injective
  change (rightCosetProjection H ≫ toSheafify (fppfOver k) _) ≫ φ.hom = _
  rw [Category.assoc, hφ, hp]
  rfl

private theorem map_projection {A B : ClosedSubgroup M}
    (h : A.group ⟶ B.group) (comm : A.inclusion ≫ 𝟙 M = h ≫ B.inclusion)
    (P : Presentation A) (Q : Presentation B) :
    ∃ r : P.scheme ⟶ Q.scheme, P.projection ≫ r = Q.projection := by
  let Y := (fppfOver k).uliftYoneda
  let r := Y.preimage (P.quotientIso.inv ≫ rightQuotientMap (𝟙 M) h comm ≫ Q.quotientIso.hom)
  refine ⟨r, Y.map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_preimage, ← P.quotientProjection, Category.assoc,
    Iso.hom_inv_id_assoc, ← Q.quotientProjection]
  apply (sheafToPresheaf _ _).map_injective
  ext T ⟨g⟩
  change Q.quotientIso.hom.hom.app T
      ((rightQuotientMap (𝟙 M) h comm).hom.app T (projectSection A g)) =
    Q.quotientIso.hom.hom.app T (projectSection B g)
  congr 1
  have hid : (𝟙 M : M ⟶ M).hom.hom = 𝟙 M.X := rfl
  simpa only [hid, Category.comp_id] using (rightQuotientMapOnLifts (𝟙 M) h comm g)

private theorem isQuasiProjective_of_immersion {X Y : SchemeOver k} (f : X ⟶ Y)
    (hf : IsImmersion f.left) (hY : IsQuasiProjective Y) : IsQuasiProjective X := by
  obtain ⟨V, _, _, _, j, hj⟩ := hY
  exact ⟨V, inferInstance, inferInstance, inferInstance, f ≫ j, IsImmersion.comp _ _⟩

private theorem basePoint_closed {X : SchemeOver k} (hX : IsQuasiProjective X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) : IsClosedImmersion x.left := by
  obtain ⟨V, _, _, _, j, hj⟩ := hX
  haveI : IsProper (projectiveSpace k V).hom := ProjectiveSpaces.projectiveSpaceProper k V
  haveI : IsSeparated X.hom := by
    rw [← Over.w j]
    infer_instance
  haveI : IsClosedImmersion (x.left ≫ X.hom) := by
    rw [Over.w x]
    change IsClosedImmersion (𝟙 _)
    infer_instance
  exact IsClosedImmersion.of_comp x.left X.hom

/-- The right quotient exists for all finite-type affine groups, including nonsmooth groups. -/
theorem quotientEmbedding : Specs.QuotientEmbedding.RightQuotientRepresentable.{u} := by
  intro k _ G H
  obtain ⟨_, M, ⟨E⟩, f, hf⟩ := faithfulLinearization k G
  have hs := smooth_of_generalLinearPoints E
  haveI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  let A : ClosedSubgroup M.val := ⟨H.group, H.inclusion ≫ f, by
    change IsClosedImmersion (H.inclusion.hom.hom.left ≫ f.hom.hom.left)
    infer_instance⟩
  let B : ClosedSubgroup M.val := ⟨G.val, f, hf⟩
  obtain ⟨_, _, _, _, _, _, _, P, _, _, _⟩ := smoothQuotientEmbedding k M A hs
  obtain ⟨_, _, _, _, _, _, _, Q, _, _, _⟩ := smoothQuotientEmbedding k M B hs
  obtain ⟨r, hr⟩ := map_projection H.inclusion (Category.comp_id A.inclusion) P Q
  let x : (𝟙_ (SchemeOver k)) ⟶ Q.scheme := (1 : (𝟙_ (SchemeOver k)) ⟶ M.val.X) ≫ Q.projection
  let F := pullback r x
  let j : F ⟶ P.scheme := pullback.fst r x
  have hx_closed : IsClosedImmersion x.left := basePoint_closed Q.quasiProjective x
  haveI : IsClosedImmersion j.left := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    ((IsPullback.of_hasPullback r x).flip.map (Over.forget _)) hx_closed
  let f' := f.hom.hom
  haveI : Mono f' := Over.mono_of_mono_left f'
  have hidentity {T : SchemeOver k} (m : T ⟶ M.val.X) :
      m ≫ Q.projection = toUnit T ≫ x ↔ ∃ g : T ⟶ G.val.X, g ≫ f' = m := by
    have h := projection_eq_iff Q (1 : T ⟶ M.val.X) m
    rw [inv_one, one_mul] at h
    have hx : toUnit T ≫ x = (1 : T ⟶ M.val.X) ≫ Q.projection := by
      rw [show x = (1 : (𝟙_ (SchemeOver k)) ⟶ M.val.X) ≫ Q.projection from rfl,
        ← Category.assoc, MonObj.comp_one]
    rw [hx, eq_comm]
    exact h
  have hc : (f' ≫ P.projection) ≫ r = toUnit G.val.X ≫ x := by
    rw [Category.assoc, hr]
    exact (hidentity f').2 ⟨𝟙 _, Category.id_comp _⟩
  let q : G.val.X ⟶ F := pullback.lift _ _ hc
  have hq : q ≫ j = f' ≫ P.projection := pullback.lift_fst _ _ _
  have hp : IsPullback f' q P.projection j := by
    refine IsPullback.mk' hq.symm (fun _ _ _ h _ ↦ (cancel_mono f').mp h) ?_
    intro T m z hz
    have hm : m ≫ Q.projection = toUnit T ≫ x := by
      rw [← hr, ← Category.assoc, hz, Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (fun h : T ⟶ (𝟙_ (SchemeOver k)) ↦ h ≫ x) (Subsingleton.elim _ _)
    obtain ⟨g, hg⟩ := (hidentity m).mp hm
    refine ⟨g, hg, (IsPullback.of_hasPullback r x).hom_ext ?_ ?_⟩
    · change (g ≫ q) ≫ j = z ≫ j
      rw [Category.assoc, hq, ← Category.assoc, hg, hz]
    · exact Subsingleton.elim _ _
  have hp' := hp.map (Over.forget _)
  haveI : Flat q.left := MorphismProperty.of_isPullback (P := @Flat) hp' P.flat
  haveI : Surjective q.left := MorphismProperty.of_isPullback (P := @Surjective) hp' P.surjective
  haveI : LocallyOfFinitePresentation q.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hp' P.finitePresentation
  haveI : Mono j := Over.mono_of_mono_left j
  obtain ⟨e, he⟩ := represent_of_fppf H q (by
    intro T g h
    rw [← cancel_mono j, Category.assoc, Category.assoc, hq, ← Category.assoc, ← Category.assoc,
      projection_eq_iff P]
    let φ := ((yonedaGrp.map f).app (op T)).hom
    change (φ g)⁻¹ * φ h ∈ SubgroupSections A T ↔ g⁻¹ * h ∈ SubgroupSections H T
    rw [← map_inv, ← map_mul]
    change (∃ a : T ⟶ H.group.X, a ≫ H.inclusion.hom.hom ≫ f' = (g⁻¹ * h) ≫ f') ↔
      ∃ a : T ⟶ H.group.X, a ≫ H.inclusion.hom.hom = g⁻¹ * h
    simp only [← Category.assoc, cancel_mono])
  exact ⟨{
    scheme := F
    quasiProjective := isQuasiProjective_of_immersion j inferInstance P.quasiProjective
    projection := q
    flat := inferInstance
    surjective := inferInstance
    finitePresentation := inferInstance
    quotientIso := e
    quotientProjection := he }⟩

end

end LinearAlgebraicGroups.QuotientEmbedding
