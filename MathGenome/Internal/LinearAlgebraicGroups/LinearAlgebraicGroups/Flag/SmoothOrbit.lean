import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SmoothOrbit
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GenericFreeness
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.Integral
import MathGenome.Internal.AlgebraCore.P103.Ch06.AffineDimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.SmoothOrbit

open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.SmoothOrbit

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : GroupScheme k} {X O : SchemeOver k}

private theorem orbitMap_comp (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    {T : SchemeOver k} (g : T ⟶ G.X) :
    letI := a
    g ≫ orbitMap a x = g • (toUnit T ≫ x) := by
  letI := a
  change g ≫ lift (𝟙 G.X) (toUnit G.X ≫ x) ≫ a.smul =
    lift g (toUnit T ≫ x) ≫ a.smul
  rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]

private theorem same_orbit_lift_iff (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (i : O ⟶ X) [Mono i] (q : G.X ⟶ O) (hq : q ≫ i = orbitMap a x)
    (H : ClosedSubgroup G)
    (hH : RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g))
    {T : SchemeOver k} (g h : T ⟶ G.X) :
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ SubgroupSections H T := by
  letI := a
  have eg : g ≫ q ≫ i = g • (toUnit T ≫ x) := by rw [hq, orbitMap_comp]
  have eh : h ≫ q ≫ i = h • (toUnit T ≫ x) := by rw [hq, orbitMap_comp]
  have heq : (g ≫ q = h ≫ q) ↔ g • (toUnit T ≫ x) = h • (toUnit T ≫ x) := by
    rw [← cancel_mono i, Category.assoc, Category.assoc, eg, eh]
  have hfix : (g⁻¹ * h ∈ SubgroupSections H T) ↔
      (g⁻¹ * h) • (toUnit T ≫ x) = toUnit T ≫ x := (hH T (g⁻¹ * h)).symm
  rw [heq, hfix, mul_smul]
  constructor
  · intro e
    rw [← e, inv_smul_smul]
  · intro e
    have ee := congrArg (g • ·) e
    rw [smul_inv_smul] at ee
    exact ee.symm

private def orbitCosetMap (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (i : O ⟶ X) [Mono i] (q : G.X ⟶ O) (hq : q ≫ i = orbitMap a x)
    (H : ClosedSubgroup G)
    (hH : RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g)) :
    rightCosetPresheaf H ⟶ (schemeFppfSheaf O).obj where
  app T := ↾fun t ↦ Quotient.lift (fun g ↦ ULift.up (g ≫ q))
    (fun g h he ↦ congrArg ULift.up
      ((same_orbit_lift_iff a x i q hq H hH g h).2 (QuotientGroup.leftRel_apply.mp he))) t.down
  naturality T U f := by
    ext ⟨g⟩
    induction g using QuotientGroup.induction_on with
    | H g =>
      change ULift.up ((f.unop ≫ g) ≫ q) = ULift.up (f.unop ≫ g ≫ q)
      rw [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A surjective flat presentation identifies the orbit with the right fppf quotient. -/
theorem orbitQuotient : Specs.SmoothOrbit.OrbitQuotient.{u} := by
  intro k _ G X O a x i q H mi hq hflat hsurj hfp hH
  letI : Mono i := mi
  letI : Flat q.left := hflat
  letI : Surjective q.left := hsurj
  letI : LocallyOfFinitePresentation q.left := hfp
  let p := orbitCosetMap a x i q hq H hH
  let F : SchemeOver k ⥤ Scheme := Over.forget _
  have hp : rightCosetProjection H ≫ p = ((fppfOver k).uliftYoneda.map q).hom := by
    ext T ⟨g⟩
    rfl
  have hlocal : Presheaf.IsLocallySurjective (fppfOver k)
      ((fppfOver k).uliftYoneda.map q).hom := by
    constructor
    intro T z
    let z' : T ⟶ O := z.down
    let f := pullback.snd q z'
    have hpb := (IsPullback.of_hasPullback q z').map F
    haveI : Flat f.left := MorphismProperty.of_isPullback (P := @Flat) hpb hflat
    haveI : Surjective f.left :=
      MorphismProperty.of_isPullback (P := @Surjective) hpb hsurj
    haveI : LocallyOfFinitePresentation f.left :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb hfp
    apply (fppfOver k).superset_covering (S := Sieve.generate (Presieve.singleton f))
    · rw [Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      refine ⟨⟨pullback.fst q z'⟩, ?_⟩
      change ULift.up (pullback.fst q z' ≫ q) = ULift.up (f ≫ z')
      exact congrArg ULift.up pullback.condition
    · rw [GrothendieckTopology.mem_over_iff, ← Presieve.ofArrows_pUnit.{0},
        ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
      change Sieve.generate (Presieve.ofArrows _ _) ∈ _
      rw [Presieve.ofArrows_pUnit]
      exact Precoverage.generate_mem_toGrothendieck f.left.singleton_mem_fppfPrecoverage
  letI := hlocal
  letI : Presheaf.IsLocallySurjective (fppfOver k) p :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hp
  letI : Presheaf.IsLocallyInjective (fppfOver k) p := by
    refine Presheaf.isLocallyInjective_of_injective _ p ?_
    intro T y z
    rcases y with ⟨y⟩
    rcases z with ⟨z⟩
    induction y using QuotientGroup.induction_on with
    | H g =>
      induction z using QuotientGroup.induction_on with
      | H h =>
        intro e
        apply congrArg ULift.up
        apply Quotient.sound
        exact QuotientGroup.leftRel_apply.mpr
          ((same_orbit_lift_iff a x i q hq H hH g h).1 (ULift.up.inj e))
  let φ : rightQuotientSheaf H ⟶ schemeFppfSheaf O :=
    ⟨sheafifyLift (fppfOver k) p (schemeFppfSheaf O).property⟩
  have hφ : toSheafify (fppfOver k) (rightCosetPresheaf H) ≫ φ.hom = p :=
    toSheafify_sheafifyLift _ _ _
  haveI : Sheaf.IsLocallySurjective φ :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac (fppfOver k) hφ
  haveI : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac (fppfOver k) p hφ
  haveI : IsIso φ := (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨inferInstance, inferInstance⟩
  refine ⟨asIso φ, ?_⟩
  apply (sheafToPresheaf _ _).map_injective
  change (rightCosetProjection H ≫ toSheafify _ _) ≫ φ.hom =
    ((fppfOver k).uliftYoneda.map q).hom
  rw [Category.assoc, hφ, hp]

section GenericFreeness

variable {X Y : Scheme.{u}}

private theorem affine_generic_fppf {A B : CommRingCat.{u}} [IsDomain A]
    (f : A ⟶ B) (hf : f.hom.FiniteType) (hinj : Function.Injective f.hom) :
    ∃ (r : A), r ≠ 0 ∧ Flat (Spec.map f ∣_ PrimeSpectrum.basicOpen r) ∧
      Surjective (Spec.map f ∣_ PrimeSpectrum.basicOpen r) := by
  letI : Algebra A B := f.hom.toAlgebra
  haveI : Algebra.FiniteType A B := hf
  obtain ⟨r, hr, J, hJ, ⟨b⟩⟩ := LinearAlgebraicGroups.genericFreeness_of_injective hinj
  refine ⟨r, hr, ?_⟩
  letI : Algebra (Localization.Away r) (Localization.Away (f.hom r)) :=
    localizationAlgebra (Submonoid.powers r) B
  letI : Nonempty J := hJ
  have hff : (Localization.awayMap f.hom r).FaithfullyFlat := by
    change (algebraMap (Localization.Away r) (Localization.Away (f.hom r))).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr
  have h := (flat_and_surjective_SpecMap_iff
    (f := CommRingCat.ofHom (Localization.awayMap f.hom r))).mpr hff
  exact ⟨(MorphismProperty.arrow_mk_iso_iff (P := @Flat) (SpecMapRestrictBasicOpenIso f r)).mpr h.1,
    (MorphismProperty.arrow_mk_iso_iff (P := @Surjective) (SpecMapRestrictBasicOpenIso f r)).mpr h.2⟩

private theorem exists_integral_affine_open (Y : Scheme.{u}) [Nonempty Y] [IsReduced Y]
    [IsNoetherian Y] : ∃ U : Y.Opens, IsAffineOpen U ∧ IsIntegral U.toScheme := by
  let y₀ : Y := Nonempty.some inferInstance
  let Z := irreducibleComponent y₀
  have hZ : Z ∈ irreducibleComponents Y := irreducibleComponent_mem_irreducibleComponents y₀
  obtain ⟨s, hs, ⟨y, hy⟩, hsZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUs⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy hs
  refine ⟨U, hU, ?_⟩
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  refine ⟨?_, inferInstance⟩
  rw [irreducibleSpace_def]
  let j := Scheme.Opens.ι (X := Y) U
  have e : j ⁻¹' Z = Set.univ :=
    Set.eq_univ_of_forall fun z : U ↦ hsZ (hUs z.property)
  change IsIrreducible (Set.univ : Set U)
  rw [← e]
  exact hZ.1.preimage j.isOpenEmbedding ⟨y, hsZ (hUs hyU), ⟨⟨y, hyU⟩, rfl⟩⟩

private theorem exists_fppf_open (f : X ⟶ Y) [IsAffineHom f] [LocallyOfFiniteType f]
    [IsSchemeTheoreticallyDominant f] [Nonempty Y] [IsReduced Y] [IsNoetherian Y] :
    ∃ (V D : Scheme.{u}) (j : V ⟶ Y) (d : D ⟶ X) (v : D ⟶ V),
      IsOpenImmersion j ∧ Nonempty V ∧ IsPullback d v f j ∧ Flat v ∧ Surjective v := by
  obtain ⟨U, hU, hUi⟩ := exists_integral_affine_open Y
  let fU := f ∣_ U
  haveI : IsAffine U.toScheme := hU
  haveI : IsIntegral U.toScheme := hUi
  haveI : IsAffine (f ⁻¹ᵁ U).toScheme := IsAffineHom.isAffine_preimage U hU
  have hpb := (isPullback_morphismRestrict f U).flip
  haveI : IsSchemeTheoreticallyDominant fU :=
    IsSchemeTheoreticallyDominant.of_isPullback hpb
  let s := fU.appTop
  have hst : s.hom.FiniteType := HasRingHomProperty.appTop (P := @LocallyOfFiniteType) fU
    inferInstance
  have hsi : Function.Injective s.hom := fU.app_injective ⊤
  obtain ⟨r, hr, hflat, hsurj⟩ := affine_generic_fppf s hst hsi
  let V : (Spec Γ(U.toScheme, ⊤)).Opens := PrimeSpectrum.basicOpen r
  let D := Spec.map s ⁻¹ᵁ V
  let eX := (f ⁻¹ᵁ U).toScheme.isoSpec
  let eY := U.toScheme.isoSpec
  let d := D.ι ≫ eX.inv
  let j := V.ι ≫ eY.inv
  have hlocal : IsPullback d (Spec.map s ∣_ V) fU j := by
    apply (isPullback_morphismRestrict (Spec.map s) V).flip.of_iso'
      (Iso.refl _) eX (Iso.refl _) eY
    · simp [d, D]
    · simp
    · exact Scheme.isoSpec_hom_naturality fU
    · simp [j]
  have hVe : Nonempty V :=
    ⟨⟨⟨⊥, Ideal.isPrime_bot⟩, (PrimeSpectrum.mem_basicOpen _ _).2 (by simpa using hr)⟩⟩
  exact ⟨V, D, j ≫ U.ι, d ≫ (f ⁻¹ᵁ U).ι, Spec.map s ∣_ V,
    inferInstance, hVe, hlocal.paste_horiz hpb, hflat, hsurj⟩

end GenericFreeness

private theorem isPullback_tensor_snd {A B C : SchemeOver k} (f : B ⟶ C) :
    IsPullback (𝟙 A ⊗ₘ f) (snd A B) (snd A C) f := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun c ↦ lift (c.fst ≫ fst A C) c.snd) ?_ (by simp) ?_)
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using c.condition.symm
  · intro c m h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using congrArg (fun t ↦ t ≫ fst A C) h₁
    · simpa using h₂

private theorem isPullback_tensor_structure (A B : SchemeOver k) :
    IsPullback (fst A B).left (snd A B).left A.hom B.hom := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk (fst A B).left (snd A B).left
    ((Over.w (fst A B)).trans (Over.w (snd A B)).symm))
  refine PullbackCone.IsLimit.mk ((Over.w (fst A B)).trans (Over.w (snd A B)).symm)
    (fun c ↦ (lift (Over.homMk c.fst : Over.mk (c.fst ≫ A.hom) ⟶ A)
      (Over.homMk c.snd c.condition.symm : Over.mk (c.fst ≫ A.hom) ⟶ B)).left)
    ?_ ?_ ?_
  · intro c
    exact congrArg Over.Hom.left (lift_fst
      (Over.homMk c.fst : Over.mk (c.fst ≫ A.hom) ⟶ A)
      (Over.homMk c.snd c.condition.symm : Over.mk (c.fst ≫ A.hom) ⟶ B))
  · intro c
    exact congrArg Over.Hom.left (lift_snd
      (Over.homMk c.fst : Over.mk (c.fst ≫ A.hom) ⟶ A)
      (Over.homMk c.snd c.condition.symm : Over.mk (c.fst ≫ A.hom) ⟶ B))
  · intro c m hm₁ hm₂
    have h : m ≫ (A ⊗ B).hom = c.fst ≫ A.hom := by
      rw [← Over.w (fst A B), ← Category.assoc, hm₁]
    apply congrArg Over.Hom.left (show
      (Over.homMk m h : Over.mk (c.fst ≫ A.hom) ⟶ A ⊗ B) = _ from ?_)
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      simpa using hm₁
    · apply Over.OverMorphism.ext
      simpa using hm₂

private def actionTwist (A : ModObj G.X X) : G.X ⊗ X ≅ G.X ⊗ X := by
  letI := A
  let g := fst G.X X
  let p := snd G.X X
  refine ⟨lift g (g • p), lift g (g⁻¹ • p), ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · simp [g]
    · simp only [Category.assoc, lift_snd, Category.id_comp, ModObj.comp_smul,
        GrpObj.comp_inv, lift_fst, g, p, inv_smul_smul]
  · apply CartesianMonoidalCategory.hom_ext
    · simp [g]
    · simp only [Category.assoc, lift_snd, Category.id_comp, ModObj.comp_smul,
        lift_fst, g, p, smul_inv_smul]

private theorem smooth_action (A : ModObj G.X X) [Smooth G.X.hom] : Smooth A.smul.left := by
  let e := actionTwist A
  haveI : Smooth (snd G.X X).left :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_tensor_structure G.X X) inferInstance
  have he : e.hom ≫ snd G.X X = A.smul := by
    letI := A
    dsimp [e, actionTwist]
    simp [Hom.smul_def]
  have he' : e.hom.left ≫ (snd G.X X).left = A.smul.left := congrArg Over.Hom.left he
  rw [← he']
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  infer_instance

private theorem mono_over {Y Z : SchemeOver k} (j : Y ⟶ Z) [Mono j.left] : Mono j :=
  (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))

private theorem toImage_dominant {Y Z : Scheme.{u}} (f : Y ⟶ Z) [QuasiCompact f] :
    IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    ← RingHom.injective_iff_ker_eq_bot]
  exact TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (F := f.image.sheaf) f.toImage.c U.1 (fun y _ ↦ f.stalkFunctor_toImage_injective y)

private abbrev restrictAction {Y : SchemeOver k} (i : Y ⟶ X) [Mono i]
    (a : ModObj G.X X) (b : G.X ⊗ Y ⟶ Y)
    (hb : b ≫ i = (𝟙 G.X ⊗ₘ i) ≫ a.smul) : ModObj G.X Y := by
  letI := a
  have map_b {T : SchemeOver k} (g : T ⟶ G.X) (y : T ⟶ Y) :
      (lift g y ≫ b) ≫ i = g • (y ≫ i) := by
    simp [Category.assoc, hb, Hom.smul_def]
  refine ⟨b, ?_, ?_⟩
  · rw [← cancel_mono i]
    have e : η[G.X] ▷ Y = lift (1 : 𝟙_ (SchemeOver k) ⊗ Y ⟶ G.X) (snd _ _) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, lift_fst, Hom.one_def]
        rw [toUnit_unique (fst (𝟙_ (SchemeOver k)) Y) (toUnit _)]
      · simp
    change (η[G.X] ▷ Y ≫ b) ≫ i = (λ_ Y).hom ≫ i
    rw [e, map_b, one_smul, leftUnitor_hom]
  · rw [← cancel_mono i]
    let T := (G.X ⊗ G.X) ⊗ Y
    let g : T ⟶ G.X := fst (G.X ⊗ G.X) Y ≫ fst G.X G.X
    let h : T ⟶ G.X := fst (G.X ⊗ G.X) Y ≫ snd G.X G.X
    let y : T ⟶ Y := snd (G.X ⊗ G.X) Y
    have el : μ[G.X] ▷ Y = lift (g * h) y := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [g, h, Hom.mul_def, lift_comp_fst_snd]
      · simp [y]
    have er : (α_ G.X G.X Y).hom ≫ G.X ◁ b = lift g (lift h y ≫ b) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [g]
      · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
        have ee : (α_ G.X G.X Y).hom ≫ snd G.X (G.X ⊗ Y) = lift h y := by
          apply CartesianMonoidalCategory.hom_ext
          · simp [h]
          · simp [y]
        rw [← Category.assoc, ee]
    change (μ[G.X] ▷ Y ≫ b) ≫ i = (((α_ G.X G.X Y).hom ≫ G.X ◁ b) ≫ b) ≫ i
    rw [el, er, map_b, map_b, map_b, mul_smul]

private def toClosure (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    G.X ⟶ orbitClosure a x :=
  Over.homMk (orbitMap a x).left.toImage (by
    change (orbitMap a x).left.toImage ≫ ((orbitMap a x).left.imageι ≫ X.hom) = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, Over.w])

private theorem toClosure_fac (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X) :
    toClosure a x ≫ closureInclusion a x = orbitMap a x := by
  apply Over.OverMorphism.ext
  exact (orbitMap a x).left.toImage_imageι

private theorem orbitClosure_action (a : ModObj G.X X) (x : 𝟙_ (SchemeOver k) ⟶ X)
    [QuasiCompact (orbitMap a x).left] [Flat G.X.hom] :
    ∃ b : ModObj G.X (orbitClosure a x),
      μ[G.X] ≫ toClosure a x = (𝟙 G.X ⊗ₘ toClosure a x) ≫ b.smul ∧
        b.smul ≫ closureInclusion a x = (𝟙 G.X ⊗ₘ closureInclusion a x) ≫ a.smul := by
  letI := a
  let f := orbitMap a x
  let Z := orbitClosure a x
  let j := closureInclusion a x
  let q := toClosure a x
  haveI : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion f.left.imageι)
  haveI : Mono j := mono_over j
  have hqj : q ≫ j = f := toClosure_fac a x
  have hflat : Flat (snd G.X Z).left :=
    MorphismProperty.of_isPullback (P := @Flat) (isPullback_tensor_structure G.X Z) inferInstance
  haveI : IsSchemeTheoreticallyDominant q.left := toImage_dominant f.left
  haveI : QuasiCompact q.left := inferInstanceAs (QuasiCompact f.left.toImage)
  have hpb : IsPullback (snd G.X G.X).left (𝟙 G.X ⊗ₘ q).left q.left (snd G.X Z).left :=
    ((isPullback_tensor_snd q).map (Over.forget _)).flip
  haveI : Flat (snd G.X Z).left := hflat
  have hh : IsSchemeTheoreticallyDominant (𝟙 G.X ⊗ₘ q).left :=
    IsSchemeTheoreticallyDominant.of_isPullback hpb
  have he : μ[G.X] ≫ f = (𝟙 G.X ⊗ₘ f) ≫ a.smul := by
    let g := fst G.X G.X
    let h := snd G.X G.X
    have hm : μ[G.X] = g * h := by rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hm, orbitMap_comp, mul_smul, ← orbitMap_comp, Hom.smul_def]
    simp only [← lift_fst_comp_snd_comp (𝟙 G.X) f, Category.comp_id, g, h, f]
    rfl
  let b' : G.X ⊗ Z ⟶ X := (𝟙 G.X ⊗ₘ j) ≫ a.smul
  have hcomp : (𝟙 G.X ⊗ₘ q) ≫ b' = (μ[G.X] ≫ q) ≫ j := by
    change (𝟙 G.X ⊗ₘ q) ≫ (𝟙 G.X ⊗ₘ j) ≫ a.smul = _
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, hqj, ← he, Category.assoc, hqj]
  have hker : j.left.ker ≤ b'.left.ker := by
    have h := (μ[G.X] ≫ q).left.le_ker_comp j.left
    rw [← Over.comp_left, ← hcomp, Over.comp_left, Scheme.Hom.ker_comp,
      hh.ker_eq_bot, Scheme.IdealSheafData.map_bot] at h
    exact h
  let b : G.X ⊗ Z ⟶ Z := Over.homMk (IsClosedImmersion.lift j.left b'.left hker) (by
    change _ ≫ (j.left ≫ X.hom) = _
    rw [← Category.assoc, IsClosedImmersion.lift_fac, Over.w])
  have hb : b ≫ j = b' := by
    apply Over.OverMorphism.ext
    exact IsClosedImmersion.lift_fac _ _ _
  refine ⟨restrictAction j a b hb, ?_, hb⟩
  change μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ b
  exact (cancel_mono j).mp (hcomp.symm.trans (Category.assoc ..).symm |>.trans
    (congrArg ((𝟙 G.X ⊗ₘ q) ≫ ·) hb.symm) |>.trans (Category.assoc ..).symm)

private theorem translate_pullback {Z D V : SchemeOver k}
    (b : ModObj G.X Z) (q : G.X ⟶ Z)
    (hq : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ b.smul)
    (d : D ⟶ G.X) (j : V ⟶ Z) (v : D ⟶ V) (h : IsPullback d v q j) :
    IsPullback (lift (fst G.X D) (snd G.X D ≫ d) ≫ μ[G.X]) (𝟙 G.X ⊗ₘ v)
      q ((𝟙 G.X ⊗ₘ j) ≫ b.smul) := by
  letI := b
  have eqv {T : SchemeOver k} (g r : T ⟶ G.X) :
      (g * r) ≫ q = g • (r ≫ q) := by
    rw [Hom.mul_def, Category.assoc, hq, ← Category.assoc, lift_map, Category.comp_id]
    rfl
  let S := G.X ⊗ D
  let a₁ := fst G.X D
  let a₂ := snd G.X D
  let m : S ⟶ G.X := lift a₁ (a₂ ≫ d) ≫ μ[G.X]
  let w : S ⟶ G.X ⊗ V := 𝟙 G.X ⊗ₘ v
  let t : G.X ⊗ V ⟶ Z := (𝟙 G.X ⊗ₘ j) ≫ b.smul
  have hm {T : SchemeOver k} (l : T ⟶ S) :
      l ≫ m = (l ≫ a₁) * ((l ≫ a₂) ≫ d) := by
    simp only [m, comp_lift_assoc, Hom.mul_def, Category.assoc]
  have hw {T : SchemeOver k} (l : T ⟶ S) :
      l ≫ w = lift (l ≫ a₁) ((l ≫ a₂) ≫ v) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [w, a₁]
    · simp [w, a₂]
  have ht {T : SchemeOver k} (p : T ⟶ G.X ⊗ V) :
      p ≫ t = (p ≫ fst G.X V) • ((p ≫ snd G.X V) ≫ j) := by
    change p ≫ (𝟙 G.X ⊗ₘ j) ≫ b.smul = _
    conv_lhs => rw [← lift_comp_fst_snd p, lift_map_assoc, Category.comp_id]
    rfl
  change IsPullback m w q t
  refine IsPullback.mk' ?_ ?_ ?_
  · have e₁ : m = a₁ * (a₂ ≫ d) := rfl
    have e₂ : w ≫ fst G.X V = a₁ := by simp [w, a₁]
    have e₃ : w ≫ snd G.X V = a₂ ≫ v := by simp [w, a₂]
    rw [e₁, eqv, ht, e₂, e₃, Category.assoc, Category.assoc, h.w]
  · intro T l l' h₁ h₂
    rw [hw, hw] at h₂
    have eg : l ≫ a₁ = l' ≫ a₁ := by
      simpa using congrArg (fun e : T ⟶ G.X ⊗ V ↦ e ≫ fst G.X V) h₂
    have ev : (l ≫ a₂) ≫ v = (l' ≫ a₂) ≫ v := by
      simpa using congrArg (fun e : T ⟶ G.X ⊗ V ↦ e ≫ snd G.X V) h₂
    rw [hm, hm, eg] at h₁
    exact CartesianMonoidalCategory.hom_ext l l' eg (h.hom_ext (mul_left_cancel h₁) ev)
  · intro T r p hp
    let g := p ≫ fst G.X V
    let z := p ≫ snd G.X V
    have hp' : r ≫ q = g • (z ≫ j) := hp.trans (ht p)
    have hpb : (g⁻¹ * r) ≫ q = z ≫ j := by
      rw [eqv, hp', inv_smul_smul]
    let s := h.lift (g⁻¹ * r) z hpb
    refine ⟨lift g s, ?_, ?_⟩
    · rw [hm, lift_fst, lift_snd, h.lift_fst _ _ hpb, mul_inv_cancel_left]
    · rw [hw, lift_fst, lift_snd, h.lift_snd _ _ hpb]
      exact lift_comp_fst_snd p

/-- If a translate lies in the orbit, its second coordinate lies in the orbit as well. -/
private theorem snd_mem_orbit_range {Z : SchemeOver k} (b : ModObj G.X Z) (q : G.X ⟶ Z)
    (hq : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ b.smul)
    (z : (G.X ⊗ Z).left) (hz : b.smul.left z ∈ Set.range q.left) :
    (snd G.X Z).left z ∈ Set.range q.left := by
  let F : SchemeOver k ⥤ Scheme := Over.forget _
  have hp : IsPullback μ[G.X].left (𝟙 G.X ⊗ₘ q).left q.left b.smul.left := by
    have h := translate_pullback b q hq (𝟙 G.X) (𝟙 Z) q (IsPullback.of_id_fst (f := q))
    simp only [Category.comp_id, lift_fst_snd, MonoidalCategory.id_tensorHom_id,
      Category.id_comp] at h
    exact h.map F
  obtain ⟨g, hg⟩ := hz
  obtain ⟨p, _, hpz⟩ := Scheme.exists_preimage_of_isPullback hp g z hg
  refine ⟨(snd G.X G.X).left p, ?_⟩
  have h := congrArg Over.Hom.left (tensorHom_snd (𝟙 G.X) q)
  simpa only [Over.comp_left, Scheme.Hom.comp_apply, hpz] using
    (congrArg (fun f : (G.X ⊗ G.X).left ⟶ Z.left ↦ f p) h).symm

private def rightTranslateProduct {D : SchemeOver k} (d : D ⟶ G.X) :
    G.X ⊗ D ≅ G.X ⊗ D := by
  let g := fst G.X D
  let y := snd G.X D
  refine ⟨lift (g * (y ≫ d)) y, lift (g * (y ≫ d)⁻¹) y, ?_, ?_⟩
  all_goals
    apply CartesianMonoidalCategory.hom_ext
    · simp [g, y, MonObj.comp_mul, GrpObj.comp_inv]
    · simp [y]

private theorem mul_right_surjective {D : SchemeOver k} [Nonempty D.left]
    (d : D ⟶ G.X) :
    Surjective (lift (fst G.X D) (snd G.X D ≫ d) ≫ μ[G.X]).left := by
  let e := rightTranslateProduct d
  have he : e.hom ≫ fst G.X D =
      lift (fst G.X D) (snd G.X D ≫ d) ≫ μ[G.X] := by
    simp [e, rightTranslateProduct, Hom.mul_def]
  rw [← he, Over.comp_left]
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hD : Surjective D.hom :=
    ⟨fun p ↦ ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  haveI : Surjective (fst G.X D).left :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_tensor_structure G.X D).flip hD
  infer_instance

private instance flat_descendsAlong :
    MorphismProperty.DescendsAlong (@Flat : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply HasRingHomProperty.descendsAlong_flat
  refine RingHom.CodescendsAlong.mk _ RingHom.Flat.respectsIso ?_
  intro R S T _ _ _ _ _ hf h
  rw [RingHom.flat_algebraMap_iff] at h ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hf
  exact Module.Flat.of_flat_tensorProduct R T S

private theorem open_fppf_orbit {Z D V : SchemeOver k} [Smooth G.X.hom]
    (b : ModObj G.X Z) (q : G.X ⟶ Z)
    (hq : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ b.smul)
    (d : D ⟶ G.X) (j : V ⟶ Z) (v : D ⟶ V) (h : IsPullback d v q j)
    [IsOpenImmersion j.left] [Nonempty V.left] [Flat v.left] [Surjective v.left]
    [LocallyOfFiniteType q.left] [IsLocallyNoetherian Z.left] :
    ∃ (W : Z.left.Opens) (r : G.X.left ⟶ W.toScheme),
      r ≫ W.ι = q.left ∧ Surjective r ∧ Flat r ∧ LocallyOfFinitePresentation r := by
  let F : SchemeOver k ⥤ Scheme := Over.forget _
  let t : G.X ⊗ V ⟶ Z := (𝟙 G.X ⊗ₘ j) ≫ b.smul
  let s : G.X ⊗ D ⟶ G.X := lift (fst G.X D) (snd G.X D ≫ d) ≫ μ[G.X]
  let w : G.X ⊗ D ⟶ G.X ⊗ V := 𝟙 G.X ⊗ₘ v
  have hp : IsPullback s.left w.left q.left t.left :=
    (translate_pullback b q hq d j v h).map F
  haveI : IsOpenImmersion (𝟙 G.X ⊗ₘ j).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (((isPullback_tensor_snd j).map F).flip) (show IsOpenImmersion j.left from inferInstance)
  haveI : Smooth b.smul.left := smooth_action b
  haveI : Smooth t.left := by
    change Smooth ((𝟙 G.X ⊗ₘ j).left ≫ b.smul.left)
    infer_instance
  haveI : Nonempty D.left := (v.left.surjective.nonempty)
  haveI : Surjective s.left := mul_right_surjective d
  haveI : Surjective w.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (((isPullback_tensor_snd v).map F).flip) (show Surjective v.left from inferInstance)
  have hwflat : Flat w.left :=
    MorphismProperty.of_isPullback (P := @Flat)
      (((isPullback_tensor_snd v).map F).flip) (show Flat v.left from inferInstance)
  have hrange : Set.range q.left = Set.range t.left := by
    have hr := congrArg (fun m : (G.X ⊗ D).left ⟶ Z.left ↦ Set.range m) hp.w
    simpa [Scheme.Hom.comp_apply, Set.range_comp, Set.range_eq_univ.mpr s.left.surjective,
      Set.range_eq_univ.mpr w.left.surjective] using hr
  let W : Z.left.Opens := ⟨Set.range t.left, t.left.isOpenMap.isOpen_range⟩
  have hrq : Set.range q.left = Set.range W.ι := hrange.trans W.range_ι.symm
  let r := IsOpenImmersion.lift W.ι q.left hrq.le
  let t' := IsOpenImmersion.lift W.ι t.left W.range_ι.ge
  have hrf : r ≫ W.ι = q.left := IsOpenImmersion.lift_fac _ _ _
  have htf : t' ≫ W.ι = t.left := IsOpenImmersion.lift_fac _ _ _
  haveI : Surjective r := ⟨fun z ↦ by
    obtain ⟨g, hg⟩ := hrq.ge ⟨z, rfl⟩
    exact ⟨g, W.ι.isOpenEmbedding.injective (by simpa [← Scheme.Hom.comp_apply, hrf] using hg)⟩⟩
  haveI : Surjective t' := ⟨fun z ↦ by
    obtain ⟨g, hg⟩ := z.property
    exact ⟨g, W.ι.isOpenEmbedding.injective (by simpa [← Scheme.Hom.comp_apply, htf] using hg)⟩⟩
  haveI : LocallyOfFiniteType (r ≫ W.ι) := by rw [hrf]; infer_instance
  haveI : LocallyOfFiniteType r := locallyOfFiniteType_of_comp r W.ι
  haveI : LocallyOfFiniteType (t' ≫ W.ι) := by rw [htf]; infer_instance
  haveI : LocallyOfFiniteType t' := locallyOfFiniteType_of_comp t' W.ι
  haveI : Flat t' := by
    apply MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 _) (g := W.ι)
        (show CommSq (𝟙 _) t' t.left W.ι from ⟨by simpa using htf.symm⟩))
    infer_instance
  have hp' : IsPullback s.left w.left r t' := by
    refine IsPullback.mk' ?_ (fun {_ _ _} h₁ h₂ ↦ hp.hom_ext h₁ h₂) ?_
    · rw [← cancel_mono W.ι, Category.assoc, Category.assoc, htf, hrf, hp.w]
    · intro T a c h'
      have hh : a ≫ q.left = c ≫ t.left := by
        simpa only [Category.assoc, hrf, htf] using congrArg (· ≫ W.ι) h'
      exact ⟨hp.lift a c hh, hp.lift_fst .., hp.lift_snd ..⟩
  have hflat : Flat r :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hp'.flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hwflat
  exact ⟨W, r, hrf, inferInstance, hflat, inferInstance⟩

private theorem restrict_to_open_orbit {Z : SchemeOver k} (b : ModObj G.X Z)
    (i : O ⟶ Z) (p : G.X ⟶ O) [IsOpenImmersion i.left] [Surjective p.left]
    (h : μ[G.X] ≫ (p ≫ i) = (𝟙 G.X ⊗ₘ (p ≫ i)) ≫ b.smul) :
    ∃ c : ModObj G.X O,
      c.smul ≫ i = (𝟙 G.X ⊗ₘ i) ≫ b.smul ∧
      μ[G.X] ≫ p = (𝟙 G.X ⊗ₘ p) ≫ c.smul := by
  let r := (𝟙 G.X ⊗ₘ i) ≫ b.smul
  let w : G.X ⊗ G.X ⟶ G.X ⊗ O := 𝟙 G.X ⊗ₘ p
  have hw : Surjective w.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (((isPullback_tensor_snd p).map (Over.forget _)).flip)
      (show Surjective p.left from inferInstance)
  have hw' : w ≫ r = μ[G.X] ≫ p ≫ i := by
    change (𝟙 G.X ⊗ₘ p) ≫ (𝟙 G.X ⊗ₘ i) ≫ b.smul = _
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, ← h]
  have hr : Set.range r.left ⊆ Set.range i.left := by
    rintro y ⟨x, rfl⟩
    obtain ⟨x', hx'⟩ := hw.1 x
    refine ⟨p.left (μ[G.X].left x'), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, ← hw',
        Over.comp_left, Scheme.Hom.comp_apply, hx']
  let m : G.X ⊗ O ⟶ O := Over.homMk (IsOpenImmersion.lift i.left r.left hr) (by
    rw [← Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])
  have hm : m ≫ i = r := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  haveI : Mono i := mono_over i
  refine ⟨restrictAction i b m hm, hm, (cancel_mono i).mp ?_⟩
  change (μ[G.X] ≫ p) ≫ i = ((𝟙 G.X ⊗ₘ p) ≫ m) ≫ i
  rw [Category.assoc, Category.assoc, hm, hw']
/-- The orbit of a rational point is an open subscheme of its schematic closure. -/
theorem schemeOrbit : Specs.SmoothOrbit.SchemeOrbit.{u} := by
  intro k _ G X a x hsm hsep hft hqc
  letI : IsAffine G.1.X.left := G.2.1
  letI : Smooth G.1.X.hom := hsm
  letI : IsSeparated X.hom := hsep
  letI : LocallyOfFiniteType X.hom := hft
  letI : QuasiCompact X.hom := hqc
  let f := orbitMap a x
  let Z := orbitClosure a x
  let q := toClosure a x
  let j := closureInclusion a x
  haveI : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion f.left.imageι)
  haveI : Mono j := mono_over j
  haveI : IsAffineHom (f.left ≫ X.hom) := by rw [Over.w]; infer_instance
  haveI : IsAffineHom f.left := IsAffineHom.of_comp f.left X.hom
  haveI : QuasiCompact (orbitMap a x).left := inferInstanceAs (QuasiCompact f.left)
  haveI : GeometricallyReduced G.1.X.hom :=
    ((affineGroupSmoothnessCriteria k G).1).mp hsm
  haveI : IsReduced G.1.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.1.X.hom
  haveI : QuasiCompact q.left := inferInstanceAs (QuasiCompact f.left.toImage)
  haveI : IsSchemeTheoreticallyDominant q.left := toImage_dominant f.left
  haveI : IsReduced Z.left := IsSchemeTheoreticallyDominant.isReduced q.left
  haveI : Nonempty Z.left :=
    ⟨q.left (η[G.1.X].left (IsLocalRing.closedPoint k))⟩
  haveI : IsSeparated Z.hom := inferInstanceAs (IsSeparated (j.left ≫ X.hom))
  haveI : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (j.left ≫ X.hom))
  haveI : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType (j.left ≫ X.hom))
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  haveI : CompactSpace Z.left := (quasiCompact_iff_compactSpace Z.hom).mp inferInstance
  haveI : IsNoetherian Z.left := {}
  haveI : IsAffineHom (q.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  haveI : IsAffineHom q.left := IsAffineHom.of_comp q.left Z.hom
  haveI : LocallyOfFiniteType (q.left ≫ Z.hom) := by rw [Over.w]; exact G.2.2.1
  haveI : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left Z.hom
  obtain ⟨b, hb, hjb⟩ := orbitClosure_action a x
  obtain ⟨V, D, jV, d, v, hjV, hV, hp, hv, hs⟩ := exists_fppf_open q.left
  let VO : SchemeOver k := Over.mk (jV ≫ Z.hom)
  let DO : SchemeOver k := Over.mk (d ≫ G.1.X.hom)
  let jo : VO ⟶ Z := Over.homMk jV
  let do' : DO ⟶ G.1.X := Over.homMk d
  let vo : DO ⟶ VO := Over.homMk v (by
    change v ≫ (jV ≫ Z.hom) = d ≫ G.1.X.hom
    rw [← Category.assoc, ← hp.w, Category.assoc, Over.w])
  have hpOver : IsPullback do' vo q jo :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext hp.w) hp
  haveI : IsOpenImmersion jo.left := hjV
  haveI : Nonempty VO.left := hV
  haveI : Flat vo.left := hv
  haveI : Surjective vo.left := hs
  obtain ⟨W, r, hW, hsurj, hflat, hfp⟩ := open_fppf_orbit b q hb do' jo vo hpOver
  let O : SchemeOver k := Over.mk (W.ι ≫ Z.hom)
  let inc : O ⟶ Z := Over.homMk W.ι
  let p : G.1.X ⟶ O := Over.homMk r (by
    change r ≫ (W.ι ≫ Z.hom) = _
    rw [← Category.assoc, hW, Over.w])
  have hfac : p ≫ inc = q := Over.OverMorphism.ext hW
  haveI : Mono inc := mono_over inc
  obtain ⟨H, hH⟩ := stabilizerScheme k G.1 X a x hsep hft hqc
  obtain ⟨e, he⟩ := orbitQuotient k G.1 X O a x (inc ≫ j) p H
    inferInstance (by rw [← Category.assoc, hfac, toClosure_fac]) hflat hsurj hfp hH
  haveI : IsOpenImmersion inc.left := inferInstanceAs (IsOpenImmersion W.ι)
  haveI : Surjective p.left := hsurj
  haveI : IsSeparated O.hom := inferInstanceAs (IsSeparated (inc.left ≫ Z.hom))
  haveI : IsAffineHom (p.left ≫ O.hom) := by rw [Over.w]; infer_instance
  have hAffine : IsAffineHom p.left := IsAffineHom.of_comp p.left O.hom
  obtain ⟨c, hc, hcp⟩ := restrict_to_open_orbit b inc p (by rw [hfac]; exact hb)
  have hcj : c.smul ≫ (inc ≫ j) = (𝟙 G.1.X ⊗ₘ (inc ≫ j)) ≫ a.smul := by
    rw [← Category.assoc, hc, Category.assoc, hjb, ← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp]
  exact ⟨⟨O, inc, inferInstance, p, hW, hflat, hsurj, hfp, H, hH, e, he, hAffine, c, hcj, hcp⟩⟩

section Projective

open Specs.ProjectiveSpaces

open private projectiveActionOfLinearRepresentation from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
open private matrixPointEndHom matrixPoint_natural matrixTransport_natural
  lineRepresentation_affine_ext from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.PluckerEmbedding

private abbrev modObjOfSchemeAction (s : Specs.PluckerEmbedding.SchemeAction G X) : ModObj G.X X where
  smul := s.act
  one_smul := by
    have h : η[G.X] ▷ X =
        snd (𝟙_ (SchemeOver k)) X ≫ lift (toUnit X ≫ η[G.X]) (𝟙 X) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [whiskerRight_fst, Category.assoc, lift_fst]
        rw [comp_toUnit_assoc, toUnit_unique (fst (𝟙_ (SchemeOver k)) X) (toUnit _)]
      · simp
    change η[G.X] ▷ X ≫ s.act = (λ_ X).hom
    rw [h, Category.assoc, s.unit, Category.comp_id, leftUnitor_hom]
  mul_smul := by
    let g := fst G.X (G.X ⊗ X)
    let h := snd G.X (G.X ⊗ X) ≫ fst G.X X
    let p := snd G.X (G.X ⊗ X) ≫ snd G.X X
    let α := (α_ G.X G.X X).hom
    have hleft : α ≫ lift (lift g h ≫ μ[G.X]) p = μ[G.X] ▷ X := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [whiskerRight_fst, Category.assoc, lift_fst, comp_lift_assoc]
        simp only [α, g, h, associator_hom_fst, associator_hom_snd_fst,
          lift_comp_fst_snd]
      · simp [α, p]
    have hright : lift g (snd G.X (G.X ⊗ X) ≫ s.act) = G.X ◁ s.act := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [g]
    simp only [g, h, p] at hleft hright
    have e := congrArg (α ≫ ·) s.assoc
    rw [← Category.assoc, hleft, hright] at e
    change μ[G.X] ▷ X ≫ s.act = (α_ G.X G.X X).hom ≫ G.X ◁ s.act ≫ s.act
    simpa only [Category.assoc] using e

private abbrev restrictGroupAction {M : GroupScheme k} (f : G ⟶ M) (a : ModObj M.X X) :
    ModObj G.X X :=
  letI := a
  Mod.scalarRestriction f.hom.hom X

@[simp]
private theorem restrictGroupAction_smul {M : GroupScheme k} (f : G ⟶ M) (a : ModObj M.X X) :
    (restrictGroupAction f a).smul = (f.hom.hom ⊗ₘ 𝟙 X) ≫ a.smul := by
  change f.hom.hom ▷ X ≫ a.smul = _
  rw [tensorHom_def, whiskerLeft_id, Category.comp_id]

private theorem orbitMap_equivariant {Y : SchemeOver k}
    (a : ModObj G.X X) (b : ModObj G.X Y)
    (j : X ⟶ Y) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (h : a.smul ≫ j = (𝟙 G.X ⊗ₘ j) ≫ b.smul) :
    orbitMap a x ≫ j = orbitMap b (x ≫ j) := by
  simp only [orbitMap, Category.assoc, h, lift_map_assoc, Category.comp_id]

private theorem orbitSet_equivariant {Y : SchemeOver k}
    (a : ModObj G.X X) (b : ModObj G.X Y)
    (j : X ⟶ Y) (x : 𝟙_ (SchemeOver k) ⟶ X)
    (h : a.smul ≫ j = (𝟙 G.X ⊗ₘ j) ≫ b.smul) :
    orbitSet b (x ≫ j) = j.left '' orbitSet a x := by
  rw [orbitSet, ← orbitMap_equivariant a b j x h, Over.comp_left]
  exact Set.range_comp ⇑j.left ⇑(orbitMap a x).left

private theorem stabilizes_equivariant_iff {Y : SchemeOver k}
    (a : ModObj G.X X) (b : ModObj G.X Y)
    (j : X ⟶ Y) [Mono j] (x : 𝟙_ (SchemeOver k) ⟶ X)
    (h : a.smul ≫ j = (𝟙 G.X ⊗ₘ j) ≫ b.smul) {T : SchemeOver k} (g : T ⟶ G.X) :
    Stabilizes a.smul x g ↔ Stabilizes b.smul (x ≫ j) g := by
  unfold Stabilizes
  rw [← cancel_mono j]
  simp only [Category.assoc, h, lift_map_assoc, Category.comp_id]

/-- Apply the scheme orbit theorem to a line in a finite-dimensional space. -/
theorem projectiveLineOrbit : Specs.SmoothOrbit.ProjectiveLineOrbit.{u} := by
  intro k V _ _ _ _ G ρ a L hs
  haveI : IsProper (Specs.ProjectiveSpaces.projectiveSpace k V).hom :=
    LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k V
  exact schemeOrbit k G _ a ((ρ.points _).symm L) hs inferInstance inferInstance inferInstance

/-- The linear action on the scheme of lines has its usual stabilizer over every test algebra. -/
theorem linearProjectiveOrbit : Specs.SmoothOrbit.LinearProjectiveOrbit.{u} := by
  intro k V I _ _ _ _ _ _ v G M E f ρ L hs
  let act := projectiveActionOfLinearRepresentation ρ
    (fun R g ↦ Specs.PluckerEmbedding.matrixTransport v R (E.hom.app R g))
    (matrixPointEndHom v E) (fun _ _ ↦ rfl) (by
      intro R T b g
      letI : Algebra R T := b.hom.toAlgebra
      letI : IsScalarTower k R T := IsScalarTower.of_algebraMap_eq' (b.hom.comp_algebraMap).symm
      change
        (Specs.PluckerEmbedding.matrixTransport v T (E.hom.app T (mapPoints b g))).toLinearMap.comp _ =
          LinearMap.comp _
            ((Specs.PluckerEmbedding.matrixTransport v R (E.hom.app R g)).toLinearMap.baseChange (↥T))
      rw [matrixPoint_natural E]
      exact matrixTransport_natural v b (E.hom.app R g))
  let a := restrictGroupAction f (modObjOfSchemeAction act.val)
  obtain ⟨P⟩ := projectiveLineOrbit k V G ρ a L hs
  have hact (R : TestAlgebra k) (g : Points G.1.X R) (p : Points (projectiveSpace k V) R) :
      ((ρ.points _ (lift g p ≫ a.smul)).line R (𝟙 _)).submodule =
        ((ρ.points _ p).line R (𝟙 _)).submodule.map
          (Specs.PluckerEmbedding.matrixTransport v R (E.hom.app R (g ≫ f.hom.hom))).toLinearMap := by
    change ((ρ.points _ (lift g p ≫ (restrictGroupAction f (modObjOfSchemeAction act.val)).smul)).line
      R (𝟙 _)).submodule = _
    rw [restrictGroupAction_smul, lift_map_assoc, Category.comp_id]
    exact act.property R (g ≫ f.hom.hom) p
  refine ⟨a, P, hact, ?_⟩
  intro R g
  let x := (ρ.points _).symm L
  let y : Points (projectiveSpace k V) R := toUnit _ ≫ x
  have hy : (ρ.points _ y).line R (𝟙 _) = L.line R (toUnit _) := by
    dsimp [y]
    rw [ρ.naturality, Equiv.apply_symm_apply]
    simp [LineFamily.pullback]
  change (∃ s : Points P.stabilizer.group.X R, s ≫ P.stabilizer.inclusion.hom.hom = g) ↔ _
  rw [← P.representsStabilizer]
  change (lift g y ≫ a.smul = y) ↔ _
  constructor
  · intro h
    have e := hact R g y
    rw [h, hy] at e
    exact e.symm
  · intro h
    apply lineRepresentation_affine_ext ρ
    rw [hact, hy, h]

/-- Transport the projective orbit and its scheme stabilizer through a closed equivariant embedding. -/
theorem equivariantProjectiveOrbit : Specs.SmoothOrbit.EquivariantProjectiveOrbit.{u} := by
  intro k W _ _ _ _ G Y a b j x hs hj he
  let X := Specs.ProjectiveSpaces.projectiveSpace k W
  haveI : IsProper X.hom := LinearAlgebraicGroups.ProjectiveSpaces.projectiveSpaceProper k W
  haveI : IsClosedImmersion j.left := hj
  haveI : Mono j := mono_over j
  obtain ⟨P⟩ := schemeOrbit k G X b (x ≫ j) hs inferInstance inferInstance inferInstance
  let z := closureInclusion b (x ≫ j)
  have hfac := orbitMap_equivariant a b j x he
  have hker : j.left.ker ≤ z.left.ker := by
    change j.left.ker ≤ (orbitMap b (x ≫ j)).left.imageι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hfac, Over.comp_left]
    exact (orbitMap a x).left.le_ker_comp j.left
  let c : orbitClosure b (x ≫ j) ⟶ Y :=
    Over.homMk (IsClosedImmersion.lift j.left z.left hker) (by
      rw [← Over.w j, ← Category.assoc, IsClosedImmersion.lift_fac, Over.w])
  have hc : c ≫ j = z := Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  haveI : IsClosedImmersion (c.left ≫ j.left) := by
    rw [← Over.comp_left, hc]
    exact inferInstanceAs (IsClosedImmersion (orbitMap b (x ≫ j)).left.imageι)
  haveI : IsClosedImmersion c.left := IsClosedImmersion.of_comp_isClosedImmersion c.left j.left
  let i := P.openInClosure ≫ c
  haveI : IsOpenImmersion P.openInClosure.left := P.isOpen
  have hi : i ≫ j = P.openInClosure ≫ z := by simp only [i, Category.assoc, hc]
  refine ⟨P, i, inferInstanceAs (IsImmersion (P.openInClosure.left ≫ c.left)),
    congrArg Over.Hom.left hi, ?_, ?_⟩
  · rw [← cancel_mono j, Category.assoc, hi, hfac]
    apply Over.OverMorphism.ext
    change P.projection.left ≫ P.openInClosure.left ≫ z.left = _
    rw [← Category.assoc, P.factors]
    exact (orbitMap b (x ≫ j)).left.toImage_imageι
  · intro T g
    exact (stabilizes_equivariant_iff a b j x he g).trans (P.representsStabilizer T g)

open private hom_toBase_eq orbit_apply from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagSchemes
open private productPlanes_injective from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FlagIncidence

private theorem isIso_point_openImmersion
    {R : TestAlgebra k} (p : Points (𝟙_ (SchemeOver k)) R) (hp : IsOpenImmersion p.left)
    (hr : IsLocalRing.closedPoint k ∈ Set.range p.left) : IsIso p := by
  have hsurj : Surjective p.left :=
    ⟨fun x ↦ (Subsingleton.elim (IsLocalRing.closedPoint k) x) ▸ hr⟩
  letI : IsIso p.left := (isIso_iff_isOpenImmersion_and_surjective p.left).mpr ⟨hp, hsurj⟩
  haveI : IsIso ((Over.forget _).map p) := inferInstanceAs (IsIso p.left)
  exact isIso_of_reflects_iso p (Over.forget _)

private theorem conjugate_fixes_iff {M : GroupScheme k} {Y T : SchemeOver k}
    (act : M.X ⨯ Y ⟶ Y)
    (one : ∀ p : T ⟶ Y, prod.lift (1 : T ⟶ M.X) p ≫ act = p)
    (mul : ∀ (g h : T ⟶ M.X) (p : T ⟶ Y),
      prod.lift (g * h) p ≫ act = prod.lift g (prod.lift h p ≫ act) ≫ act)
    (g t : T ⟶ M.X) (p : T ⟶ Y) :
    prod.lift g (prod.lift t p ≫ act) ≫ act = prod.lift t p ≫ act ↔
      prod.lift (t⁻¹ * g * t) p ≫ act = p := by
  constructor
  · intro h
    rw [mul, mul, h, ← mul, inv_mul_cancel, one]
  · intro h
    have hh := congrArg (fun q ↦ prod.lift t q ≫ act) h
    rw [← mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul] at hh
    exact hh

/-- The flag orbit and its stabilizer use the upstream incidence scheme and embedding. -/
theorem flagOrbit : Specs.SmoothOrbit.FlagOrbit.{u} := by
  intro k V _ _ _ _ n v m ranks P D M E A J C G f hs htrans
  let W := Specs.FlagSchemes.flagRepresentation (k := k) (V := V) ranks
  let j := Specs.FlagSchemes.flagEmbedding (Specs.FlagSchemes.liftedBasis v) ranks P D J.segre
  let b : ModObj G.1.X (projectiveSpace k W) :=
    restrictGroupAction f (modObjOfSchemeAction J.action)
  have hb : b.smul = (f.hom.hom ⊗ₘ 𝟙 _) ≫ J.action.act :=
    restrictGroupAction_smul f (modObjOfSchemeAction J.action)
  let act : G.1.X ⊗ D.scheme ⟶ D.scheme :=
    prod.lift (fst _ _ ≫ f.hom.hom) (snd _ _) ≫ A.onFlags
  haveI : IsClosedImmersion j.left := J.embedding_closed
  haveI : Mono j := mono_over j
  have he : act ≫ j = (𝟙 G.1.X ⊗ₘ j) ≫ b.smul := by
    rw [hb, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id,
      ← lift_fst_comp_snd_comp]
    exact J.equivariant _ (fst _ _ ≫ f.hom.hom) (snd _ _)
  let a := restrictAction j b act he
  have ha (S : SchemeOver k) (g : S ⟶ G.1.X) (p : S ⟶ D.scheme) :
      lift g p ≫ a.smul = prod.lift (g ≫ f.hom.hom) p ≫ A.onFlags := by
    change lift g p ≫ prod.lift (fst _ _ ≫ f.hom.hom) (snd _ _) ≫ A.onFlags = _
    rw [prod.comp_lift_assoc, lift_fst_assoc, lift_snd]
  refine ⟨a, b, ha, hb, ?_⟩
  intro x
  obtain ⟨Q, i, hi, hij, hq, hQ⟩ := equivariantProjectiveOrbit k W G D.scheme a b j x
    hs J.embedding_closed he
  have hij' : i ≫ j = Q.openInClosure ≫ closureInclusion b (x ≫ j) :=
    Over.OverMorphism.ext hij
  obtain ⟨z, hz, hl⟩ := htrans n v
  haveI : IsClosedImmersion D.inclusion.left := D.closed
  haveI : Mono D.inclusion := mono_over D.inclusion
  have hzC : z = C.point := by
    apply (cancel_mono D.inclusion).mp
    apply productPlanes_injective (Specs.FlagSchemes.liftedBasis v) ranks _
    exact funext fun q ↦ Module.Grassmannian.ext ((hz q).trans (C.point_formula q).symm)
  subst z
  obtain ⟨R₀, p, d, hp, hr, hpx⟩ := hl _ x (IsLocalRing.closedPoint k)
  haveI : IsIso p := isIso_point_openImmersion p hp hr
  let t := inv p ≫ d
  have hxt : x = prod.lift t (Specs.FlagSchemes.toBasePoint _ ≫ C.point) ≫ A.onFlags := by
    let r := (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k R₀)).op
    have h := congrArg (inv p ≫ ·) hpx
    simp only [prod.comp_lift_assoc, IsIso.inv_hom_id_assoc] at h
    change prod.lift t (inv p ≫ r ≫ C.point) ≫ A.onFlags = x at h
    rw [← Category.assoc (f := inv p) (g := r), hom_toBase_eq (inv p ≫ r)] at h
    exact h.symm
  refine ⟨Q, i, t, hi, hij', hq, hQ, hxt, ?_⟩
  intro R g
  let S := (testSpec k).obj (op R)
  let pR := Specs.FlagSchemes.toBasePoint S ≫ C.point
  let tR : Points M.X R := toUnit _ ≫ t
  let h : Points M.X R := tR⁻¹ * (g ≫ f.hom.hom) * tR
  have hxR : toUnit S ≫ x = prod.lift tR pR ≫ A.onFlags := by
    rw [hxt, prod.comp_lift_assoc]
    change prod.lift tR (toUnit S ≫ Specs.FlagSchemes.toBasePoint _ ≫ C.point) ≫ A.onFlags = _
    rw [← Category.assoc (f := toUnit S) (g := Specs.FlagSchemes.toBasePoint _),
      hom_toBase_eq (toUnit S ≫ Specs.FlagSchemes.toBasePoint _)]
  let inc := Specs.FlagSchemes.coordinateFlagInclusion k _ (Specs.FlagSchemes.prefixCuts ranks) ≫
    C.matrixIso.hom
  have hcoords : g ∈ SubgroupSections Q.stabilizer S ↔
      ∃ q : Points (Specs.FlagSchemes.coordinateFlagLocus k _ (Specs.FlagSchemes.prefixCuts ranks)) R,
        q ≫ inc = h := by
    change (∃ q : S ⟶ Q.stabilizer.group.X, q ≫ Q.stabilizer.inclusion.hom.hom = g) ↔ _
    rw [← hQ S g]
    change (lift g (toUnit S ≫ x) ≫ a.smul = toUnit S ≫ x) ↔ _
    rw [ha, hxR, conjugate_fixes_iff A.onFlags (A.one S) (A.mul S)]
    change prod.lift h pR ≫ A.onFlags = pR ↔ _
    rw [← orbit_apply A.onFlags C.point h]
    constructor
    · intro hh
      exact ⟨C.stabilizer_pullback.lift h (Specs.FlagSchemes.toBasePoint S) hh,
        C.stabilizer_pullback.lift_fst h _ hh⟩
    · rintro ⟨q, hq'⟩
      rw [← hq', Category.assoc, C.stabilizer_pullback.w, ← Category.assoc,
        hom_toBase_eq (q ≫ Specs.FlagSchemes.toBasePoint _)]
  exact ⟨hcoords.trans (C.equations R h), fun hfull ↦
    hcoords.trans (C.full_upper_triangular hfull R h)⟩

end Projective

section DimensionLemmas

open TopologicalSpace Topology Order TopologicalSpace.IrreducibleCloseds

private theorem dim_le_of_affine_charts (Z : Scheme.{u}) (d : WithBot ℕ∞)
    (h : ∀ (U : Z.Opens), IsAffineOpen U → Nonempty U → topologicalKrullDim U ≤ d) :
    topologicalKrullDim Z ≤ d := by
  apply iSup_le
  intro c
  obtain ⟨z, hz⟩ := c.head.isIrreducible.nonempty
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  let U' : Z.Opens := U
  let e := orderIsoOfIsOpenEmbedding U'.ι U'.ι.isOpenEmbedding
  let l : LTSeries (IrreducibleCloseds U) :=
    { length := c.length
      toFun := fun i ↦ e.symm ⟨c i, ⟨⟨z, hzU⟩, c.head_le i hz⟩⟩
      step := fun i ↦ e.symm.strictMono (c.step i) }
  exact (l.length_le_krullDim).trans (h U' hU ⟨⟨z, hzU⟩⟩)

private theorem ring_dimension_eq_trdeg_of_domain (k A : Type u) [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toENat : WithBot ℕ∞) := by
  haveI : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have hh := trdeg_add_eq k A (A := FractionRing A)
  rw [(trdeg_eq_zero_iff (R := A) (A := FractionRing A)).mpr inferInstance, add_zero] at hh
  rw [hh]
  exact P103.Ch06.AffineDimension.domain_dimension k A

private theorem ring_dimension_eq_of_away (k A B : Type u)
    [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] (r : A) (hr : r ≠ 0) [Algebra A B] [IsLocalization.Away r B] :
    ringKrullDim B = ringKrullDim A := by
  have hM : Submonoid.powers r ≤ nonZeroDivisors A :=
    Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hr)
  haveI : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (IsLocalization.injective B hM)
  letI : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' rfl
  have hFt : (algebraMap A B).FiniteType := RingHom.finiteType_holdsForLocalizationAway B r
  letI : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp hFt
  haveI : Algebra.FiniteType k B := Algebra.FiniteType.trans (R := k) (S := A) inferInstance inferInstance
  letI : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers r)
  have hh := trdeg_add_eq k A (A := B)
  rw [(trdeg_eq_zero_iff (R := A) (A := B)).mpr inferInstance, add_zero] at hh
  simp only [ring_dimension_eq_trdeg_of_domain k, hh]

private theorem affine_open_dim_finite {k : Type u} [Field k] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : Z.Opens) (hU : IsAffineOpen U) :
    ∃ n : ℕ, topologicalKrullDim U ≤ n := by
  let A := Γ(Z, U)
  let a := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    f.appLE ⊤ U (by simp)
  letI : Algebra k A := a.hom.toAlgebra
  haveI : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp
    (RingHom.FiniteType.comp (f.finiteType_appLE (isAffineOpen_top _) hU (by simp))
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective))
  obtain ⟨n, p, hp⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
    (inferInstance : Algebra.FiniteType k A)
  refine ⟨n, ?_⟩
  rw [IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum A) ≤ n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (ringKrullDim_le_of_surjective p.toRingHom hp).trans (by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
    simp [ringKrullDim_eq_zero_of_field])

private theorem affine_basic_open_dimension {k : Type u} [Field k] {Z : Scheme.{u}}
    [IsIntegral Z] (f : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : Z.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (r : Γ(Z, U)) (hr : Nonempty (Z.basicOpen r)) :
    topologicalKrullDim (Z.basicOpen r) = topologicalKrullDim U := by
  let A := Γ(Z, U)
  let a := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp)
  letI : Algebra k A := a.hom.toAlgebra
  haveI : Algebra.FiniteType k A := RingHom.finiteType_algebraMap.mp
    (RingHom.FiniteType.comp (f.finiteType_appLE (isAffineOpen_top _) hU (by simp))
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective))
  haveI := hU.isLocalization_basicOpen r
  have hr' : r ≠ 0 := by
    intro h
    subst r
    simp at hr
  change topologicalKrullDim (Z.basicOpen r).toScheme = topologicalKrullDim U.toScheme
  rw [IsHomeomorph.topologicalKrullDim_eq _ (hU.basicOpen r).isoSpec.hom.homeomorph.isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  change topologicalKrullDim (PrimeSpectrum Γ(Z, Z.basicOpen r)) = topologicalKrullDim (PrimeSpectrum A)
  simp only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ring_dimension_eq_of_away k A Γ(Z, Z.basicOpen r) r hr'

private theorem integral_dim_le_of_open {k : Type u} [Field k] {Z : Scheme.{u}}
    [IsIntegral Z] (f : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (W : Z.Opens) (hW : Nonempty W) : topologicalKrullDim Z ≤ topologicalKrullDim W := by
  obtain ⟨z, hz⟩ := hW
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hz W.isOpen
  let V' : Z.Opens := V
  haveI : Nonempty V' := ⟨⟨z, hzV⟩⟩
  have hVW' : topologicalKrullDim V' ≤ topologicalKrullDim W :=
    (Topology.IsEmbedding.inclusion hVW).isInducing.topologicalKrullDim_le
  apply dim_le_of_affine_charts Z
  intro U hU hUne
  haveI : Nonempty U := hUne
  obtain ⟨p, hpU, hpV⟩ :=
    nonempty_preirreducible_inter U.isOpen V'.isOpen
      ⟨(Nonempty.some hUne).val, (Nonempty.some hUne).property⟩ ⟨z, hzV⟩
  obtain ⟨r, s, he, hp⟩ := exists_basicOpen_le_affine_inter hU hV p ⟨hpU, hpV⟩
  have e₁ := affine_basic_open_dimension f U hU r ⟨⟨p, hp⟩⟩
  have e₂ := affine_basic_open_dimension f V' hV s ⟨⟨p, he ▸ hp⟩⟩
  rw [he, e₂] at e₁
  exact e₁.symm.le.trans hVW'

private def restrict_irreducible_closed {T : Type u} [TopologicalSpace T]
    (S : Set T) (C : IrreducibleCloseds T) (h : (C : Set T) ⊆ S) :
    IrreducibleCloseds S where
  carrier := Subtype.val ⁻¹' (C : Set T)
  isClosed' := C.isClosed.preimage continuous_subtype_val
  isIrreducible' := by
    let e := Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
        (by simpa using h : (C : Set T) ⊆ Set.range (Subtype.val : S → T))
    haveI : IrreducibleSpace (C : Set T) := Subtype.irreducibleSpace C.isIrreducible
    haveI : IrreducibleSpace (Subtype.val ⁻¹' (C : Set T) : Set S) :=
      e.irreducibleSpace_iff.mpr inferInstance
    exact IsIrreducible.of_subtype

private theorem dim_le_of_components {T : Type u} [TopologicalSpace T] (d : WithBot ℕ∞)
    (h : ∀ (S : Set T), S ∈ irreducibleComponents T → topologicalKrullDim S ≤ d) :
    topologicalKrullDim T ≤ d := by
  apply iSup_le
  intro c
  obtain ⟨S, hS, hcS⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ c.last.isIrreducible
  have e (i : Fin (c.length + 1)) : (c i : Set T) ⊆ S :=
    (show (c i : Set T) ⊆ c.last from c.monotone (Fin.le_last i)).trans hcS
  let l : LTSeries (IrreducibleCloseds S) :=
    { length := c.length
      toFun := fun i ↦ restrict_irreducible_closed S (c i) (e i)
      step := fun i ↦ by
        have hstep : c i.castSucc < c i.succ := c.step i
        change restrict_irreducible_closed S (c i.castSucc) (e i.castSucc) <
          restrict_irreducible_closed S (c i.succ) (e i.succ)
        refine lt_of_le_of_ne ?_ ?_
        · change Subtype.val ⁻¹' (c i.castSucc : Set T) ⊆ Subtype.val ⁻¹' (c i.succ : Set T)
          exact Set.preimage_mono hstep.le
        · intro ee
          have eq := congrArg (fun C : IrreducibleCloseds S ↦ Subtype.val '' (C : Set S)) ee
          change Subtype.val '' (Subtype.val ⁻¹' (c i.castSucc : Set T) : Set S) =
            Subtype.val '' (Subtype.val ⁻¹' (c i.succ : Set T) : Set S) at eq
          rw [Set.image_preimage_eq_of_subset, Set.image_preimage_eq_of_subset] at eq
          · exact hstep.ne (SetLike.coe_injective eq)
          · simpa using e i.succ
          · simpa using e i.castSucc }
  exact (l.length_le_krullDim).trans (h S hS)

private theorem component_inter_dense_open {T : Type u} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] (W : Set T) (hW : Dense W)
    (S : Set T) (hS : S ∈ irreducibleComponents T) : (W ∩ S).Nonempty := by
  obtain ⟨U, hU, hUne, hUS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent S hS
  obtain ⟨s, hsU, hsW⟩ := hW.inter_open_nonempty U hU hUne
  exact ⟨s, hsW, hUS hsU⟩

private theorem boundary_dim_lt {T : Type u} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {W : Set T} (hW : Dense W) (ho : IsOpen W)
    {n : ℕ} (hn : topologicalKrullDim T = n) : topologicalKrullDim ↥(Wᶜ : Set T) < n := by
  rw [topologicalKrullDim, Order.krullDim_lt_coe_iff]
  intro c
  let φ := map (Subtype.val : ↥(Wᶜ : Set T) → T) continuous_subtype_val
  let l := c.map φ (map_strictMono_of_isInducing Topology.IsInducing.subtypeVal)
  have hl : (l.last : Set T) ⊆ Wᶜ := by
    change closure (Subtype.val '' (c.last : Set ↥(Wᶜ : Set T))) ⊆ Wᶜ
    exact ho.isClosed_compl.closure_subset_iff.mpr (by
      rintro _ ⟨z, _, rfl⟩
      exact z.property)
  obtain ⟨S, hS, hLS⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ l.last.isIrreducible
  let C : IrreducibleCloseds T :=
    ⟨S, hS.1, isClosed_of_mem_irreducibleComponents S hS⟩
  have hlt : l.last < C := by
    refine lt_of_le_of_ne hLS ?_
    intro e
    obtain ⟨z, hzW, hzS⟩ := component_inter_dense_open W hW S hS
    exact (hl (by simpa [e, C] using hzS)) hzW
  have hd := Order.LTSeries.length_le_krullDim (l.snoc C hlt : LTSeries (IrreducibleCloseds T))
  change ((c.length + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim T at hd
  rw [hn, ← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_le_coe,
    ENat.natCast_le_natCast] at hd
  exact Nat.lt_of_succ_le hd

end DimensionLemmas

section Dimensions

open TopologicalSpace Topology Order TopologicalSpace.IrreducibleCloseds

private theorem component_dim_data {k : Type u} [Field k] {Z : Scheme.{u}}
    [IsNoetherian Z] [IsReduced Z]
    (f : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (W : Z.Opens) (hW : Dense (W : Set Z))
    {S : Set Z} (hS : S ∈ irreducibleComponents Z) :
    ∃ n : ℕ, topologicalKrullDim S ≤ n ∧ topologicalKrullDim S ≤ topologicalKrullDim W := by
  let j := Z.irreducibleComponentι S hS
  let T := Z.irreducibleComponent S hS
  let V := Z.irreducibleComponentOpen S
  haveI : QuasiCompact V.ι := by
    haveI : NoetherianSpace V.toScheme := V.ι.isOpenEmbedding.isInducing.noetherianSpace
    rw [quasiCompact_iff_isSpectralMap]
    refine ⟨V.ι.continuous, ?_⟩
    intro U hU ho
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hR : IsReduced T := by
    haveI : IsReduced V.toScheme := inferInstance
    let q : V.toScheme ⟶ (V.ι).image := V.ι.toImage
    haveI : IsSchemeTheoreticallyDominant q := toImage_dominant V.ι
    have hred := IsSchemeTheoreticallyDominant.isReduced q
    change IsReduced (Z.irreducibleComponentIdeal S hS).subscheme
    rw [Scheme.irreducibleComponentIdeal_def]
    exact hred
  haveI : IsIntegral T := (isIntegral_iff_irreducibleSpace_and_isReduced T).mpr
    ⟨inferInstanceAs (IrreducibleSpace (Z.irreducibleComponent S hS)), hR⟩
  haveI : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (Z.irreducibleComponentι S hS))
  let g := j ≫ f
  haveI : LocallyOfFiniteType g := inferInstanceAs (LocallyOfFiniteType (j ≫ f))
  let W' : T.Opens := j ⁻¹ᵁ W
  obtain ⟨z, hzW, hzS⟩ := component_inter_dense_open W hW S hS
  have hz : (⟨z, hzS⟩ : T) ∈ W' := hzW
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUW⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hz W'.isOpen
  let U' : T.Opens := U
  obtain ⟨n, hn⟩ := affine_open_dim_finite g U' hU
  have hdim : topologicalKrullDim T ≤ topologicalKrullDim U' :=
    integral_dim_le_of_open g U' ⟨⟨⟨z, hzS⟩, hzU⟩⟩
  have hdW' : topologicalKrullDim U' ≤ topologicalKrullDim W' :=
    (Topology.IsEmbedding.inclusion hUW).isInducing.topologicalKrullDim_le
  have hdW : topologicalKrullDim W' ≤ topologicalKrullDim W := by
    apply (show Topology.IsInducing (fun t : W' ↦ (⟨j t.val, t.property⟩ : W)) from ?_).topologicalKrullDim_le
    apply Topology.IsInducing.subtypeVal.of_comp_iff.mp
    exact j.isEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  exact ⟨n, hdim.trans hn, hdim.trans (hdW'.trans hdW)⟩

private theorem dense_open_dimension {k : Type u} [Field k] {Z : Scheme.{u}}
    [Nonempty Z] [IsNoetherian Z] [IsReduced Z]
    (f : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (W : Z.Opens) (hW : Dense (W : Set Z)) :
    ∃ n : ℕ, topologicalKrullDim Z = n ∧ topologicalKrullDim W = n := by
  classical
  haveI : Finite (irreducibleComponents Z) := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  letI := Fintype.ofFinite (irreducibleComponents Z)
  have hf : ∀ S : irreducibleComponents Z,
      ∃ n : ℕ, topologicalKrullDim S.val ≤ n ∧ topologicalKrullDim S.val ≤ topologicalKrullDim W :=
    fun S ↦ component_dim_data f W hW S.property
  choose N hN hNW using hf
  let bound : ℕ := Finset.univ.sup N
  have hb : topologicalKrullDim Z ≤ bound :=
    dim_le_of_components _ (fun S hS ↦ (hN ⟨S, hS⟩).trans (by
      exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ ⟨S, hS⟩)))
  have he : topologicalKrullDim Z = topologicalKrullDim W :=
    (dim_le_of_components _ (fun S hS ↦ hNW ⟨S, hS⟩)).antisymm
      (topologicalKrullDim_subspace_le _ _)
  haveI : Nonempty (IrreducibleCloseds Z) := ⟨⟨closure {(Nonempty.some inferInstance : Z)},
    isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hn : ¬InfiniteDimensionalOrder (IrreducibleCloseds Z) := by
    intro hinf
    have ht : topologicalKrullDim Z = ⊤ := Order.krullDim_eq_top
    rw [ht] at hb
    have hbound : (bound : WithBot ℕ∞) < ⊤ := by
      rw [← WithBot.coe_natCast, ← WithBot.coe_top, WithBot.coe_lt_coe]
      exact ENat.natCast_lt_top _
    exact hbound.not_ge hb
  haveI := (finiteDimensionalOrder_or_infiniteDimensionalOrder (IrreducibleCloseds Z)).resolve_right hn
  exact ⟨_, Order.krullDim_eq_length_of_finiteDimensionalOrder,
    he ▸ Order.krullDim_eq_length_of_finiteDimensionalOrder⟩

private theorem minimum_orbit_closed_in_scheme {k : Type u} [Field k] [IsAlgClosed k]
    (G : AffineAlgebraicGroup k) (X : SchemeOver k) (a : ModObj G.1.X X)
    (x : 𝟙_ (SchemeOver k) ⟶ X) [Smooth G.1.X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (hmin : ∀ y : 𝟙_ (SchemeOver k) ⟶ X,
      topologicalKrullDim (orbitSet a x) ≤ topologicalKrullDim (orbitSet a y)) :
    IsClosed (orbitSet a x) := by
  classical
  let f := orbitMap a x
  let Z := orbitClosure a x
  let q := toClosure a x
  let i := closureInclusion a x
  haveI : IsAffine G.1.X.left := G.2.1
  haveI : IsAffineHom (f.left ≫ X.hom) := by rw [Over.w]; infer_instance
  haveI : IsAffineHom f.left := IsAffineHom.of_comp f.left X.hom
  haveI : QuasiCompact (orbitMap a x).left := inferInstanceAs (QuasiCompact f.left)
  haveI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion f.left.imageι)
  haveI : LocallyOfFiniteType Z.hom := inferInstanceAs (LocallyOfFiniteType (i.left ≫ X.hom))
  haveI : QuasiCompact Z.hom := inferInstanceAs (QuasiCompact (i.left ≫ X.hom))
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  haveI : CompactSpace Z.left := (quasiCompact_iff_compactSpace Z.hom).mp inferInstance
  haveI : IsNoetherian Z.left := {}
  haveI : GeometricallyReduced G.1.X.hom :=
    (affineGroupSmoothnessCriteria k G).1.mp inferInstance
  haveI : IsReduced G.1.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.1.X.hom
  haveI : IsSchemeTheoreticallyDominant q.left := toImage_dominant f.left
  haveI : IsReduced Z.left := IsSchemeTheoreticallyDominant.isReduced q.left
  haveI : Nonempty Z.left := ⟨q.left (η[G.1.X].left (IsLocalRing.closedPoint k))⟩
  obtain ⟨P⟩ := schemeOrbit k G X a x inferInstance inferInstance inferInstance inferInstance
  haveI : IsOpenImmersion P.openInClosure.left := P.isOpen
  let U := P.openInClosure.left.opensRange
  have hU : Set.range q.left = (U : Set Z.left) := by
    change Set.range f.left.toImage = Set.range P.openInClosure.left
    rw [← P.factors]
    change Set.range (P.openInClosure.left ∘ P.projection.left) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr P.surjective.1, Set.image_univ]
  have hDense : Dense (U : Set Z.left) := hU ▸ f.left.toImage.denseRange
  have hOrbit : orbitSet a x = i.left '' (U : Set Z.left) := by
    rw [← hU, orbitSet, ← toClosure_fac a x, Over.comp_left]
    exact Set.range_comp ⇑i.left ⇑q.left
  by_contra hclosed
  have hB : ((U : Set Z.left)ᶜ).Nonempty := by
    rw [← Set.ssubset_univ_iff_nonempty_compl]
    refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, fun hu ↦ hclosed ?_⟩
    rw [hOrbit, hu, Set.image_univ]
    exact i.left.isClosedEmbedding.isClosed_range
  haveI : JacobsonSpace Z.left := LocallyOfFiniteType.jacobsonSpace Z.hom
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints hB U.isOpen.isClosed_compl.isLocallyClosed
  let y : 𝟙_ (SchemeOver k) ⟶ Z :=
    Over.homMk (pointOfClosedPoint Z.hom z hzc) (pointOfClosedPoint_comp Z.hom z hzc)
  obtain ⟨c, hc, hi⟩ := orbitClosure_action a x
  have hSmall : orbitSet c y ⊆ (U : Set Z.left)ᶜ := by
    rintro _ ⟨g, rfl⟩ hg
    let l := lift (𝟙 G.1.X) (toUnit G.1.X ≫ y)
    have ha : c.smul.left (l.left g) ∈ Set.range q.left := by
      rw [hU]
      exact hg
    have hp := snd_mem_orbit_range c q hc (l.left g) ha
    have hl : l ≫ snd G.1.X Z = toUnit G.1.X ≫ y := lift_snd _ _
    have hl' := congrArg Over.Hom.left hl
    rw [Over.comp_left, Over.comp_left] at hl'
    have he : (snd G.1.X Z).left (l.left g) = z := by
      rw [← Scheme.Hom.comp_apply, hl', Scheme.Hom.comp_apply]
      exact pointOfClosedPoint_apply Z.hom z hzc _
    rw [he, hU] at hp
    exact hz hp
  obtain ⟨n, hn, hUn⟩ := dense_open_dimension Z.hom U hDense
  have hOld : topologicalKrullDim (orbitSet a x) = n := by
    rw [hOrbit, ← hUn]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (i.left.isEmbedding.homeomorphImage (U : Set Z.left)).isHomeomorph).symm
  have hNew : topologicalKrullDim (orbitSet a (y ≫ i)) < n := by
    rw [orbitSet_equivariant c a i y hi]
    have hdim := IsHomeomorph.topologicalKrullDim_eq _
      (i.left.isEmbedding.homeomorphImage (orbitSet c y)).isHomeomorph
    rw [← hdim]
    exact (Topology.IsEmbedding.inclusion hSmall).isInducing.topologicalKrullDim_le.trans_lt
      (boundary_dim_lt hDense U.isOpen hn)
  exact (not_lt_of_ge (hmin (y ≫ i))) (hOld.symm ▸ hNew)

/-- An orbit of least dimension in a stable closed subscheme is closed. -/
theorem minimumOrbitClosed : Specs.SmoothOrbit.MinimumOrbitClosed.{u} := by
  intro k _ _ G X Y j a b hs hsep hft hqc hj he x hmin
  haveI : Smooth G.1.X.hom := hs
  haveI : IsClosedImmersion j.left := hj
  haveI : IsSeparated X.hom := hsep
  haveI : LocallyOfFiniteType X.hom := hft
  haveI : QuasiCompact X.hom := hqc
  haveI : IsSeparated Y.hom := by rw [← Over.w j]; infer_instance
  haveI : LocallyOfFiniteType Y.hom := by rw [← Over.w j]; infer_instance
  haveI : QuasiCompact Y.hom := by rw [← Over.w j]; infer_instance
  have ht : 𝟙 G.1.X ⊗ₘ j = lift (fst G.1.X Y) (snd G.1.X Y ≫ j) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have he' : b.smul ≫ j = (𝟙 G.1.X ⊗ₘ j) ≫ a.smul := ht.symm ▸ he
  have hd (y : 𝟙_ (SchemeOver k) ⟶ Y) :
      topologicalKrullDim (orbitSet b y) = topologicalKrullDim (orbitSet a (y ≫ j)) := by
    rw [orbitSet_equivariant b a j y he']
    exact IsHomeomorph.topologicalKrullDim_eq _
      (j.left.isEmbedding.homeomorphImage (orbitSet b y)).isHomeomorph
  rw [orbitSet_equivariant b a j x he']
  apply j.left.isClosedEmbedding.isClosedMap
  apply minimum_orbit_closed_in_scheme G Y b x
  intro y
  rw [hd x, hd y]
  exact hmin y

private theorem exists_rational_point {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] [Nonempty X.left] : Nonempty (𝟙_ (SchemeOver k) ⟶ X) := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty (α := X.left)) isOpen_univ.isLocallyClosed
  exact ⟨Over.homMk (pointOfClosedPoint X.hom x hx) (pointOfClosedPoint_comp X.hom x hx)⟩

/-- A nonempty finite-type scheme over an algebraically closed field has a closed orbit. -/
theorem closedOrbitExists : Specs.SmoothOrbit.ClosedOrbitExists.{u} := by
  intro k _ _ G X a hs hsep hft hqc hn
  letI : Smooth G.1.X.hom := hs
  letI : IsSeparated X.hom := hsep
  letI : LocallyOfFiniteType X.hom := hft
  letI : QuasiCompact X.hom := hqc
  letI : Nonempty X.left := hn
  obtain ⟨y⟩ := exists_rational_point X
  obtain ⟨x, hx⟩ := exists_minimalFor_of_wellFoundedLT (fun _ ↦ True)
    (fun z ↦ topologicalKrullDim (orbitSet a z)) ⟨y, trivial⟩
  have hclosed := minimum_orbit_closed_in_scheme G X a x (fun _ ↦ hx.le trivial)
  obtain ⟨P⟩ := schemeOrbit k G X a x hs hsep hft hqc
  let i := P.openInClosure ≫ closureInclusion a x
  have hfac : P.projection ≫ i = orbitMap a x := by
    apply Over.OverMorphism.ext
    change P.projection.left ≫ P.openInClosure.left ≫ (orbitMap a x).left.imageι = _
    rw [← Category.assoc, P.factors, Scheme.Hom.toImage_imageι]
  have hrange : orbitSet a x = Set.range i.left := by
    rw [orbitSet, ← hfac, Over.comp_left]
    change Set.range (i.left ∘ P.projection.left) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr P.surjective.1, Set.image_univ]
  haveI : IsOpenImmersion P.openInClosure.left := P.isOpen
  haveI : IsPreimmersion i.left := by dsimp [i]; infer_instance
  exact ⟨x, P, IsClosedImmersion.of_isPreimmersion i.left (hrange ▸ hclosed)⟩

end Dimensions

/-- Every geometric point of a scheme orbit is a translate of its defining point. -/
theorem geometricOrbitLifts : Specs.SmoothOrbit.GeometricOrbitLifts.{u} := by
  intro k _ _ G X a x y
  let f := orbitMap a x
  constructor
  · rintro ⟨g, hg⟩
    let T := pullback f y
    let p := pullback.snd f y
    have hp := (IsPullback.of_hasPullback f y).map (Over.forget _)
    obtain ⟨z, -, -⟩ := Scheme.exists_preimage_of_isPullback hp g (IsLocalRing.closedPoint k) hg
    letI : Nonempty T.left := ⟨z⟩
    haveI : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [Over.w]; exact G.2.2.1
    haveI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
    haveI : LocallyOfFiniteType p.left :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp
        (show LocallyOfFiniteType f.left from inferInstance)
    haveI : LocallyOfFiniteType (𝟙_ (SchemeOver k)).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k))))
    haveI : LocallyOfFiniteType T.hom := by rw [← Over.w p]; infer_instance
    obtain ⟨t⟩ := exists_rational_point T
    refine ⟨t ≫ pullback.fst f y, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      toUnit_unique (t ≫ p) (𝟙 _), Category.id_comp]
  · rintro ⟨g, hg⟩
    refine ⟨g.left (IsLocalRing.closedPoint k), ?_⟩
    change f.left (g.left _) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hg]

end

end LinearAlgebraicGroups.SmoothOrbit
