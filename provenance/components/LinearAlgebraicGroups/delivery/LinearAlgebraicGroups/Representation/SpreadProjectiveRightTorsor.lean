import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Int.Basic
import Specs.LinearAlgebraicGroups.Representation.SpreadProjectiveRightTorsor
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 80000

universe u v w

namespace LinearAlgebraicGroups.Representation.SpreadProjectiveRightTorsor

noncomputable section

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.ArithmeticProjectiveFiniteness (BaseRing projectiveSpace)
open Specs.SpreadProjectiveRightTorsor (rationalMap changeBaseComp changeBaseAlongComp rightMultiply HasLocalSections RationalFibreComparison Statement)


section LocalizationDiagram

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- The principal localizations whose denominators lie in a fixed submonoid. -/
structure Denominator where
  val : M

instance : Preorder (Denominator M) where
  le a b := (a.val : R) ∣ (b.val : R)
  le_refl _ := dvd_refl _
  le_trans _ _ _ := dvd_trans

instance : Nonempty (Denominator M) := ⟨⟨1⟩⟩

instance : IsDirectedOrder (Denominator M) where
  directed a b := ⟨⟨a.val * b.val⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩

private def principalLocalizationMap {a b : Denominator M} (h : a ≤ b) :
    Localization.Away (a.val : R) →+* Localization.Away (b.val : R) :=
  IsLocalization.Away.lift (a.val : R)
    (IsLocalization.Away.isUnit_of_dvd (b.val : R) h)

@[simp] private theorem principalLocalizationMap_algebraMap {a b : Denominator M}
    (h : a ≤ b) (r : R) :
    principalLocalizationMap M h (algebraMap R _ r) = algebraMap R _ r :=
  IsLocalization.Away.lift_eq _ _ _

/-- Diagram of the rings obtained by inverting a single denominator. -/
abbrev principalLocalizations : Denominator M ⥤ CommRingCat.{u} where
  obj a := CommRingCat.of (Localization.Away (a.val : R))
  map f := CommRingCat.ofHom (principalLocalizationMap M (leOfHom f))
  map_id a := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : R))
    ext r
    change principalLocalizationMap M (le_refl a) (algebraMap R _ r) = algebraMap R _ r
    simp
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : R))
    ext r
    change principalLocalizationMap M (leOfHom (f ≫ g)) (algebraMap R _ r) =
      principalLocalizationMap M (leOfHom g)
        (principalLocalizationMap M (leOfHom f) (algebraMap R _ r))
    simp

private def localizationComparison (K : Type u) [CommRing K] [Algebra R K] [IsLocalization M K]
    (a : Denominator M) : Localization.Away (a.val : R) →+* K :=
  IsLocalization.Away.lift (a.val : R) (IsLocalization.map_units K a.val)

@[simp] private theorem localizationComparison_algebraMap (K : Type u) [CommRing K] [Algebra R K]
    [IsLocalization M K] (a : Denominator M) (r : R) :
    localizationComparison M K a (algebraMap R _ r) = algebraMap R K r :=
  IsLocalization.Away.lift_eq _ _ _

/-- The comparison cocone from single-denominator localizations to localization at the submonoid. -/
def localizationCocone (K : Type u) [CommRing K] [Algebra R K] [IsLocalization M K] :
    Cocone (principalLocalizations M) := by
  refine ⟨CommRingCat.of K, ?_⟩
  refine { app := fun a => CommRingCat.ofHom (localizationComparison M K a), naturality := ?_ }
  intro a b f
  trans CommRingCat.ofHom (localizationComparison M K a)
  swap
  · exact (Category.comp_id (CommRingCat.ofHom (localizationComparison M K a))).symm
  apply CommRingCat.hom_ext
  change (localizationComparison M K b).comp (principalLocalizationMap M (leOfHom f)) =
    localizationComparison M K a
  apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : R))
  ext r
  simp

private def localizationCoconeBaseMap (s : Cocone (principalLocalizations M)) :
    R →+* s.pt :=
  (s.ι.app ⟨1⟩).hom.comp (algebraMap R (Localization.Away (1 : R)))

private theorem localizationCoconeBaseMap_apply (s : Cocone (principalLocalizations M))
    (a : Denominator M) (r : R) :
    localizationCoconeBaseMap M s r =
      (s.ι.app a).hom (algebraMap R (Localization.Away (a.val : R)) r) := by
  let f : (⟨1⟩ : Denominator M) ⟶ a := homOfLE (one_dvd _)
  have h : (principalLocalizations M).map f ≫ s.ι.app a = s.ι.app ⟨1⟩ := s.w f
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    (algebraMap R (Localization.Away (1 : R)) r)
  simp only [CommRingCat.hom_comp] at h'
  change (s.ι.app a).hom (principalLocalizationMap M (leOfHom f)
    (algebraMap R (Localization.Away (1 : R)) r)) =
    (s.ι.app ⟨1⟩).hom (algebraMap R (Localization.Away (1 : R)) r) at h'
  exact h'.symm.trans (congrArg (s.ι.app a).hom
    (principalLocalizationMap_algebraMap M (a := ⟨1⟩) (b := a) (leOfHom f) r))

private theorem localizationCoconeBaseMap_isUnit (s : Cocone (principalLocalizations M))
    (a : M) : IsUnit (localizationCoconeBaseMap M s a) := by
  rw [localizationCoconeBaseMap_apply M s ⟨a⟩]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a : R)) (a : R)).map
    (s.ι.app ⟨a⟩).hom

/-- Localizing at all the denominators is the filtered colimit of inverting one denominator at a
time. This gives an affine-transition inverse limit on spectra. -/
def localizationCoconeIsColimit (K : Type u) [CommRing K] [Algebra R K] [IsLocalization M K] :
    IsColimit (localizationCocone M K) where
  desc s := CommRingCat.ofHom (IsLocalization.lift (localizationCoconeBaseMap_isUnit M s))
  fac s a := by
    apply CommRingCat.hom_ext
    change (IsLocalization.lift (localizationCoconeBaseMap_isUnit M s)).comp
      (localizationComparison M K a) = (s.ι.app a).hom
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : R))
    ext r
    change (IsLocalization.lift (localizationCoconeBaseMap_isUnit M s))
      (localizationComparison M K a (algebraMap R _ r)) =
      (s.ι.app a).hom (algebraMap R (Localization.Away (a.val : R)) r)
    rw [localizationComparison_algebraMap, IsLocalization.lift_eq]
    exact localizationCoconeBaseMap_apply M s a r
  uniq s f h := by
    apply CommRingCat.hom_ext
    change f.hom = (IsLocalization.lift (S := K) (localizationCoconeBaseMap_isUnit M s))
    apply IsLocalization.ringHom_ext (S := K) M
    ext r
    have he := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (h ⟨1⟩))
      (algebraMap R (Localization.Away (1 : R)) r)
    change f.hom (localizationComparison M K ⟨1⟩ (algebraMap R _ r)) =
      (s.ι.app ⟨1⟩).hom (algebraMap R (Localization.Away (1 : R)) r) at he
    change f.hom (algebraMap R K r) =
      IsLocalization.lift (S := K) (localizationCoconeBaseMap_isUnit M s) (algebraMap R K r)
    rw [IsLocalization.lift_eq]
    rw [localizationComparison_algebraMap] at he
    exact he

private abbrev specLocalizationDiagram :=
  (principalLocalizations M).op ⋙ Scheme.Spec

private def specLocalizationStructure :
    specLocalizationDiagram M ⟶
      (Functor.const (Denominator M)ᵒᵖ).obj (Spec (CommRingCat.of R)) where
  app a := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a.unop.val : R))))
  naturality a b f := by
    dsimp
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact principalLocalizationMap_algebraMap M (leOfHom f.unop) r

variable (K : Type u) [CommRing K] [Algebra R K] [IsLocalization M K]

private abbrev specLocalizationCone : Cone (specLocalizationDiagram M) :=
  Scheme.Spec.mapCone (localizationCocone M K).op

private theorem specLocalizationCone_comm (a : (Denominator M)ᵒᵖ) :
    (specLocalizationCone M K).π.app a ≫ (specLocalizationStructure M).app a =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  change Spec.map (CommRingCat.ofHom (localizationComparison M K a.unop)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a.unop.val : R)))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact localizationComparison_algebraMap M K a.unop r

/-- The localization spectrum is the inverse limit of the principal opens in the base. -/
def localizationOverIsLimit :
    IsLimit (Over.liftCone _ (specLocalizationStructure M) (specLocalizationCone M K)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) (specLocalizationCone_comm M K)) :=
  Over.isLimitLiftCone _ _ _ _ _ <|
    isLimitOfPreserves Scheme.Spec (IsColimit.op (localizationCoconeIsColimit M K))

private abbrev localizationBaseDiagram :=
  Over.lift (specLocalizationDiagram M) (specLocalizationStructure M)

private abbrev localizationBaseCone :=
  Over.liftCone _ (specLocalizationStructure M) (specLocalizationCone M K)
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (specLocalizationCone_comm M K)

variable (X : Over (Spec (CommRingCat.of R)))

/-- The diagram of successive principal restrictions of an (R)-scheme. -/
abbrev principalRestriction :=
  localizationBaseDiagram M ⋙ Over.pullback X.hom

/-- The restriction of X to the localization at all denominators, with its maps to
the principal restrictions. -/
abbrev principalRestrictionCone :=
  (Over.pullback X.hom).mapCone (localizationBaseCone M K)

private theorem isOpenImmersion_principalRestriction_hom (a : (Denominator M)ᵒᵖ) :
    IsOpenImmersion ((principalRestriction M X).obj a).hom := by
  change IsOpenImmersion (pullback.snd
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a.unop.val : R))))) X.hom)
  infer_instance

private theorem isAffineHom_principalRestriction_hom (a : (Denominator M)ᵒᵖ) :
    IsAffineHom ((principalRestriction M X).obj a).hom := by
  let v := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (a.unop.val : R))))
  exact MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback v X.hom) (inferInstanceAs (IsAffineHom v))

private theorem isAffineHom_principalRestriction_map {a b : (Denominator M)ᵒᵖ}
    (f : a ⟶ b) : IsAffineHom ((principalRestriction M X).map f).left := by
  have := isOpenImmersion_principalRestriction_hom M X b
  have h : IsPullback (𝟙 _) ((principalRestriction M X).map f).left
      ((principalRestriction M X).obj a).hom ((principalRestriction M X).obj b).hom :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, Over.w]⟩
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h
    (isAffineHom_principalRestriction_hom M X a)

private abbrev restrictionSchemes :=
  principalRestriction M X ⋙ Over.forget X.left

private def restrictionToBase :
    restrictionSchemes M X ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) where
  app a := ((principalRestriction M X).obj a).hom ≫ X.hom
  naturality a b e := by
    change ((principalRestriction M X).map e).left ≫
        (((principalRestriction M X).obj b).hom ≫ X.hom) = _
    rw [← Category.assoc, Over.w, Functor.const_obj_map]
    exact (Category.comp_id _).symm

private def restrictionSchemesLimit :
    IsLimit ((Over.forget _).mapCone (principalRestrictionCone M K X)) :=
  isLimitOfPreserves (Over.forget _) <|
    isLimitOfPreserves (Over.pullback X.hom) (localizationOverIsLimit M K)

private theorem compactSpace_principalRestriction [CompactSpace X.left]
    (a : (Denominator M)ᵒᵖ) : CompactSpace ((restrictionSchemes M X).obj a) := by
  have := isAffineHom_principalRestriction_hom M X a
  exact QuasiCompact.compactSpace_of_compactSpace (((principalRestriction M X).obj a).hom)

/-- Over an affine base, a map from a localized quasi-compact quasi-separated scheme
to a scheme locally of finite presentation descends to a principal restriction. -/
theorem exists_morphism_of_principalRestriction [CompactSpace X.left]
    [QuasiSeparatedSpace X.left] {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation p]
    (f : (principalRestrictionCone M K X).pt.left ⟶ Y)
    (hf : f ≫ p = (principalRestrictionCone M K X).pt.hom ≫ X.hom) :
    ∃ (a : (Denominator M)ᵒᵖ) (g : ((principalRestriction M X).obj a).left ⟶ Y),
      ((principalRestrictionCone M K X).π.app a).left ≫ g = f ∧
      g ≫ p = ((principalRestriction M X).obj a).hom ≫ X.hom := by
  let D := restrictionSchemes M X
  let c := (Over.forget _).mapCone (principalRestrictionCone M K X)
  have hc : IsLimit c := restrictionSchemesLimit M K X
  let affineStages {a b : (Denominator M)ᵒᵖ} (e : a ⟶ b) : IsAffineHom (D.map e) :=
    isAffineHom_principalRestriction_map M X e
  let compactStage (a : (Denominator M)ᵒᵖ) : CompactSpace (D.obj a) :=
    compactSpace_principalRestriction M X a
  let separatedStage (a : (Denominator M)ᵒᵖ) : QuasiSeparatedSpace (D.obj a) :=
    (isOpenImmersion_principalRestriction_hom M X a).1.quasiSeparatedSpace
  apply Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D (restrictionToBase M X) p c hc f
  ext a
  change ((principalRestrictionCone M K X).π.app a).left ≫
      (((principalRestriction M X).obj a).hom ≫ X.hom) = f ≫ p
  rw [hf, ← Category.assoc, Over.w]
  rfl

/-- An equality of morphisms over a localization holds after inverting one
of the original denominators, for a quasi-compact source and a locally
finite type target. -/
theorem exists_equal_after_principalRestriction [CompactSpace X.left]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType p] (f g : X.left ⟶ Y)
    (hf : f ≫ p = X.hom) (hg : g ≫ p = X.hom)
    (h : (principalRestrictionCone M K X).pt.hom ≫ f =
      (principalRestrictionCone M K X).pt.hom ≫ g) :
    ∃ a : (Denominator M)ᵒᵖ,
      ((principalRestriction M X).obj a).hom ≫ f =
        ((principalRestriction M X).obj a).hom ≫ g := by
  let D := restrictionSchemes M X
  let c := (Over.forget _).mapCone (principalRestrictionCone M K X)
  have hc : IsLimit c := restrictionSchemesLimit M K X
  let affineStages {a b : (Denominator M)ᵒᵖ} (e : a ⟶ b) : IsAffineHom (D.map e) :=
    isAffineHom_principalRestriction_map M X e
  let compactStage (a : (Denominator M)ᵒᵖ) : CompactSpace (D.obj a) :=
    compactSpace_principalRestriction M X a
  let a : (Denominator M)ᵒᵖ := op ⟨1⟩
  let j := ((principalRestriction M X).obj a).hom
  have hh : c.π.app a ≫ j = (principalRestrictionCone M K X).pt.hom :=
    Over.w ((principalRestrictionCone M K X).π.app a)
  obtain ⟨b, e, he⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D
    (restrictionToBase M X) p c hc (j ≫ f) (j ≫ g)
    (by rw [Category.assoc, hf]; rfl) (by rw [Category.assoc, hg]; rfl)
    (by simp only [← Category.assoc, hh, h])
  refine ⟨b, ?_⟩
  have hj : D.map e ≫ j = ((principalRestriction M X).obj b).hom :=
    Over.w ((principalRestriction M X).map e)
  simpa only [← Category.assoc, hj] using he

end LocalizationDiagram

/-- A constructible subset of an integral affine base missing its generic point
is contained in the zero locus of a single nonzero element. -/
theorem exists_nonzero_zeroLocus_of_constructible {R : Type u} [CommRing R] [IsDomain R]
    {Z : Set (PrimeSpectrum R)} (hZ : IsConstructible Z) (hη : (⊥ : PrimeSpectrum R) ∉ Z) :
    ∃ a : R, a ≠ 0 ∧ Z ⊆ PrimeSpectrum.zeroLocus {a} := by
  classical
  obtain ⟨C, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hZ
  have hEach (c : C) :
      ∃ a : R, a ≠ 0 ∧ c.val.toSet ⊆ PrimeSpectrum.zeroLocus {a} := by
    by_cases hf : c.val.f = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [PrimeSpectrum.BasicConstructibleSetData.toSet, hf]
      simp
    · have h : ¬ ∀ j, c.val.g j = 0 := by
        intro h
        apply hη
        rw [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion₂]
        refine ⟨c.val, c.property, ?_⟩
        change (⊥ : PrimeSpectrum R) ∈
          PrimeSpectrum.zeroLocus (Set.range c.val.g) \ PrimeSpectrum.zeroLocus {c.val.f}
        simp [PrimeSpectrum.mem_zeroLocus, h, hf]
      obtain ⟨j, hj⟩ := not_forall.mp h
      refine ⟨c.val.g j, hj, ?_⟩
      intro x hx
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hx.1 (Set.mem_range_self j)
  choose a hne ha using hEach
  refine ⟨∏ c : C, a c, Finset.prod_ne_zero_iff.mpr fun c _ ↦ hne c, ?_⟩
  intro x hx
  rw [PrimeSpectrum.ConstructibleSetData.toSet, Set.mem_iUnion₂] at hx
  obtain ⟨c, hc, hx⟩ := hx
  have hh := ha ⟨c, hc⟩ hx
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hh ⊢
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ ⟨c, hc⟩)) hh

/-- A constructible bad locus on a finitely presented scheme can be removed from the base
by a single principal localization if it misses the generic fibre. -/
theorem exists_principal_open_avoiding {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    {Z : Set X} (hZ : IsConstructible Z) (hη : ∀ x ∈ Z, f x ≠ (⊥ : PrimeSpectrum R)) :
    ∃ a : R, a ≠ 0 ∧
      Disjoint Z (Set.range (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away a)))))) := by
  obtain ⟨a, ha, h⟩ := exists_nonzero_zeroLocus_of_constructible
    (f.isConstructible_image hZ) (by
      rintro ⟨x, hx, he⟩
      exact hη x hx he)
  refine ⟨a, ha, Set.disjoint_left.mpr fun x hx hxf ↦ ?_⟩
  rw [IsOpenImmersion.range_pullbackFst] at hxf
  have hax : a ∈ (f x).asIdeal := by
    have he : (f x : PrimeSpectrum R) ∈ PrimeSpectrum.zeroLocus {a} :=
      h (Set.mem_image_of_mem f hx)
    exact ((PrimeSpectrum.mem_zeroLocus (f x : PrimeSpectrum R) {a}).mp he) (Set.mem_singleton a)
  change f x ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) at hxf
  rw [PrimeSpectrum.localization_away_comap_range _ a] at hxf
  exact (PrimeSpectrum.mem_basicOpen a (f x : PrimeSpectrum R)).mp hxf hax

section QuotientSpreading

open Specs.FlagCohomology (SchemeOverRing)

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The scalar composition comparison preserves the group scheme laws. -/
def changeBaseGrpComp {C : Type u} [CommRing C] (φ : A →+* B) (ψ : B →+* C) :
    (changeBase (ψ.comp φ)).mapGrp ≅ (changeBase φ).mapGrp ⋙ (changeBase ψ).mapGrp :=
  Functor.mapGrpNatIso (changeBaseComp φ ψ) ≪≫ Functor.mapGrpCompIso

/-- Changing the base of a morphism in the slice gives the same
cartesian square as pulling back over its target. -/
theorem changeBaseMap_isPullback (φ : A →+* B) {X Y : SchemeOverRing A} (q : X ⟶ Y) :
    IsPullback ((changeBase φ).map q).left (fibreProjection φ X)
      (fibreProjection φ Y) q.left := by
  let b := Spec.map (CommRingCat.ofHom φ)
  have h : IsPullback (fibreProjection φ X) (pullback.snd X.hom b) (q.left ≫ Y.hom) b := by
    rw [Over.w q]
    exact IsPullback.of_hasPullback _ _
  have hf : ((changeBase φ).map q).left ≫ fibreProjection φ Y =
      fibreProjection φ X ≫ q.left := pullback.lift_fst _ _ _
  have hs : ((changeBase φ).map q).left ≫ pullback.snd Y.hom b =
      pullback.snd X.hom b := pullback.lift_snd _ _ _
  exact (IsPullback.of_bot (hs.symm ▸ h) hf.symm (IsPullback.of_hasPullback Y.hom b)).flip

theorem range_changeBaseMap (φ : A →+* B) {X Y : SchemeOverRing A} (q : X ⟶ Y) :
    Set.range ((changeBase φ).map q).left = (fibreProjection φ Y) ⁻¹' Set.range q.left := by
  let h := changeBaseMap_isPullback φ q
  have hs : Function.Surjective h.isoPullback.hom := h.isoPullback.hom.homeomorph.surjective
  rw [← h.isoPullback_hom_fst]
  change Set.range (pullback.fst (fibreProjection φ Y) q.left ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr hs,
    Set.image_univ, Scheme.Pullback.range_fst]

private theorem flat_fibreProjection (M : Submonoid A) [Algebra A B] [IsLocalization M B]
    (X : SchemeOverRing A) : Flat (fibreProjection (algebraMap A B) X) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B M))
  change Flat (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap A B))))
  infer_instance

private theorem isIso_stalkMap_of_flat_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] [SurjectiveOnStalks f] (x : X) : IsIso (f.stalkMap x) := by
  have hr := Flat.stalkMap f x
  have hf : (f.stalkMap x).hom.FaithfullyFlat := by
    algebraize [(f.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := f.prop x
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hf.injective, f.stalkMap_surjective x⟩

private theorem isIso_stalkMap_fibreProjection (M : Submonoid A) [Algebra A B]
    [IsLocalization M B] (X : SchemeOverRing A) (x : ((changeBase (algebraMap A B)).obj X).left) :
    IsIso ((fibreProjection (algebraMap A B) X).stalkMap x) := by
  have := IsPreimmersion.of_isLocalization M (S := B)
  have : IsPreimmersion (fibreProjection (algebraMap A B) X) :=
    inferInstanceAs (IsPreimmersion (pullback.fst X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))))
  have := flat_fibreProjection (B := B) M X
  exact isIso_stalkMap_of_flat_of_surjectiveOnStalks _ x

private def stalkMapIso_of_square {X' Y' X Y : Scheme.{u}}
    {a : X' ⟶ X} {r : X' ⟶ Y'} {q : X ⟶ Y} {b : Y' ⟶ Y}
    (h : a ≫ q = r ≫ b) (x : X') [IsIso (a.stalkMap x)] [IsIso (b.stalkMap (r x))] :
    Arrow.mk (q.stalkMap (a x)) ≅ Arrow.mk (r.stalkMap x) :=
  Arrow.isoMk' _ _
    (TopCat.Presheaf.stalkCongr _ (.of_eq <| by
      rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]) ≪≫ asIso (b.stalkMap (r x)))
    (asIso (a.stalkMap x))
    (by
      simp only [Iso.trans_hom, asIso_hom, Category.assoc, ← Scheme.Hom.stalkMap_comp]
      exact (Scheme.Hom.stalkMap_congr_hom _ _ h x).symm)

private theorem formallySmooth_iff_of_localization (M : Submonoid A) [Algebra A B]
    [IsLocalization M B] {X Y : SchemeOverRing A} (q : X ⟶ Y)
    (x : ((changeBase (algebraMap A B)).obj X).left) :
    (q.left.stalkMap (fibreProjection (algebraMap A B) X x)).hom.FormallySmooth ↔
      (((changeBase (algebraMap A B)).map q).left.stalkMap x).hom.FormallySmooth := by
  let φ := algebraMap A B
  letI := isIso_stalkMap_fibreProjection M X x
  letI := isIso_stalkMap_fibreProjection M Y (((changeBase φ).map q).left x)
  let e := stalkMapIso_of_square (changeBaseMap_isPullback φ q).w.symm x
  exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff e

/-- The right-action kernel pair is preserved by every base change, including
base change to a residue field. -/
theorem changeBase_kernelPair (φ : A →+* B) {G H : Grp (SchemeOverRing A)}
    (i : H ⟶ G) {Y : SchemeOverRing A} (q : G.X ⟶ Y)
    (hq : IsPullback prod.fst (rightMultiply i) q q) :
    IsPullback prod.fst (rightMultiply ((changeBase φ).mapGrp.map i))
      ((changeBase φ).map q) ((changeBase φ).map q) := by
  let F := changeBase φ
  let e := PreservesLimitPair.iso F G.X H.X
  have hfst : e.inv ≫ F.map prod.fst = prod.fst := PreservesLimitPair.iso_inv_fst F G.X H.X
  have hsnd : e.inv ≫ F.map prod.snd = prod.snd := PreservesLimitPair.iso_inv_snd F G.X H.X
  have hmul : e.inv ≫ F.map (rightMultiply i) = rightMultiply (F.mapGrp.map i) := by
    change e.inv ≫ F.map (prod.fst * (prod.snd ≫ i.hom.hom)) = _
    simp only [F.map_mul, F.map_comp, MonObj.comp_mul, ← Category.assoc]
    rw [hfst, hsnd]
    rfl
  change IsPullback (prod.fst : F.obj G.X ⨯ F.obj H.X ⟶ F.obj G.X)
    (rightMultiply (F.mapGrp.map i)) (F.map q) (F.map q)
  have hId : 𝟙 (F.obj G.X) ≫ F.map q = F.map q ≫ 𝟙 (F.obj Y) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  exact (F.map_isPullback hq).of_iso' e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hfst.trans (Category.comp_id _).symm) (hmul.trans (Category.comp_id _).symm)
    hId hId


private theorem rightMultiply_lift {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    {T : SchemeOverRing A} (g : T ⟶ G.X) (b : T ⟶ H.X) :
    prod.lift g b ≫ rightMultiply i = g * (b ≫ i.hom.hom) := by
  simp [rightMultiply, MonObj.comp_mul]

private theorem quotient_rightMultiply {G H : Grp (SchemeOverRing A)} {i : H ⟶ G}
    {Y : SchemeOverRing A} {q : G.X ⟶ Y}
    (hq : IsPullback prod.fst (rightMultiply i) q q)
    {T : SchemeOverRing A} (g : T ⟶ G.X) (b : T ⟶ H.X) :
    (g * (b ≫ i.hom.hom)) ≫ q = g ≫ q := by
  rw [← rightMultiply_lift, Category.assoc, ← hq.w, prod.lift_fst_assoc]

private theorem quotient_difference {G H : Grp (SchemeOverRing A)} {i : H ⟶ G}
    {Y : SchemeOverRing A} {q : G.X ⟶ Y}
    (hq : IsPullback prod.fst (rightMultiply i) q q)
    {T : SchemeOverRing A} (g g' : T ⟶ G.X) (he : g ≫ q = g' ≫ q) :
    ∃ b : T ⟶ H.X, g * (b ≫ i.hom.hom) = g' := by
  let t := hq.lift g g' he
  refine ⟨t ≫ prod.snd, ?_⟩
  have ht : t ≫ prod.fst = g := hq.lift_fst _ _ _
  rw [← ht]
  simpa only [t, rightMultiply, MonObj.comp_mul, Category.assoc] using hq.lift_snd g g' he

/-- To spread a right-torsor kernel pair, it suffices to spread invariance
and the factorization of the universal difference through the subgroup. -/
theorem rightKernelPair_iff_difference {G H : Grp (SchemeOverRing A)}
    (i : H ⟶ G) [Mono i.hom.hom] {Y : SchemeOverRing A} (q : G.X ⟶ Y) :
    IsPullback prod.fst (rightMultiply i) q q ↔
      prod.fst ≫ q = rightMultiply i ≫ q ∧
        ∃ d : pullback q q ⟶ H.X, d ≫ i.hom.hom =
          (pullback.fst q q)⁻¹ * pullback.snd q q := by
  constructor
  · intro hq
    obtain ⟨d, hd⟩ := quotient_difference hq (pullback.fst q q) (pullback.snd q q)
      pullback.condition
    exact ⟨hq.w, d, inv_mul_eq_iff_eq_mul.mpr hd.symm |>.symm⟩
  · rintro ⟨w, d, hd⟩
    refine IsPullback.mk' w ?_ ?_
    · intro T l l' hf hs
      apply prod.hom_ext hf
      apply (cancel_mono i.hom.hom).mp
      have h : (l ≫ prod.fst) * ((l ≫ prod.snd) ≫ i.hom.hom) =
          (l' ≫ prod.fst) * ((l' ≫ prod.snd) ≫ i.hom.hom) := by
        simpa only [rightMultiply, MonObj.comp_mul, Category.assoc] using hs
      rw [hf] at h
      exact mul_left_cancel h
    · intro T g g' he
      let b := pullback.lift g g' he ≫ d
      refine ⟨prod.lift g b, prod.lift_fst _ _, ?_⟩
      have h : b ≫ i.hom.hom = g⁻¹ * g' := by
        dsimp only [b]
        rw [Category.assoc, hd, MonObj.comp_mul, GrpObj.comp_inv,
          pullback.lift_fst, pullback.lift_snd]
      rw [rightMultiply_lift, h, mul_inv_cancel_left]


variable (A) [IsDomain A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]

private theorem genericPoint_mem_range :
    (⊥ : PrimeSpectrum A) ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)

/-- Smoothness of a finitely presented morphism on the generic fibre
persists after a principal restriction of its arithmetic base. -/
theorem exists_smooth_principal_restriction {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation q.left] [LocallyOfFinitePresentation X.hom]
    [QuasiCompact X.hom] [TopologicalSpace.NoetherianSpace X.left]
    (hq : Smooth ((changeBase (algebraMap A K)).map q).left) :
    ∃ a : A, a ≠ 0 ∧
      Smooth ((changeBase (algebraMap A (Localization.Away a))).map q).left := by
  let Z := (q.left.smoothLocus : Set X.left)ᶜ
  have hZ : IsConstructible Z := isConstructible_compl.mpr
    ((TopologicalSpace.NoetherianSpace.isCompact _).isConstructible q.left.smoothLocus.2)
  have hη (x : X.left) (hx : x ∈ Z) : X.hom x ≠ (⊥ : PrimeSpectrum A) := by
    intro hxη
    have hm : x ∈ Set.range (fibreProjection (algebraMap A K) X) := by
      change x ∈ Set.range (pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hxη]
      exact genericPoint_mem_range A K
    obtain ⟨y, rfl⟩ := hm
    apply hx
    apply (formallySmooth_iff_of_localization (nonZeroDivisors A) q y).mpr
    let := hq
    change y ∈ ((changeBase (algebraMap A K)).map q).left.smoothLocus
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  obtain ⟨a, ha, h⟩ := exists_principal_open_avoiding X.hom hZ hη
  refine ⟨a, ha, ?_⟩
  let φ := algebraMap A (Localization.Away a)
  let r := ((changeBase φ).map q).left
  have : LocallyOfFinitePresentation r :=
    MorphismProperty.of_isPullback (changeBaseMap_isPullback φ q).flip ‹_›
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  apply (formallySmooth_iff_of_localization (Submonoid.powers a) q x).mp
  by_contra hn
  exact Set.disjoint_left.mp h hn ⟨x, rfl⟩

/-- If a finitely presented map is surjective over the generic point of an
integral affine base, it is surjective after inverting one nonzero scalar. -/
theorem exists_surjective_principal_restriction {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation q.left] [QuasiCompact q.left]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [TopologicalSpace.NoetherianSpace Y.left]
    (hq : Surjective ((changeBase (algebraMap A K)).map q).left) :
    ∃ a : A, a ≠ 0 ∧
      Surjective ((changeBase (algebraMap A (Localization.Away a))).map q).left := by
  let Z := (Set.range q.left)ᶜ
  have hZ : IsConstructible Z := by
    apply isConstructible_compl.mpr
    rw [← Set.image_univ]
    exact q.left.isConstructible_image IsConstructible.univ
  have hη (y : Y.left) (hy : y ∈ Z) : Y.hom y ≠ (⊥ : PrimeSpectrum A) := by
    intro he
    have hmem : y ∈ Set.range (fibreProjection (algebraMap A K) Y) := by
      change y ∈ Set.range (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, he]
      exact genericPoint_mem_range A K
    obtain ⟨z, rfl⟩ := hmem
    apply hy
    letI := hq
    have hh : z ∈ Set.range ((changeBase (algebraMap A K)).map q).left :=
      ((changeBase (algebraMap A K)).map q).left.surjective z
    rw [range_changeBaseMap] at hh
    exact hh
  obtain ⟨a, ha, h⟩ := exists_principal_open_avoiding Y.hom hZ hη
  refine ⟨a, ha, ⟨?_⟩⟩
  rw [← Set.range_eq_univ, range_changeBaseMap, Set.eq_univ_iff_forall]
  intro z
  change fibreProjection (algebraMap A (Localization.Away a)) Y z ∈ Set.range q.left
  by_contra hz
  exact Set.disjoint_left.mp h hz ⟨z, rfl⟩

end QuotientSpreading

private theorem liftedIntegerHom_unique {R : Type u} [CommRing R] (f g : ULift.{u} ℤ →+* R) :
    f = g := by
  ext x
  have h : f.comp ULift.ringEquiv.symm.toRingHom = g.comp ULift.ringEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  exact DFunLike.congr_fun h x.down

theorem rationalMap_comp_refinement {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (φ : BaseRing.{u} m →+* BaseRing.{u} n)
    (hφ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} n)) :
    (rationalMap hn).comp φ = rationalMap hm := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (m : ULift.{u} ℤ))
  rw [RingHom.comp_assoc, hφ]
  exact liftedIntegerHom_unique _ _

/-- A further principal restriction of the arithmetic base is again
obtained by inverting one nonzero positive integer. -/
theorem refineArithmeticBase {m : ℕ} (hm : m ≠ 0) (a : BaseRing.{u} m) (ha : a ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ m ∣ n ∧
      ∃ e : Localization.Away a ≃+* BaseRing.{u} n,
        e.toRingHom.comp ((algebraMap (BaseRing.{u} m) (Localization.Away a)).comp
          (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m))) =
          algebraMap (ULift.{u} ℤ) (BaseRing.{u} n) := by
  let R := ULift.{u} ℤ
  let S := BaseRing.{u} m
  let T := Localization.Away a
  let algRS : Algebra R S := inferInstance
  let algST : Algebra S T := inferInstance
  let τ : R →+* T := (algebraMap S T).comp (algebraMap R S)
  let alg : Algebra R T := @RingHom.toAlgebra R T _ _ τ
  letI : Algebra R T := alg
  have hTower : @IsScalarTower R S T algRS.toSMul algST.toSMul alg.toSMul :=
    @IsScalarTower.of_algebraMap_eq' R S T _ _ _ algRS algST alg rfl
  let r := (IsLocalization.Away.sec (m : R) a).1
  have hr : Associated (algebraMap R S r) a := IsLocalization.Away.associated_sec_fst (m : R) a
  let d := r.down.natAbs
  have hdr : Associated r (d : R) :=
    (Int.associated_natAbs r.down).map (ULift.ringEquiv.symm : ℤ ≃+* R)
  have hd : d ≠ 0 := by
    intro h
    apply ha
    have hzero : (d : R) = 0 := by rw [h]; rfl
    exact hr.eq_zero_iff.mp (by rw [hdr.eq_zero_iff.mpr hzero, map_zero])
  have hAssoc : Associated (algebraMap R S (d : R)) a :=
    (hdr.map (algebraMap R S)).symm.trans hr
  have hloc : IsLocalization.Away (↑(m * d) : R) T := by
    rw [Nat.cast_mul]
    exact @IsLocalization.Away.mul_of_associated R _ S _ algRS (m : R) (d : R) a
      inferInstance T _ algST alg hTower inferInstance hAssoc
  let e := IsLocalization.algEquiv (Submonoid.powers (↑(m * d) : R)) T (BaseRing.{u} (m * d))
  refine ⟨m * d, mul_ne_zero hm hd, dvd_mul_right m d, e.toRingEquiv, ?_⟩
  apply RingHom.ext
  intro x
  exact e.commutes x

private theorem imageFactor_schemeTheoreticallyDominant {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  let V (U : Y.affineOpens) : f.image.affineOpens :=
    ⟨f.imageι ⁻¹ᵁ U.val, U.property.preimage f.imageι⟩
  have hV : (⨆ U, (V U).val) = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    have h : f.imageι x ∈ (⨆ U : Y.affineOpens, U.val) := by
      rw [iSup_affineOpens_eq_top Y]
      trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩
  refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top V hV fun U ↦ ?_⟩
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    ← RingHom.injective_iff_ker_eq_bot]
  exact f.toImage_app_injective U

/-- The schematic image of a closed subscheme along a quasi-compact flat
monomorphism restricts back to that closed subscheme. -/
theorem image_restricts_of_flat_mono {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    [Flat f] [Mono f] [QuasiCompact f] (j : Z ⟶ Y) [IsClosedImmersion j] :
    IsPullback j (j ≫ f).toImage f (j ≫ f).imageι := by
  let h := j ≫ f
  let p := h.toImage
  let i := h.imageι
  have w : j ≫ f = p ≫ i := h.toImage_imageι.symm
  let t := pullback.lift j p w
  have hp : IsPullback (𝟙 Z) t p (pullback.snd f i) := by
    have hout : IsPullback (𝟙 Z) (t ≫ pullback.fst f i) (p ≫ i) f := by
      refine IsPullback.of_horiz_isIso_mono ⟨?_⟩
      rw [Category.id_comp, pullback.lift_fst, w]
    refine IsPullback.of_bot hout ?_ (IsPullback.of_hasPullback f i).flip
    rw [Category.id_comp, pullback.lift_snd]
  letI : IsSchemeTheoreticallyDominant p := imageFactor_schemeTheoreticallyDominant h
  letI : QuasiCompact p := inferInstanceAs (QuasiCompact h.toImage)
  have ht : IsSchemeTheoreticallyDominant t := .of_isPullback hp
  have hclosed : IsClosedImmersion (t ≫ pullback.fst f i) := by
    rw [show t ≫ pullback.fst f i = j from pullback.lift_fst _ _ _]
    exact ‹IsClosedImmersion j›
  letI : IsClosedImmersion t :=
    @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ t (pullback.fst f i) inferInstance hclosed
  have : IsIso t.imageι := (Scheme.isIso_subschemeι_iff_eq_bot t.ker).mpr ht.ker_eq_bot
  letI : IsIso t := by
    rw [← t.toImage_imageι]
    infer_instance
  exact (IsPullback.of_hasPullback f i).of_iso' (asIso t) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ((pullback.lift_fst _ _ _).trans (Category.comp_id _).symm)
    ((pullback.lift_snd _ _ _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- A closed immersion over a localization has a closed model in the fixed
ambient scheme, with its generic embedding recovered by base change. -/
theorem exists_closed_model_of_localization {A B : Type u} [CommRing A] [CommRing B]
    (M : Submonoid A) [Algebra A B] [IsLocalization M B]
    {P : SchemeOverRing A} {Z : SchemeOverRing B}
    (j : Z ⟶ (changeBase (algebraMap A B)).obj P) (hj : IsClosedImmersion j.left) :
    ∃ (Y : SchemeOverRing A) (i : Y ⟶ P), IsClosedImmersion i.left ∧
      ∃ e : Z ≅ (changeBase (algebraMap A B)).obj Y,
        e.hom ≫ (changeBase (algebraMap A B)).map i = j := by
  let φ := algebraMap A B
  let b := Spec.map (CommRingCat.ofHom φ)
  let p := fibreProjection φ P
  have : IsPreimmersion b := IsPreimmersion.of_isLocalization M (S := B)
  have : IsPreimmersion p := inferInstanceAs (IsPreimmersion (pullback.fst P.hom b))
  have : Flat p := flat_fibreProjection M P
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (pullback.fst P.hom b))
  let i := (j.left ≫ p).imageι
  let r := (j.left ≫ p).toImage
  let Y : SchemeOverRing A := Over.mk (i ≫ P.hom)
  let i' : Y ⟶ P := Over.homMk i rfl
  have hs : IsPullback j.left r p i := image_restricts_of_flat_mono p j.left
  have hpb : IsPullback r Z.hom Y.hom b := by
    rw [← Over.w j]
    exact hs.flip.paste_vert (IsPullback.of_hasPullback P.hom b)
  let e : Z ≅ (changeBase φ).obj Y := Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd
  refine ⟨Y, i', inferInstanceAs (IsClosedImmersion i), e, ?_⟩
  apply Over.OverMorphism.ext
  change e.hom.left ≫ ((changeBase φ).map i').left = j.left
  apply (cancel_mono p).mp
  calc
    _ = e.hom.left ≫ fibreProjection φ Y ≫ i :=
      (Category.assoc _ _ _).trans (e.hom.left ≫= pullback.lift_fst _ _ _)
    _ = r ≫ i := hpb.isoPullback_hom_fst_assoc _
    _ = j.left ≫ p := hs.w.symm


section ProjectiveComparison

open HomogeneousLocalization
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase)
open Specs.ArithmeticProjectiveFiniteness (projectiveSpace)

private abbrev polyGrading (A : Type u) (I : Type v) [CommRing A] := MvPolynomial.homogeneousSubmodule I A

private def polyConstants (A : Type u) (I : Type v) [CommRing A] : A →+* polyGrading A I 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C I a⟩
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

private abbrev polyProj (A : Type (max u v)) (I : Type v) [CommRing A] : SchemeOverRing A :=
  Over.mk (Proj.toSpecZero (polyGrading A I) ≫ Spec.map (CommRingCat.ofHom (polyConstants A I)))

private theorem polynomialIrrelevant_le (A : Type u) (I : Type v) [CommRing A] :
    (HomogeneousIdeal.irrelevant (polyGrading A I)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := A) (σ := I))) := by
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  simp only [Set.iUnion_subset_iff]
  intro n hn p hp
  classical
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hd := (show p.IsHomogeneous n from hp).degree_eq_sum_deg_support hm
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    simp at hd
    omega
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hm0
  exact Ideal.mem_of_dvd _ (MvPolynomial.X_dvd_monomial.mpr (.inr
    (Finsupp.mem_support_iff.mp hi))) (Ideal.subset_span ⟨i, rfl⟩)

private abbrev polyProjCover (A : Type (max u v)) (I : Type v) [CommRing A] : (polyProj A I).left.AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (polyGrading A I) MvPolynomial.X
    (fun i => MvPolynomial.isHomogeneous_X A i) (fun _ => Nat.one_pos)
    (polynomialIrrelevant_le A I)

section GradedPolynomialMaps
variable {A B : Type u} [CommRing A] [CommRing B] {I : Type v} {J : Type w}

private def gradedPolynomialMap (φ : A →+* B) (f : I → J) :
    polyGrading A I →+*ᵍ polyGrading B J where
  toRingHom := (MvPolynomial.rename f).toRingHom.comp (MvPolynomial.map φ)
  map_mem h := (MvPolynomial.IsHomogeneous.map h φ).rename_isHomogeneous

@[simp] private theorem gradedPolynomialMap_X (φ : A →+* B) (f : I → J) (i : I) :
    gradedPolynomialMap φ f (MvPolynomial.X i) = MvPolynomial.X (f i) := by
  change MvPolynomial.rename f (MvPolynomial.map φ (MvPolynomial.X i)) = _
  simp

@[simp] private theorem gradedPolynomialMap_C (φ : A →+* B) (f : I → J) (a : A) :
    gradedPolynomialMap φ f (MvPolynomial.C a) = MvPolynomial.C (φ a) := by
  change MvPolynomial.rename f (MvPolynomial.map φ (MvPolynomial.C a)) = _
  simp

private theorem irrelevant_le_gradedPolynomialMap (φ : A →+* B) (f : I → J)
    (hf : Function.Surjective f) :
    HomogeneousIdeal.irrelevant (polyGrading B J) ≤
      (HomogeneousIdeal.irrelevant (polyGrading A I)).map (gradedPolynomialMap φ f) := by
  change (HomogeneousIdeal.irrelevant (polyGrading B J)).toIdeal ≤ _
  refine (polynomialIrrelevant_le B J).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  obtain ⟨i, rfl⟩ := hf j
  rw [← gradedPolynomialMap_X φ f i]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _
    Nat.one_pos (MvPolynomial.isHomogeneous_X A i))

end GradedPolynomialMaps

section PolynomialProjMaps
variable {A B : Type (max u v w)} [CommRing A] [CommRing B] {I : Type v} {J : Type w}

private abbrev polyProjMap (φ : A →+* B) (f : I → J) (hf : Function.Surjective f) :
    (polyProj.{max u v,w} B J).left ⟶ (polyProj.{max u w,v} A I).left :=
  Proj.map (gradedPolynomialMap φ f) (irrelevant_le_gradedPolynomialMap φ f hf)

private def chartConstants (A : Type u) (I : Type v) [CommRing A] (s : MvPolynomial I A) :
    A →+* Away (polyGrading A I) s :=
  (fromZeroRingHom _ _).comp (polyConstants A I)

@[simp] private theorem chartMap_constants (φ : A →+* B) (f : I → J)
    (s : MvPolynomial I A) (a : A) :
    Away.map (gradedPolynomialMap φ f) s (chartConstants A I s a) =
      chartConstants B J _ (φ a) := by
  change map _ _ (HomogeneousLocalization.mk _) = HomogeneousLocalization.mk _
  rw [HomogeneousLocalization.map_mk]
  apply val_injective
  change Localization.mk (gradedPolynomialMap φ f (MvPolynomial.C a))
      ⟨gradedPolynomialMap φ f 1, _⟩ =
    Localization.mk (MvPolynomial.C (φ a)) ⟨1, _⟩
  rw [gradedPolynomialMap_C]
  congr 1
  exact Subtype.ext (map_one (gradedPolynomialMap φ f))

private theorem chartToBase (A : Type (max u v)) (I : Type v) [CommRing A] {s : MvPolynomial I A}
    {n : ℕ} (hn : 0 < n) (hs : s ∈ polyGrading A I n) :
    Proj.awayι (polyGrading A I) s hs hn ≫ (polyProj A I).hom =
      Spec.map (CommRingCat.ofHom (chartConstants A I s)) := by
  change Proj.awayι _ _ hs hn ≫ (Proj.toSpecZero _ ≫ _) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem polyProjMap_over (φ : A →+* B) (f : I → J) (hf : Function.Surjective f) :
    polyProjMap.{u,v,w} φ f hf ≫ (polyProj.{max u w,v} A I).hom =
      (polyProj.{max u v,w} B J).hom ≫ Spec.map (CommRingCat.ofHom φ) := by
  let g := gradedPolynomialMap φ f
  let h := irrelevant_le_gradedPolynomialMap φ f hf
  refine (Proj.mapAffineOpenCover g h).openCover.hom_ext _ _
    (fun (i : Σ d : PNat, polyGrading A I d) => ?_)
  change Proj.awayι _ (g i.2) (g.2 i.2.2) i.1.2 ≫ (Proj.map g h ≫ (polyProj.{max u w,v} A I).hom) =
    Proj.awayι _ (g i.2) (g.2 i.2.2) i.1.2 ≫ ((polyProj.{max u v,w} B J).hom ≫ Spec.map _)
  rw [← Category.assoc, Proj.awayι_comp_map g h i.1.2 _ i.2.2, Category.assoc, (chartToBase.{max u w,v} A I), ← Category.assoc,
    (chartToBase.{max u v,w} B J), ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact chartMap_constants.{u,v,w} φ f _ a

private theorem gradedPolynomialMap_comp {C : Type (max u v w)} {L : Type v} [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) (f : I → J) (g : J → L) :
    (gradedPolynomialMap ψ g).comp (gradedPolynomialMap φ f) =
      gradedPolynomialMap (ψ.comp φ) (g ∘ f) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change gradedPolynomialMap ψ g (gradedPolynomialMap φ f (MvPolynomial.C a)) =
      gradedPolynomialMap (ψ.comp φ) (g ∘ f) (MvPolynomial.C a)
    simp
  · intro i
    change gradedPolynomialMap ψ g (gradedPolynomialMap φ f (MvPolynomial.X i)) =
      gradedPolynomialMap (ψ.comp φ) (g ∘ f) (MvPolynomial.X i)
    simp

private theorem gradedPolynomialMap_id (A : Type (max u v)) (I : Type v) [CommRing A] :
    gradedPolynomialMap (RingHom.id A) (id : I → I) = GradedRingHom.id (polyGrading A I) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · exact gradedPolynomialMap_C _ _
  · exact gradedPolynomialMap_X _ _

private theorem polyProjMap_congr {g g' : polyGrading A I →+*ᵍ polyGrading B J}
    (e : g = g')
    (h : HomogeneousIdeal.irrelevant (polyGrading B J) ≤
      (HomogeneousIdeal.irrelevant (polyGrading A I)).map g)
    (h' : HomogeneousIdeal.irrelevant (polyGrading B J) ≤
      (HomogeneousIdeal.irrelevant (polyGrading A I)).map g') :
    Proj.map g h = Proj.map g' h' := by
  cases e
  rfl

private theorem polyProjRename_inv_hom (A : Type (max u v w)) [CommRing A] (e : I ≃ J) :
    polyProjMap.{u,v,w} (RingHom.id A) e e.surjective ≫
      polyProjMap.{u,w,v} (RingHom.id A) e.symm e.symm.surjective = 𝟙 _ := by
  rw [polyProjMap, polyProjMap, ← Proj.map_comp]
  have he : (e : I → J) ∘ (e.symm : J → I) = id := funext e.apply_symm_apply
  have he' : (gradedPolynomialMap (RingHom.id A) e).comp
      (gradedPolynomialMap (RingHom.id A) e.symm) = GradedRingHom.id (polyGrading A J) := by
    rw [gradedPolynomialMap_comp.{u,w,v}, RingHom.id_comp, he,
      gradedPolynomialMap_id.{max u v,w}]
  exact (polyProjMap_congr he' _ _).trans Proj.map_id

private def polyProjRename (A : Type (max u v w)) [CommRing A] (e : I ≃ J) :
    polyProj.{max u w,v} A I ≅ polyProj.{max u v,w} A J := by
  let f := polyProjMap.{u,w,v} (RingHom.id A) e.symm e.symm.surjective
  let g := polyProjMap.{u,v,w} (RingHom.id A) e e.surjective
  exact Over.isoMk ⟨f, g, polyProjRename_inv_hom.{u,w,v} A e.symm,
      polyProjRename_inv_hom.{u,v,w} A e⟩ (by
    change polyProjMap.{u,w,v} (RingHom.id A) e.symm e.symm.surjective ≫ _ = _
    rw [polyProjMap_over.{u,w,v}, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

end PolynomialProjMaps

section PolynomialCharts

private abbrev polyChart (A : Type u) (I : Type v) [CommRing A] (i : I) :=
  Away (polyGrading A I) (MvPolynomial.X i)

private def chartRatio (A : Type u) (I : Type v) [CommRing A] (i j : I) : polyChart A I i :=
  Away.mk (polyGrading A I) (MvPolynomial.isHomogeneous_X A i) 1 (MvPolynomial.X j)
    (by change MvPolynomial.X _ ∈ polyGrading A I 1; exact MvPolynomial.isHomogeneous_X A j)

private theorem chartRatio_val (A : Type u) (I : Type v) [CommRing A] (i j : I) :
    (chartRatio A I i j).val = Localization.mk
      (S := Submonoid.powers (MvPolynomial.X (R := A) i)) (MvPolynomial.X j)
        ⟨(MvPolynomial.X i)^1, ⟨1, rfl⟩⟩ := rfl

@[simp] private theorem chartRatio_diag (A : Type u) (I : Type v) [CommRing A] (i : I) :
    chartRatio A I i i = 1 := by
  apply val_injective
  rw [chartRatio_val, val_one]
  simpa only [pow_one] using
    (Localization.mk_self (S := Submonoid.powers (MvPolynomial.X (R := A) i))
      ⟨MvPolynomial.X i, Submonoid.mem_powers _⟩)

private def polynomialToChart (A : Type u) (I : Type v) [CommRing A] (i : I) :
    MvPolynomial {j : I // j ≠ i} A →+* polyChart A I i :=
  MvPolynomial.eval₂Hom (chartConstants A I (MvPolynomial.X i)) (fun j => chartRatio A I i j)

private theorem polyConstants_surj (A : Type u) (I : Type v) [CommRing A] :
    Function.Surjective (polyConstants A I) := by
  intro p
  have hp := p.property
  change (p : MvPolynomial I A) ∈ MvPolynomial.homogeneousSubmodule I A 0 at hp
  rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hp
  obtain ⟨a, ha⟩ := hp
  exact ⟨a, Subtype.ext ha⟩

private theorem polynomialToChart_injective (A : Type u) (I : Type v) [CommRing A] (i : I) :
    Function.Injective (polynomialToChart A I i) := by
  classical
  let ev : MvPolynomial I A →+* MvPolynomial {j : I // j ≠ i} A :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun j => if h : j ≠ i then MvPolynomial.X ⟨j, h⟩ else 1)
  have ev_i : ev (MvPolynomial.X i) = 1 := by simp [ev]
  let ev' : Localization.Away (MvPolynomial.X (R := A) i) →+*
      MvPolynomial {j : I // j ≠ i} A :=
    IsLocalization.Away.lift (g := ev) (MvPolynomial.X i) (ev_i ▸ isUnit_one)
  have evalFrac (p : MvPolynomial I A) (n : ℕ) :
      ev' (Localization.mk p ⟨(MvPolynomial.X i)^n, ⟨n, rfl⟩⟩) = ev p := by
    rw [Localization.mk_eq_mk']
    have h := congrArg ev' (IsLocalization.mk'_spec (M := Submonoid.powers (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i)) p ⟨(MvPolynomial.X i)^n, ⟨n, rfl⟩⟩)
    simpa [ev', ev_i] using h
  let r := ev'.comp (algebraMap (polyChart A I i) _)
  have h : r.comp (polynomialToChart A I i) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, polynomialToChart, MvPolynomial.eval₂Hom_C]
      change ev' (Localization.mk (MvPolynomial.C a) ⟨(MvPolynomial.X i)^0, ⟨0, rfl⟩⟩) = _
      rw [evalFrac]
      simp [ev]
    · intro j
      rw [RingHom.comp_apply, polynomialToChart, MvPolynomial.eval₂Hom_X']
      change ev' (Localization.mk (MvPolynomial.X j.val) ⟨(MvPolynomial.X i)^1, ⟨1, rfl⟩⟩) = _
      rw [evalFrac]
      simp [ev, j.property]
  exact Function.LeftInverse.injective (g := r) fun p => DFunLike.congr_fun h p

private theorem polynomialVariables_generate (A : Type u) (I : Type v) [CommRing A] :
    Algebra.adjoin (polyGrading A I 0) (Set.range (MvPolynomial.X (R := A) (σ := I))) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ (polyConstants A I a)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp => exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

private theorem polynomialToChart_surjective (A : Type u) (I : Type v) [CommRing A] [Fintype I] (i : I) :
    Function.Surjective (polynomialToChart A I i) := by
  classical
  let R := polyGrading A I 0
  let G := polyGrading A I
  let S : Subalgebra R (polyChart A I i) :=
    { (polynomialToChart A I i).range with
      algebraMap_mem' := fun r => by
        obtain ⟨a, rfl⟩ := polyConstants_surj A I r
        exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩ }
  have gen := polynomialVariables_generate A I
  have hgen := Away.adjoin_mk_prod_pow_eq_top (𝒜 := G)
    (MvPolynomial.isHomogeneous_X A i) I MvPolynomial.X gen (fun _ => 1)
    (MvPolynomial.isHomogeneous_X A)
  have hS : ⊤ ≤ S := by
    rw [← hgen, Algebra.adjoin_le_iff]
    rintro _ ⟨n, a, hn, _, rfl⟩
    have hd : (∏ j, MvPolynomial.X j ^ a j) ∈ G (n • 1) :=
      hn ▸ SetLike.prod_pow_mem_graded G (fun _ => 1) MvPolynomial.X a
        (fun j _ => MvPolynomial.isHomogeneous_X A j)
    have hp : ∏ j, chartRatio A I i j ^ a j =
        Away.mk G (MvPolynomial.isHomogeneous_X A i) n (∏ j, MvPolynomial.X j ^ a j) hd := by
      apply val_injective
      change (algebraMap (polyChart A I i) (Localization.Away (MvPolynomial.X (R := A) i)))
        (∏ j, chartRatio A I i j ^ a j) = _
      simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply, chartRatio_val,
        Localization.mk_pow, Localization.mk_prod, pow_one]
      change Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := A) i)) _ _ =
        Localization.mk (S := Submonoid.powers (MvPolynomial.X (R := A) i))
          (∏ j, MvPolynomial.X j ^ a j) ⟨(MvPolynomial.X i)^n, ⟨n, rfl⟩⟩
      congr 1
      apply Subtype.ext
      simp only [Submonoid.coe_finsetProd, SubmonoidClass.coe_pow]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      simpa using hn
    rw [← hp]
    exact S.prod_mem fun j _ => S.pow_mem (by
      by_cases h : j = i
      · subst j
        rw [chartRatio_diag]
        exact S.one_mem
      · exact ⟨MvPolynomial.X ⟨j, h⟩, MvPolynomial.eval₂Hom_X' _ _ _⟩) _
  intro f
  exact hS (Set.mem_univ f)

private def polynomialChartEquiv (A : Type u) (I : Type v) [CommRing A] [Fintype I] (i : I) :
    MvPolynomial {j : I // j ≠ i} A ≃+* polyChart A I i :=
  RingEquiv.ofBijective (polynomialToChart A I i)
    ⟨polynomialToChart_injective A I i, polynomialToChart_surjective A I i⟩

private def polynomialChartEquivAt (A : Type u) (I : Type v) [CommRing A] [Fintype I] (i : I)
    {s : MvPolynomial I A} (h : s = MvPolynomial.X i) :
    MvPolynomial {j : I // j ≠ i} A ≃+* Away (polyGrading A I) s :=
  h.symm ▸ polynomialChartEquiv A I i

private theorem polynomialChartEquivAt_C (A : Type u) (I : Type v) [CommRing A] [Fintype I] (i : I)
    {s : MvPolynomial I A} (h : s = MvPolynomial.X i) (a : A) :
    polynomialChartEquivAt A I i h (MvPolynomial.C a) = chartConstants A I s a := by
  subst s
  exact MvPolynomial.eval₂Hom_C _ _ _

private theorem polynomialChartEquivAt_X (A : Type u) (I : Type v) [CommRing A] [Fintype I] (i : I)
    {s : MvPolynomial I A} (h : s = MvPolynomial.X i) (hs : s ∈ polyGrading A I 1)
    (j : {j : I // j ≠ i}) :
    polynomialChartEquivAt A I i h (MvPolynomial.X j) =
      Away.mk (polyGrading A I) hs 1 (MvPolynomial.X j.val)
        (by change MvPolynomial.X _ ∈ polyGrading A I 1; exact MvPolynomial.isHomogeneous_X A j.val) := by
  subst s
  exact MvPolynomial.eval₂Hom_X' _ _ _

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {A B : Type (max u v)} [CommRing A] [CommRing B] {I : Type v}

set_option backward.isDefEq.respectTransparency false in
private theorem chartBaseChange_isPullback (φ : A →+* B) [Fintype I] (i : I) :
    let g := gradedPolynomialMap φ (id : I → I)
    let s := MvPolynomial.X (R := A) i
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map g s)))
      (Spec.map (CommRingCat.ofHom (chartConstants B I (g s))))
      (Spec.map (CommRingCat.ofHom (chartConstants A I s))) (Spec.map (CommRingCat.ofHom φ)) := by
  let g := gradedPolynomialMap φ (id : I → I)
  let s := MvPolynomial.X (R := A) i
  have hX : g s = MvPolynomial.X i := gradedPolynomialMap_X φ id i
  let eA := (polynomialChartEquivAt A I i (s := s) rfl).toCommRingCatIso
  let eB := (polynomialChartEquivAt B I i hX).toCommRingCatIso
  letI : Algebra A B := φ.toAlgebra
  let J := {j : I // j ≠ i}
  have hp := CommRingCat.isPushout_of_isPushout A B (MvPolynomial J A) (MvPolynomial J B)
  apply isPullback_SpecMap_of_isPushout
  refine hp.flip.of_iso (.refl _) eA (.refl _) eB ?_ (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact polynomialChartEquivAt_C A I i rfl a
  · apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change polynomialChartEquivAt B I i hX (MvPolynomial.map φ (MvPolynomial.C a)) =
        Away.map g s (polynomialChartEquivAt A I i rfl (MvPolynomial.C a))
      rw [MvPolynomial.map_C, polynomialChartEquivAt_C, polynomialChartEquivAt_C,
        chartMap_constants]
    · intro j
      change polynomialChartEquivAt B I i hX (MvPolynomial.map φ (MvPolynomial.X j)) =
        Away.map g s (polynomialChartEquivAt A I i rfl (MvPolynomial.X j))
      rw [MvPolynomial.map_X, polynomialChartEquivAt_X _ _ _ hX
        (g.2 (MvPolynomial.isHomogeneous_X A i)), polynomialChartEquivAt_X _ _ _ rfl
        (MvPolynomial.isHomogeneous_X A i), Away.map_mk]
      apply val_injective
      rw [Away.val_mk, Away.val_mk]
      simp [g]
  · simp only [Iso.refl_hom, Category.id_comp]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact polynomialChartEquivAt_C B I i hX b

set_option backward.isDefEq.respectTransparency false in
private theorem polyProjBaseChange_isPullback (φ : A →+* B) (I : Type v) [Fintype I] :
    IsPullback (polyProjMap.{u,v,v} φ (id : I → I) Function.surjective_id) (polyProj B I).hom
      (polyProj A I).hom (Spec.map (CommRingCat.ofHom φ)) := by
  let g := gradedPolynomialMap φ (id : I → I)
  let hg := irrelevant_le_gradedPolynomialMap φ (id : I → I) Function.surjective_id
  let p := Proj.map g hg
  let U := (polyProjCover A I).openCover
  refine Scheme.isPullback_of_openCover p (polyProj B I).hom (polyProj A I).hom _ U
    (fun (i : I) => ?_)
  let s := MvPolynomial.X (R := A) i
  let hs := MvPolynomial.isHomogeneous_X A i
  let j := Proj.awayι (polyGrading B I) (g s) (g.2 hs) Nat.one_pos
  let j' := Proj.awayι (polyGrading A I) s hs Nat.one_pos
  let t := Spec.map (CommRingCat.ofHom (Away.map g s))
  have hj : j ≫ p = t ≫ j' := Proj.awayι_comp_map g hg Nat.one_pos s hs
  have hr : p ⁻¹ᵁ j'.opensRange = j.opensRange := by
    rw [Proj.opensRange_awayι, Proj.opensRange_awayι, Proj.map_preimage_basicOpen]
  let H : IsPullback t j j' p := IsOpenImmersion.isPullback t j j' p hj hr
  have H' : IsPullback t (j ≫ (polyProj B I).hom) (j' ≫ (polyProj A I).hom)
      (Spec.map (CommRingCat.ofHom φ)) := by
    rw [chartToBase, chartToBase]
    exact chartBaseChange_isPullback φ i
  let e : (U.pullback₁ p).X i ≅ _ := (pullbackSymmetry p j') ≪≫ H.isoPullback.symm
  exact H'.of_iso' e (.refl _) (.refl _) (.refl _) (by
    change _ = _ ≫ 𝟙 _
    simp [e, H.isoPullback_inv_fst]
    rfl) (by
    change _ = _ ≫ 𝟙 _
    simp [e]
    rfl) (by simp; rfl) (by simp)

/-- Base change of the arithmetic projective space is the same Proj over the new base. -/
private def arithmeticProjectiveBaseChange {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) :
    projectiveSpace S d ≅ (changeBase φ).obj (projectiveSpace R d) := by
  let h := polyProjBaseChange_isPullback.{u,0} φ (Fin (d + 1))
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- The finite basis coordinates of the field projective space can be
renumbered into the coordinates of the arithmetic projective space. -/
private theorem exists_arithmeticCoordinates {K : Type u} [Field K]
    (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V]
    (x : (Specs.ProjectiveSpaces.projectiveSpace K V).left) :
    ∃ d : ℕ, Nonempty (Specs.ProjectiveSpaces.projectiveSpace K V ≅ projectiveSpace K d) := by
  let n := Module.finrank K V
  let I := ULift.{u} (Fin n)
  have i : I := (polyProjCover.{0,u} K I).openCover.idx x
  let d := n - 1
  have h : n = d + 1 := Nat.eq_add_of_sub_eq (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.zero_lt_of_lt i.down.isLt))) rfl
  let e : I ≃ Fin (d + 1) := Equiv.ulift.trans (finCongr h)
  exact ⟨d, ⟨polyProjRename.{0,u,0} K e⟩⟩

private theorem arithmeticProjectiveProper {R : Type u} [CommRing R] (d : ℕ) :
    IsProper (projectiveSpace R d).hom := by
  let I := Fin (d + 1)
  let P := MvPolynomial I R
  let D := polyGrading R I 0
  have hfin : Algebra.FiniteType D P := by
    classical
    exact ⟨⟨Finset.univ.image MvPolynomial.X, by simpa using polynomialVariables_generate R I⟩⟩
  have hC : Function.Injective (polyConstants R I) := by
    have hleft : Function.LeftInverse
        (fun x : D => MvPolynomial.constantCoeff (x : P)) (polyConstants R I) := by
      intro r
      exact MvPolynomial.constantCoeff_C I r
    exact hleft.injective
  have hIso : IsIso (CommRingCat.ofHom (polyConstants R I)) :=
    (RingEquiv.ofBijective _ ⟨hC, polyConstants_surj R I⟩).toCommRingCatIso.isIso_hom
  change IsProper (Proj.toSpecZero (polyGrading R I) ≫ Spec.map (CommRingCat.ofHom (polyConstants R I)))
  infer_instance

end PolynomialCharts

end ProjectiveComparison


section FlatBaseChangeDetection

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.SpreadProjectiveRightTorsor (rightMultiply)


variable {A B : Type u} [CommRing A] [CommRing B]

/-- A flat scheme is schematically dominated by its base change along an injective ring map. -/
private theorem fibreProjection_dominant (φ : A →+* B) (hφ : Function.Injective φ)
    (X : SchemeOverRing A) [Flat X.hom] :
    IsSchemeTheoreticallyDominant (fibreProjection φ X) := by
  let a := CommRingCat.ofHom φ
  have h : IsSchemeTheoreticallyDominant (Spec.map a) := by
    rw [isSchemeTheoreticallyDominant_iff]
    apply Scheme.IdealSheafData.ext_of_isAffine
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    apply (RingHom.injective_iff_ker_eq_bot _).mp
    have h' := Scheme.ΓSpecIso_naturality a
    have : Function.Injective ((Spec.map a).appTop ≫ (Scheme.ΓSpecIso _).hom) := by
      rw [h']
      exact hφ.comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1
    exact Function.Injective.of_comp this
  have : QuasiCompact (Spec.map a) := inferInstance
  exact inferInstanceAs
    (IsSchemeTheoreticallyDominant (pullback.fst X.hom (Spec.map a)))

/-- Equality of maps from a flat scheme into a separated scheme can be tested after
an injective extension of the base ring. -/
private theorem eq_of_injective_baseChange (κ : A →+* B) (hκ : Function.Injective κ)
    {X Y : SchemeOverRing A} [Flat X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : (changeBase κ).map f = (changeBase κ).map g) : f = g := by
  let X₀ : SchemeOverRing A := Over.mk (fibreProjection κ X ≫ X.hom)
  let p : X₀ ⟶ X := Over.homMk (fibreProjection κ X) rfl
  have hp : p ≫ f = p ≫ g := by
    apply Over.OverMorphism.ext
    change fibreProjection κ X ≫ f.left = fibreProjection κ X ≫ g.left
    rw [← (changeBaseMap_isPullback κ f).w, ← (changeBaseMap_isPullback κ g).w, h]
  let r := equalizer.ι f g
  let a := equalizer.lift p hp
  have ha : a.left ≫ r.left = fibreProjection κ X := congrArg (fun l => l.left)
    (equalizer.lift_ι p hp)
  have hz : r.left.ker = ⊥ := by
    apply bot_unique
    rw [← (fibreProjection_dominant κ hκ X).ker_eq_bot, ← ha]
    exact a.left.le_ker_comp r.left
  have : IsIso r.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hz
  apply Over.OverMorphism.ext
  apply (cancel_epi r.left).mp
  exact congrArg (fun l => l.left) (equalizer.condition f g)

end FlatBaseChangeDetection

section GenericKernelPair

variable {A K : Type u} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsDomain A]

/-- A map from a flat scheme factors through a closed subscheme as soon as
the map on its generic fibre factors through the generic closed subscheme. -/
private theorem factors_of_generic_fibre {X H G : SchemeOverRing A}
    [Flat X.hom] (i : H ⟶ G) [IsClosedImmersion i.left] (f : X ⟶ G)
    (d : (changeBase (algebraMap A K)).obj X ⟶ (changeBase (algebraMap A K)).obj H)
    (hd : d ≫ (changeBase (algebraMap A K)).map i = (changeBase (algebraMap A K)).map f) :
    ∃ b : X ⟶ H, b ≫ i = f := by
  let κ := algebraMap A K
  have he : (d.left ≫ fibreProjection κ H) ≫ i.left = fibreProjection κ X ≫ f.left := by
    rw [Category.assoc, ← (changeBaseMap_isPullback κ i).w, ← Category.assoc,
      ← Over.comp_left, hd, (changeBaseMap_isPullback κ f).w]
  have hk : i.left.ker ≤ f.left.ker := by
    have hker := (d.left ≫ fibreProjection κ H).le_ker_comp i.left
    rw [he, Scheme.Hom.ker_comp, (fibreProjection_dominant κ (IsFractionRing.injective A K) X).ker_eq_bot,
      Scheme.IdealSheafData.map_bot] at hker
    exact hker
  let b := IsClosedImmersion.lift i.left f.left hk
  refine ⟨Over.homMk b ?_, ?_⟩
  · rw [← Over.w i, ← Category.assoc, IsClosedImmersion.lift_fac, Over.w f]
  · apply Over.OverMorphism.ext
    exact IsClosedImmersion.lift_fac _ _ _

/-- Recover the entire right kernel pair on a smooth model from the generic
right kernel pair, using flatness of the two domains where equations are tested. -/
private theorem kernelPair_of_generic {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    [IsClosedImmersion i.hom.hom.left] [Flat G.X.hom] [Flat H.X.hom]
    {Y : SchemeOverRing A} [IsSeparated Y.hom] (q : G.X ⟶ Y) [Smooth q.left]
    (h : IsPullback prod.fst (rightMultiply (((changeBase (algebraMap A K)).mapGrp).map i))
      ((changeBase (algebraMap A K)).map q) ((changeBase (algebraMap A K)).map q)) :
    IsPullback prod.fst (rightMultiply i) q q := by
  let F := changeBase (algebraMap A K)
  have : Mono i.hom.hom :=
    (Over.forget _).mono_of_mono_map (f := i.hom.hom) (by
      change Mono i.hom.hom.left
      infer_instance)
  have hp : Flat (G.X ⨯ H.X).hom := by
    rw [← Over.w (Limits.prod.fst : G.X ⨯ H.X ⟶ G.X)]
    have : Flat (Limits.prod.fst : G.X ⨯ H.X ⟶ G.X).left := by
      let e := Over.prodLeftIsoPullback G.X H.X
      rw [← Over.prodLeftIsoPullback_hom_fst]
      infer_instance
    infer_instance
  refine (rightKernelPair_iff_difference i q).mpr ⟨?_, ?_⟩
  · apply eq_of_injective_baseChange (algebraMap A K) (IsFractionRing.injective A K)
    change F.map (prod.fst ≫ q) = F.map (rightMultiply i ≫ q)
    simp only [Functor.map_comp]
    let e := PreservesLimitPair.iso F G.X H.X
    apply (cancel_epi e.inv).mp
    have hf : e.inv ≫ F.map prod.fst = prod.fst := PreservesLimitPair.iso_inv_fst F G.X H.X
    have hs : e.inv ≫ F.map prod.snd = prod.snd := PreservesLimitPair.iso_inv_snd F G.X H.X
    have hm : e.inv ≫ F.map (rightMultiply i) = rightMultiply (F.mapGrp.map i) := by
      change e.inv ≫ F.map (prod.fst * (prod.snd ≫ i.hom.hom)) = _
      simp only [F.map_mul, F.map_comp, MonObj.comp_mul, ← Category.assoc, hf, hs]
      rfl
    rw [← Category.assoc, ← Category.assoc, hf, hm]
    exact h.w
  · have hW : Flat (pullback q q).hom := by
      have hh := (IsPullback.of_hasPullback q q).map (Over.forget _)
      have hp : Smooth (pullback.fst q q).left := MorphismProperty.of_isPullback hh.flip ‹_›
      rw [← Over.w (pullback.fst q q)]
      infer_instance
    let b := (pullback.fst q q)⁻¹ * pullback.snd q q
    let hp := F.map_isPullback (IsPullback.of_hasPullback q q)
    obtain ⟨d, hd⟩ := quotient_difference h (F.map (pullback.fst q q))
      (F.map (pullback.snd q q)) hp.w
    refine factors_of_generic_fibre (K := K) i.hom.hom b d ?_
    change d ≫ (F.mapGrp.map i).hom.hom = F.map ((pullback.fst q q)⁻¹ * pullback.snd q q)
    rw [F.map_mul, F.map_inv']
    exact (eq_inv_mul_iff_mul_eq).mpr hd

end GenericKernelPair


section Transport

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.SpreadProjectiveRightTorsor (rightMultiply HasLocalSections changeBaseComp)

variable {A : Type u} [CommRing A]

private abbrev groupIsoUnderlying {G G' : Grp (SchemeOverRing A)} (e : G ≅ G') :
    G.X ≅ G'.X := (Grp.forget _).mapIso e

private theorem kernelPair_transport {G H G' H' : Grp (SchemeOverRing A)}
    (i : H ⟶ G) (i' : H' ⟶ G') (eG : G ≅ G') (eH : H ≅ H')
    (he : i ≫ eG.hom = eH.hom ≫ i')
    {Y Y' : SchemeOverRing A} (eY : Y ≅ Y') (q : G.X ⟶ Y) (q' : G'.X ⟶ Y')
    (hq : q ≫ eY.hom = (groupIsoUnderlying eG).hom ≫ q')
    (h : IsPullback prod.fst (rightMultiply i) q q) :
    IsPullback prod.fst (rightMultiply i') q' q' := by
  let a := groupIsoUnderlying eG
  let b := groupIsoUnderlying eH
  let e := prod.mapIso a b
  refine h.of_iso e a a eY (prod.map_fst _ _).symm ?_ hq hq
  change (prod.fst * (prod.snd ≫ i.hom.hom)) ≫ a.hom =
    prod.map a.hom b.hom ≫ (prod.fst * (prod.snd ≫ i'.hom.hom))
  have : IsMonHom a.hom := eG.hom.hom.isMonHom_hom
  have hh : i.hom.hom ≫ a.hom = b.hom ≫ i'.hom.hom :=
    congrArg (fun f => f.hom.hom) he
  rw [MonObj.mul_comp, MonObj.comp_mul, prod.map_fst, prod.map_snd_assoc, Category.assoc, hh]

private theorem localSections_transport {X X' Y Y' : SchemeOverRing A}
    (eX : X ≅ X') (eY : Y ≅ Y') (q : X ⟶ Y) (q' : X' ⟶ Y')
    (hq : q ≫ eY.hom = eX.hom ≫ q') (h : HasLocalSections q) : HasLocalSections q' := by
  intro y
  obtain ⟨U, j, s, hj, ⟨x, hx⟩, hs⟩ := h (eY.inv.left y)
  refine ⟨U, j ≫ eY.hom, s ≫ eX.hom, ?_, ⟨x, ?_⟩, ?_⟩
  · change IsOpenImmersion (j.left ≫ eY.hom.left)
    infer_instance
  · change eY.hom.left (j.left x) = y
    rw [hx]
    exact congrArg (fun f : Y' ⟶ Y' => f.left y) eY.inv_hom_id
  · rw [Category.assoc, ← hq, ← Category.assoc, hs]

private theorem morphismProperty_transport (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X X' Y Y' : SchemeOverRing A} (eX : X ≅ X') (eY : Y ≅ Y')
    (q : X ⟶ Y) (q' : X' ⟶ Y') (h : q ≫ eY.hom = eX.hom ≫ q') :
    P q.left ↔ P q'.left := by
  have h' : q.left ≫ eY.hom.left = eX.hom.left ≫ q'.left :=
    congrArg (fun f => f.left) h
  rw [← MorphismProperty.cancel_right_of_respectsIso P q.left eY.hom.left, h',
    MorphismProperty.cancel_left_of_respectsIso P eX.hom.left q'.left]

variable {B C : Type u} [CommRing B] [CommRing C]

private theorem baseChange_morphismProperty (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (φ : A →+* B) {X Y : SchemeOverRing A}
    (q : X ⟶ Y) (hq : P q.left) :
    P ((changeBase φ).map q).left :=
  MorphismProperty.of_isPullback (changeBaseMap_isPullback φ q).flip hq

private theorem baseChange_structureProperty (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] (φ : A →+* B) (X : SchemeOverRing A) (hX : P X.hom) :
    P ((changeBase φ).obj X).hom :=
  MorphismProperty.pullback_snd _ _ hX

private theorem structureProperty_transport (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X X' : SchemeOverRing A} (e : X ≅ X') :
    P X.hom ↔ P X'.hom := by
  rw [← Over.w e.hom, MorphismProperty.cancel_left_of_respectsIso P e.hom.left X'.hom]

end Transport


section ArithmeticBase

open Specs.ArithmeticProjectiveFiniteness (BaseRing)
open Specs.SpreadProjectiveRightTorsor (rationalMap)


private theorem liftedIntegers_domain : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).injective.isDomain (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)

private theorem arithmeticBase_isDomain (m : ℕ) (hm : m ≠ 0) :
    IsDomain (BaseRing.{u} m) := by
  have := liftedIntegers_domain.{u}
  apply Localization.Away.isDomain
  intro hz
  exact Int.natCast_ne_zero.mpr hm (congrArg ULift.down hz)

private theorem arithmeticBase_isNoetherian (m : ℕ) : IsNoetherianRing (BaseRing.{u} m) := by
  have : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  infer_instance

/-- Identify the specified rational map with the fraction map using the
fraction-field property of the integers and invariance under localization. -/
private theorem arithmeticGeneric_isFractionRing (m : ℕ) (hm : m ≠ 0) :
    letI : Algebra (BaseRing.{u} m) (ULift.{u} ℚ) := (rationalMap hm).toAlgebra
    IsFractionRing (BaseRing.{u} m) (ULift.{u} ℚ) := by
  let R := ULift.{u} ℤ
  let A := BaseRing.{u} m
  let K := ULift.{u} ℚ
  let r := (algebraMap ℤ ℚ).comp (ULift.ringEquiv : R ≃+* ℤ).toRingHom
  letI : Algebra R ℚ := r.toAlgebra
  have hR : IsFractionRing R ℚ :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
      (S := ℚ) (ULift.ringEquiv.symm : ℤ ≃+* R)).mp Rat.isFractionRing
  let e : ℚ ≃+* K := ULift.ringEquiv.symm
  let algRK : Algebra R K := (e.toRingHom.comp r).toAlgebra
  letI : Algebra R K := algRK
  have hRK : IsFractionRing R K :=
    (IsLocalization.isLocalization_iff_of_ringEquiv (nonZeroDivisors R) e).mp hR
  let algAK : Algebra A K := (rationalMap hm).toAlgebra
  let algRA : Algebra R A := inferInstance
  letI : Algebra A K := algAK
  have hcomp : (algebraMap A K).comp (algebraMap R A) = algebraMap R K :=
    liftedIntegerHom_unique _ _
  have hTower : @IsScalarTower R A K algRA.toSMul algAK.toSMul algRK.toSMul :=
    @IsScalarTower.of_algebraMap_eq' R A K _ _ _ algRA algAK algRK hcomp.symm
  exact @IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    R _ (Submonoid.powers (m : R)) liftedIntegers_domain A K _ _ algRA algRK algAK hTower inferInstance hRK

end ArithmeticBase


section BaseChangeComparison

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.SpreadProjectiveRightTorsor (changeBaseComp)


variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

@[reassoc] private theorem changeBaseAlongComp_hom_projections
    (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C} (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    ((changeBaseAlongComp φ ψ h).hom.app X).left ≫
      fibreProjection ψ ((changeBase φ).obj X) ≫ fibreProjection φ X =
        fibreProjection κ X := by
  subst κ
  let b := Spec.map (CommRingCat.ofHom φ)
  let c := Spec.map (CommRingCat.ofHom ψ)
  change (𝟙 _ ≫ ((changeBaseComp φ ψ).hom.app X)).left ≫
    pullback.fst (pullback.snd X.hom b) c ≫ pullback.fst X.hom b = _
  rw [Category.id_comp]
  change (_ ≫ (pullbackLeftPullbackSndIso X.hom b c).inv) ≫
    pullback.fst (pullback.snd X.hom b) c ≫ pullback.fst X.hom b = _
  simp [b, c]
  rfl

private theorem changeBaseAlongComp_inv_projections
    (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C} (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    ((changeBaseAlongComp φ ψ h).inv.app X).left ≫ fibreProjection κ X =
      fibreProjection ψ ((changeBase φ).obj X) ≫ fibreProjection φ X := by
  let e := (changeBaseAlongComp φ ψ h).app X
  have hh := changeBaseAlongComp_hom_projections φ ψ h X
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ :=
    congrArg (fun f => f.left) e.inv_hom_id
  calc
    _ = e.inv.left ≫ (e.hom.left ≫ fibreProjection ψ ((changeBase φ).obj X) ≫
        fibreProjection φ X) := congrArg (e.inv.left ≫ ·) hh.symm
    _ = _ := by rw [← Category.assoc, he, Category.id_comp]

@[reassoc] private theorem map_fibreProjection (φ : A →+* B) {X Y : SchemeOverRing A} (f : X ⟶ Y) :
    ((changeBase φ).map f).left ≫ fibreProjection φ Y = fibreProjection φ X ≫ f.left :=
  (changeBaseMap_isPullback φ f).w

private theorem eq_of_fibreProjection (φ : A →+* B)
    {X : SchemeOverRing B} {Y : SchemeOverRing A} (f g : X ⟶ (changeBase φ).obj Y)
    (h : f.left ≫ fibreProjection φ Y = g.left ≫ fibreProjection φ Y) : f = g := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w f).trans (Over.w g).symm

private theorem eq_of_iterated_fibreProjection (φ : A →+* B) (ψ : B →+* C)
    {X : SchemeOverRing C} {Y : SchemeOverRing A} (f g : X ⟶ (changeBase ψ).obj ((changeBase φ).obj Y))
    (h : f.left ≫ fibreProjection ψ _ ≫ fibreProjection φ Y =
      g.left ≫ fibreProjection ψ _ ≫ fibreProjection φ Y) : f = g := by
  apply eq_of_fibreProjection ψ
  apply pullback.hom_ext
  · simpa only [Category.assoc] using h
  · change (f.left ≫ fibreProjection ψ ((changeBase φ).obj Y)) ≫ ((changeBase φ).obj Y).hom =
        (g.left ≫ fibreProjection ψ ((changeBase φ).obj Y)) ≫ ((changeBase φ).obj Y).hom
    rw [Category.assoc, Category.assoc, fibreProjection_over ψ,
      ← Category.assoc, ← Category.assoc, Over.w f, Over.w g]

private theorem localizationComparison_comp (M : Submonoid A) (K : Type u) [CommRing K]
    [Algebra A K] [IsLocalization M K] (a : M) :
    (localizationComparison M K ⟨a⟩).comp (algebraMap A (Localization.Away (a : A))) =
      algebraMap A K :=
  RingHom.ext fun t => localizationComparison_algebraMap M K ⟨a⟩ t


/-- A finite-stage map agrees with a given map after the canonical change of base. -/
private structure ProjectionCompatibility (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C}
    (h : ψ.comp φ = κ) {X Y : SchemeOverRing A}
    (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (q : (changeBase κ).obj X ⟶ (changeBase κ).obj Y) : Prop where
  comm : (changeBaseAlongComp φ ψ h).hom.app X ≫ (changeBase ψ).map p =
    q ≫ (changeBaseAlongComp φ ψ h).hom.app Y

end BaseChangeComparison


section LocalSections

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.SpreadProjectiveRightTorsor (changeBaseComp HasLocalSections)

variable {A B : Type u} [CommRing A] [CommRing B]

private theorem changeBase_openSections (φ : A →+* B) {X Y : SchemeOverRing A}
    (q : X ⟶ Y) (h : HasLocalSections q) : HasLocalSections ((changeBase φ).map q) := by
  intro y
  obtain ⟨U, j, s, hj, hy, hs⟩ := h (fibreProjection φ Y y)
  refine ⟨_, (changeBase φ).map j, (changeBase φ).map s,
    MorphismProperty.of_isPullback (changeBaseMap_isPullback φ j).flip hj, ?_, ?_⟩
  · rw [range_changeBaseMap]
    exact hy
  · rw [← Functor.map_comp, hs]

private theorem surjective_of_localSections {X Y : SchemeOverRing A} (q : X ⟶ Y)
    (h : HasLocalSections q) : Surjective q.left := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, j, s, hj, ⟨x, rfl⟩, hs⟩ := h y
  refine ⟨s.left x, ?_⟩
  exact congrArg (fun f : U ⟶ Y => f.left x) hs

private abbrev overOpen (Y : SchemeOverRing A) (U : Y.left.Opens) : SchemeOverRing A :=
  Over.mk (U.ι ≫ Y.hom)

private abbrev overOpenι (Y : SchemeOverRing A) (U : Y.left.Opens) : overOpen Y U ⟶ Y :=
  Over.homMk U.ι rfl

variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [IsDomain A]

/-- Around each generic point a section can be taken on the pullback of
an affine open of the original target. -/
private theorem affineNeighborhoodSection {X Y : SchemeOverRing A} (q : X ⟶ Y)
    (h : HasLocalSections ((changeBase (algebraMap A K)).map q))
    (y : ((changeBase (algebraMap A K)).obj Y).left) :
    ∃ (U : Y.left.affineOpens),
      fibreProjection (algebraMap A K) Y y ∈ U.val ∧
      ∃ s : (changeBase (algebraMap A K)).obj (overOpen Y U.val) ⟶
          (changeBase (algebraMap A K)).obj X,
        s ≫ (changeBase (algebraMap A K)).map q =
          (changeBase (algebraMap A K)).map (overOpenι Y U.val) := by
  let F := changeBase (algebraMap A K)
  let p := fibreProjection (algebraMap A K) Y
  have hp : IsPreimmersion p := by
    have h : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors A)
    exact inferInstanceAs (IsPreimmersion
      (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A K)))))
  obtain ⟨V, j, s, hj, hy, hs⟩ := h y
  have hB := p.isEmbedding.isInducing.isTopologicalBasis Y.left.isBasis_affineOpens
  obtain ⟨_, ⟨_, ⟨U, hU, rfl⟩, rfl⟩, hyU, hUj⟩ :=
    hB.exists_subset_of_mem_open (show y ∈ (j.left.opensRange : Set _) from hy)
      j.left.opensRange.isOpen
  let j' := F.map (overOpenι Y U)
  have hj' : Set.range j'.left ⊆ Set.range j.left := by
    rw [range_changeBaseMap]
    have hU' : Set.range (overOpenι Y U).left = (U : Set Y.left) :=
      Scheme.Opens.range_ι (show Y.left.Opens from U)
    rw [hU']
    exact hUj
  let r : (F.obj (overOpen Y U)).left ⟶ V.left := IsOpenImmersion.lift j.left j'.left hj'
  have hr : r ≫ j.left = j'.left := IsOpenImmersion.lift_fac _ _ _
  let rr : F.obj (overOpen Y U) ⟶ V := Over.homMk r (by
    rw [← Over.w j, ← Category.assoc, hr, Over.w j'])
  have hrr : rr ≫ j = j' := Over.OverMorphism.ext hr
  exact ⟨⟨U, hU⟩, hyU, rr ≫ s, by rw [Category.assoc, hs, hrr]⟩

private theorem localization_isFractionRing (a : nonZeroDivisors A) :
    letI : Algebra (Localization.Away (a : A)) K :=
      (localizationComparison (nonZeroDivisors A) K ⟨a⟩).toAlgebra
    IsFractionRing (Localization.Away (a : A)) K := by
  let D := Localization.Away (a : A)
  letI : Algebra D K := (localizationComparison (nonZeroDivisors A) K ⟨a⟩).toAlgebra
  letI : IsScalarTower A D K :=
    IsScalarTower.of_algebraMap_eq' (localizationComparison_comp (nonZeroDivisors A) K a).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (a : A)) D K


end LocalSections


section ProjectiveModel

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase)
open Specs.ArithmeticProjectiveFiniteness (projectiveSpace)

/-- Close the given field model in the same coordinate projective space
over the base, with its original generic embedding recovered. -/
private theorem exists_projective_model {R K : Type u} [CommRing R] [Field K]
    (M : Submonoid R) [Algebra R K] [IsLocalization M K]
    {Y : SchemeOverRing K} (y : Y.left)
    (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V]
    (j : Y ⟶ Specs.ProjectiveSpaces.projectiveSpace K V) (hj : IsClosedImmersion j.left) :
    ∃ (d : ℕ) (Y₀ : SchemeOverRing R) (j₀ : Y₀ ⟶ projectiveSpace R d),
      IsClosedImmersion j₀.left ∧ IsProper Y₀.hom ∧
      ∃ (eP : Specs.ProjectiveSpaces.projectiveSpace K V ≅ projectiveSpace K d)
        (eY : Y ≅ (changeBase (algebraMap R K)).obj Y₀),
        eY.hom ≫ (changeBase (algebraMap R K)).map j₀ =
          j ≫ eP.hom ≫ (arithmeticProjectiveBaseChange (algebraMap R K) d).hom := by
  obtain ⟨d, ⟨eP⟩⟩ := exists_arithmeticCoordinates V (j.left y)
  let κ := algebraMap R K
  let p := arithmeticProjectiveBaseChange κ d
  let jκ := j ≫ eP.hom ≫ p.hom
  have hjκ : IsClosedImmersion jκ.left := by
    change IsClosedImmersion (j.left ≫ eP.hom.left ≫ p.hom.left)
    infer_instance
  obtain ⟨Y₀, j₀, hj₀, eY, heY⟩ := exists_closed_model_of_localization M jκ hjκ
  refine ⟨d, Y₀, j₀, hj₀, ?_, eP, eY, heY⟩
  have hP := arithmeticProjectiveProper (R := R) d
  rw [← Over.w j₀]
  infer_instance

end ProjectiveModel


section ProjectionComparison

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.SpreadProjectiveRightTorsor (changeBaseComp)

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 300000 in
private theorem descendMorphismWithProjection
    (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C} (he : ψ.comp φ = κ)
    {X Y : SchemeOverRing A} (f : (changeBase κ).obj X ⟶ (changeBase κ).obj Y)
    (g0 : pullback (Spec.map (CommRingCat.ofHom φ)) X.hom ⟶ Y.left)
    (hgY : g0 ≫ Y.hom = pullback.snd (Spec.map (CommRingCat.ofHom φ)) X.hom ≫ X.hom)
    (de : pullback (Spec.map (CommRingCat.ofHom κ)) X.hom ⟶
      pullback (Spec.map (CommRingCat.ofHom φ)) X.hom)
    (hde1 : de ≫ pullback.fst (Spec.map (CommRingCat.ofHom φ)) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom κ)) X.hom ≫ Spec.map (CommRingCat.ofHom ψ))
    (hde2 : de ≫ pullback.snd (Spec.map (CommRingCat.ofHom φ)) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom κ)) X.hom)
    (hg0 : de ≫ g0 = (pullbackSymmetry (Spec.map (CommRingCat.ofHom κ)) X.hom).hom ≫
        f.left ≫ fibreProjection κ Y) :
    ∃ g : (changeBase φ).obj X ⟶ (changeBase φ).obj Y,
      ((changeBaseAlongComp φ ψ he).hom.app X).left ≫ fibreProjection ψ ((changeBase φ).obj X) ≫
        g.left ≫ fibreProjection φ Y = f.left ≫ fibreProjection κ Y := by
  let e := changeBaseAlongComp φ ψ he
  let ba := Spec.map (CommRingCat.ofHom φ)
  let b := Spec.map (CommRingCat.ofHom κ)
  let t := Spec.map (CommRingCat.ofHom ψ)
  let e0 := pullbackSymmetry b X.hom
  let ea := pullbackSymmetry X.hom ba
  let f0 := e0.hom ≫ f.left ≫ fibreProjection κ Y
  let g₁ := ea.hom ≫ g0
  have hg₁ : g₁ ≫ Y.hom = ((changeBase φ).obj X).hom ≫ ba := by
    change ea.hom ≫ g0 ≫ Y.hom = _
    rw [hgY, ← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback.condition
  let g : (changeBase φ).obj X ⟶ (changeBase φ).obj Y :=
    Over.homMk (pullback.lift g₁ ((changeBase φ).obj X).hom hg₁)
      (pullback.lift_snd _ _ _)
  let p := fibreProjection ψ ((changeBase φ).obj X)
  let ex := (e.hom.app X).left
  have hπ : ex ≫ p ≫ ea.hom = e0.inv ≫ de := by
    apply pullback.hom_ext
    · have ha : ea.hom ≫ pullback.fst ba X.hom = ((changeBase φ).obj X).hom :=
        pullbackSymmetry_hom_comp_fst X.hom ba
      have hd : de ≫ pullback.fst ba X.hom = pullback.fst b X.hom ≫ t := hde1
      simp only [Category.assoc]
      rw [ha, hd, fibreProjection_over ψ, ← Category.assoc ex]
      have hw : ex ≫ ((changeBase ψ).obj ((changeBase φ).obj X)).hom =
          ((changeBase κ).obj X).hom := Over.w (e.hom.app X)
      rw [hw, ← Category.assoc e0.inv]
      exact congrArg (· ≫ t) (pullbackSymmetry_inv_comp_fst b X.hom).symm
    · have ha : ea.hom ≫ pullback.snd ba X.hom = fibreProjection φ X :=
        pullbackSymmetry_hom_comp_snd X.hom ba
      have hd : de ≫ pullback.snd ba X.hom = pullback.snd b X.hom := hde2
      simp only [Category.assoc]
      rw [ha, hd]
      exact (changeBaseAlongComp_hom_projections φ ψ he X).trans
        (pullbackSymmetry_inv_comp_snd b X.hom).symm
  refine ⟨g, ?_⟩
  have hg₁' : g.left ≫ fibreProjection φ Y = ea.hom ≫ g0 :=
    pullback.lift_fst g₁ ((changeBase φ).obj X).hom hg₁
  change ex ≫ p ≫ g.left ≫ fibreProjection φ Y = _
  calc
    _ = ex ≫ p ≫ ea.hom ≫ g0 := congrArg (fun k => ex ≫ p ≫ k) hg₁'
    _ = (ex ≫ p ≫ ea.hom) ≫ g0 := by simp only [Category.assoc]
    _ = (e0.inv ≫ de) ≫ g0 := congrArg (· ≫ g0) hπ
    _ = _ := by
      rw [Category.assoc, hg0]
      change e0.inv ≫ e0.hom ≫ f.left ≫ fibreProjection κ Y = _
      rw [Iso.inv_hom_id_assoc]


end ProjectionComparison


section ArithmeticRefinement

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase)
open Specs.ArithmeticProjectiveFiniteness (BaseRing)
open Specs.SpreadProjectiveRightTorsor (rationalMap)

private theorem exists_arithmetic_refinement {m : ℕ} (hm : m ≠ 0) (a : BaseRing.{u} m)
    (ha : a ≠ 0) :
    ∃ (n : ℕ) (hn : n ≠ 0), m ∣ n ∧
      ∃ e : Localization.Away a ≃+* BaseRing.{u} n,
        let φ := e.toRingHom.comp (algebraMap (BaseRing.{u} m) (Localization.Away a))
        let κ := rationalMap hm
        letI : Algebra (BaseRing.{u} m) (ULift.{u} ℚ) := κ.toAlgebra
        letI : IsDomain (BaseRing.{u} m) := arithmeticBase_isDomain m hm
        letI : IsFractionRing (BaseRing.{u} m) (ULift.{u} ℚ) := arithmeticGeneric_isFractionRing m hm
        let ψ := localizationComparison (nonZeroDivisors (BaseRing.{u} m)) (ULift.{u} ℚ)
          ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩⟩
        φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
          algebraMap (ULift.{u} ℤ) (BaseRing.{u} n) ∧
        (rationalMap hn).comp φ = rationalMap hm ∧
        (rationalMap hn).comp e.toRingHom = ψ := by
  let A := BaseRing.{u} m
  let B := Localization.Away a
  let κ := rationalMap hm
  letI : Algebra A (ULift.{u} ℚ) := κ.toAlgebra
  letI : IsDomain A := arithmeticBase_isDomain m hm
  letI : IsFractionRing A (ULift.{u} ℚ) := arithmeticGeneric_isFractionRing m hm
  obtain ⟨n, hn, hmn, e, he⟩ := refineArithmeticBase hm a ha
  let φ := e.toRingHom.comp (algebraMap A B)
  have hφ : φ.comp (algebraMap (ULift.{u} ℤ) A) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} n) := by
    change (e.toRingHom.comp (algebraMap A B)).comp (algebraMap (ULift.{u} ℤ) A) = _
    rw [RingHom.comp_assoc]
    exact he
  have hη := rationalMap_comp_refinement hm hn φ hφ
  refine ⟨n, hn, hmn, e, hφ, hη, ?_⟩
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  rw [RingHom.comp_assoc, hη]
  exact (localizationComparison_comp (nonZeroDivisors A) (ULift.{u} ℚ)
    ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩).symm

end ArithmeticRefinement


section GenericProjectionComparison

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.SpreadProjectiveRightTorsor (changeBaseComp)

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

private theorem map_eq_of_projection_eq
    (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C} (he : ψ.comp φ = κ)
    {X Y : SchemeOverRing A} (f : (changeBase κ).obj X ⟶ (changeBase κ).obj Y)
    (g : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (h : ((changeBaseAlongComp φ ψ he).hom.app X).left ≫
      fibreProjection ψ ((changeBase φ).obj X) ≫ g.left ≫ fibreProjection φ Y =
        f.left ≫ fibreProjection κ Y) :
    (changeBaseAlongComp φ ψ he).hom.app X ≫ (changeBase ψ).map g =
      f ≫ (changeBaseAlongComp φ ψ he).hom.app Y := by
  let e := changeBaseAlongComp φ ψ he
  let U := e.hom.app X ≫ (changeBase ψ).map g
  let V := f ≫ e.hom.app Y
  let p := fibreProjection ψ ((changeBase φ).obj X)
  let p' := fibreProjection ψ ((changeBase φ).obj Y)
  let r := fibreProjection φ Y
  let x := (e.hom.app X).left
  let gy := ((changeBase ψ).map g).left
  have hm : gy ≫ p' = p ≫ g.left := (changeBaseMap_isPullback ψ g).w
  have hU : U.left ≫ p' ≫ r = f.left ≫ fibreProjection κ Y := by
    change (x ≫ gy) ≫ p' ≫ r = _
    calc
      _ = x ≫ (gy ≫ p') ≫ r := by simp only [Category.assoc]
      _ = x ≫ (p ≫ g.left) ≫ r := congrArg (fun k => x ≫ k ≫ r) hm
      _ = x ≫ p ≫ g.left ≫ r := by simp only [Category.assoc]
      _ = _ := h
  have hV : V.left ≫ p' ≫ r = f.left ≫ fibreProjection κ Y := by
    change (f.left ≫ (e.hom.app Y).left) ≫ p' ≫ r = _
    exact (Category.assoc _ _ _).trans
      (congrArg (f.left ≫ ·) (changeBaseAlongComp_hom_projections φ ψ he Y))
  exact eq_of_iterated_fibreProjection φ ψ U V (hU.trans hV.symm)


end GenericProjectionComparison


section LocalizationProjections

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.SpreadProjectiveRightTorsor (changeBaseComp)

variable {A B : Type u} [CommRing A] [CommRing B]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_map_from_localized_pullback (M : Submonoid A) (K : Type u)
    [CommRing K] [Algebra A K] [IsLocalization M K] {X Y : SchemeOverRing A}
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [LocallyOfFinitePresentation Y.hom]
    (f : pullback (Spec.map (CommRingCat.ofHom (algebraMap A K))) X.hom ⟶ Y.left)
    (hf : f ≫ Y.hom = pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A K))) X.hom ≫ X.hom) :
    ∃ a : (Denominator M)ᵒᵖ,
      let φ := algebraMap A (Localization.Away (a.unop.val : A))
      let ψ := localizationComparison M K a.unop
      let b := Spec.map (CommRingCat.ofHom (algebraMap A K))
      let ba := Spec.map (CommRingCat.ofHom φ)
      ∃ (g : pullback ba X.hom ⟶ Y.left) (p : pullback b X.hom ⟶ pullback ba X.hom),
        p ≫ pullback.fst ba X.hom = pullback.fst b X.hom ≫ Spec.map (CommRingCat.ofHom ψ) ∧
        p ≫ pullback.snd ba X.hom = pullback.snd b X.hom ∧
        p ≫ g = f ∧ g ≫ Y.hom = pullback.snd ba X.hom ≫ X.hom := by
  obtain ⟨a, g, hg, hg'⟩ := exists_morphism_of_principalRestriction M K X Y.hom f hf
  let c := principalRestrictionCone M K X
  exact ⟨a, g, (c.π.app a).left, pullback.lift_fst _ _ _, Over.w (c.π.app a), hg, hg'⟩

private theorem domainChangeBase_over {X Y : SchemeOverRing A} (κ : A →+* B)
    (f : (changeBase κ).obj X ⟶ (changeBase κ).obj Y) :
    ((pullbackSymmetry (Spec.map (CommRingCat.ofHom κ)) X.hom).hom ≫
      f.left ≫ fibreProjection κ Y) ≫ Y.hom =
        pullback.snd (Spec.map (CommRingCat.ofHom κ)) X.hom ≫ X.hom := by
  let b := Spec.map (CommRingCat.ofHom κ)
  let e0 := pullbackSymmetry b X.hom
  have he0 : e0.hom ≫ fibreProjection κ X = pullback.snd b X.hom :=
    pullbackSymmetry_hom_comp_fst b X.hom
  change (e0.hom ≫ f.left ≫ fibreProjection κ Y) ≫ Y.hom = _
  rw [Category.assoc, Category.assoc, fibreProjection_over κ Y, Over.w_assoc,
    ← fibreProjection_over κ X, ← Category.assoc, he0]


end LocalizationProjections


section ProjectionDescent

variable {A : Type u} [CommRing A]

set_option backward.isDefEq.respectTransparency false in
private theorem descendAtPrincipalStage (M : Submonoid A) (K : Type u)
    [CommRing K] [Algebra A K] [IsLocalization M K] {X Y : SchemeOverRing A}
    (f : (changeBase (algebraMap A K)).obj X ⟶ (changeBase (algebraMap A K)).obj Y)
    (a : M)
    (g : pullback (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (a : A)))))
      X.hom ⟶ Y.left)
    (p : pullback (Spec.map (CommRingCat.ofHom (algebraMap A K))) X.hom ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (a : A))))) X.hom)
    (h₁ : p ≫ pullback.fst _ _ = pullback.fst _ _ ≫
      Spec.map (CommRingCat.ofHom (localizationComparison M K ⟨a⟩)))
    (h₂ : p ≫ pullback.snd _ _ = pullback.snd _ _)
    (hg : p ≫ g = (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap A K))) X.hom).hom ≫
      f.left ≫ fibreProjection (algebraMap A K) Y)
    (hgY : g ≫ Y.hom = pullback.snd _ _ ≫ X.hom) :
    let φ := algebraMap A (Localization.Away (a : A))
    let ψ := localizationComparison M K ⟨a⟩
    let e := changeBaseAlongComp φ ψ (localizationComparison_comp M K a)
    ∃ g' : (changeBase φ).obj X ⟶ (changeBase φ).obj Y,
      e.hom.app X ≫ (changeBase ψ).map g' = f ≫ e.hom.app Y := by
  dsimp only
  obtain ⟨g', hg'⟩ := descendMorphismWithProjection
    (algebraMap A (Localization.Away (a : A))) (localizationComparison M K ⟨a⟩)
    (localizationComparison_comp M K a) f g hgY p h₁ h₂ hg
  exact ⟨g', map_eq_of_projection_eq
    (algebraMap A (Localization.Away (a : A))) (localizationComparison M K ⟨a⟩)
    (localizationComparison_comp M K a) f g' hg'⟩

/-- A map in the slice over the localization descends to a single principal restriction. -/
private theorem exists_map_after_localization (M : Submonoid A) (K : Type u)
    [CommRing K] [Algebra A K] [IsLocalization M K] {X Y : SchemeOverRing A}
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [LocallyOfFinitePresentation Y.hom]
    (f : (changeBase (algebraMap A K)).obj X ⟶ (changeBase (algebraMap A K)).obj Y) :
    ∃ (a : M) (g : (changeBase (algebraMap A (Localization.Away (a : A)))).obj X ⟶
        (changeBase (algebraMap A (Localization.Away (a : A)))).obj Y),
      let φ := algebraMap A (Localization.Away (a : A))
      let ψ := localizationComparison M K ⟨a⟩
      let e := changeBaseAlongComp φ ψ (localizationComparison_comp M K a)
      e.hom.app X ≫ (changeBase ψ).map g = f ≫ e.hom.app Y := by
  let κ := algebraMap A K
  let b := Spec.map (CommRingCat.ofHom κ)
  let f₀ := (pullbackSymmetry b X.hom).hom ≫ f.left ≫ fibreProjection κ Y
  have h₀ := domainChangeBase_over κ f
  obtain ⟨a, g, p, h₁, h₂, hg, hgY⟩ := exists_map_from_localized_pullback M K f₀ h₀
  exact ⟨a.unop.val, descendAtPrincipalStage M K f a.unop.val g p h₁ h₂ hg hgY⟩

private theorem exists_compatible_projection (M : Submonoid A) (K : Type u)
    [CommRing K] [Algebra A K] [IsLocalization M K] {X Y : SchemeOverRing A}
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] [LocallyOfFinitePresentation Y.hom]
    (f : (changeBase (algebraMap A K)).obj X ⟶ (changeBase (algebraMap A K)).obj Y) :
    ∃ (a : M) (g : (changeBase (algebraMap A (Localization.Away (a : A)))).obj X ⟶
        (changeBase (algebraMap A (Localization.Away (a : A)))).obj Y),
      ProjectionCompatibility (algebraMap A (Localization.Away (a : A)))
        (localizationComparison M K ⟨a⟩) (localizationComparison_comp M K a) g f := by
  obtain ⟨a, g, hg⟩ := exists_map_after_localization M K f
  exact ⟨a, g, ⟨hg⟩⟩

end ProjectionDescent


section SpreadSections

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection)
open Specs.SpreadProjectiveRightTorsor (changeBaseComp HasLocalSections)
open TopologicalSpace Topology
open scoped BigOperators
variable {A : Type u} [CommRing A]

section SectionDescent

variable {K : Type u} [CommRing K] [Algebra A K]

private theorem map_section_eq_of_natIso
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F : C₀ ⥤ C₁} {L : C₁ ⥤ C₂} {K₀ : C₀ ⥤ C₂} (e : K₀ ≅ F ⋙ L)
    {U X Y : C₀} (q : X ⟶ Y) (j : U ⟶ Y)
    (s : K₀.obj U ⟶ K₀.obj X) (s' : F.obj U ⟶ F.obj X)
    (h : s ≫ K₀.map q = K₀.map j)
    (h' : e.hom.app U ≫ L.map s' = s ≫ e.hom.app X) :
    L.map (s' ≫ F.map q) = L.map (F.map j) := by
  apply (cancel_epi (e.hom.app U)).mp
  calc
    _ = (e.hom.app U ≫ L.map s') ≫ L.map (F.map q) := by
      rw [Functor.map_comp, Category.assoc]
    _ = s ≫ (e.hom.app X ≫ L.map (F.map q)) := by rw [h', Category.assoc]
    _ = (s ≫ K₀.map q) ≫ e.hom.app Y := by
      rw [Category.assoc]
      exact congrArg (s ≫ ·) (e.hom.naturality q).symm
    _ = _ := h ▸ e.hom.naturality j

private theorem flat_overOpen {Y : SchemeOverRing A} [Flat Y.hom] (U : Y.left.Opens) :
    Flat (overOpen Y U).hom := by
  change Flat (U.ι ≫ Y.hom)
  infer_instance

private theorem localizationComparison_injective (M : Submonoid A) [IsLocalization M K]
    (hκ : Function.Injective (algebraMap A K)) (a : M) :
    Function.Injective (localizationComparison M K ⟨a⟩) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (a : A)) _).mpr
  intro x y
  refine ⟨congrArg (localizationComparison M K ⟨a⟩), ?_⟩
  rw [localizationComparison_algebraMap, localizationComparison_algebraMap]
  exact fun h => congrArg _ (hκ h)

private theorem section_eq_of_generic_comparison {D : Type u} [CommRing D]
    (φ : A →+* D) (ψ : D →+* K) (hψ : Function.Injective ψ)
    (hφ : ψ.comp φ = algebraMap A K)
    {U X Y : SchemeOverRing A} (q : X ⟶ Y) (j : U ⟶ Y)
    (hU : Flat U.hom) (hY : IsSeparated Y.hom)
    (s : (changeBase (algebraMap A K)).obj U ⟶ (changeBase (algebraMap A K)).obj X)
    (s' : (changeBase φ).obj U ⟶ (changeBase φ).obj X)
    (hs : s ≫ (changeBase (algebraMap A K)).map q = (changeBase (algebraMap A K)).map j)
    (hs' : (changeBaseAlongComp φ ψ hφ).hom.app U ≫ (changeBase ψ).map s' =
      s ≫ (changeBaseAlongComp φ ψ hφ).hom.app X) :
    s' ≫ (changeBase φ).map q = (changeBase φ).map j := by
  have : Flat ((changeBase φ).obj U).hom := baseChange_structureProperty @Flat φ U hU
  have : IsSeparated ((changeBase φ).obj Y).hom := baseChange_structureProperty @IsSeparated φ Y hY
  exact eq_of_injective_baseChange ψ hψ
    (map_section_eq_of_natIso (changeBaseAlongComp φ ψ hφ) q j s s' hs hs')

private theorem section_after_localization (M : Submonoid A) [IsLocalization M K]
    (hκ : Function.Injective (algebraMap A K)) {U X Y : SchemeOverRing A} (q : X ⟶ Y)
    (j : U ⟶ Y) [LocallyOfFinitePresentation X.hom] [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] [Flat U.hom] [IsSeparated Y.hom]
    (s : (changeBase (algebraMap A K)).obj U ⟶ (changeBase (algebraMap A K)).obj X)
    (hs : s ≫ (changeBase (algebraMap A K)).map q = (changeBase (algebraMap A K)).map j) :
    ∃ (a : M) (s' : (changeBase (algebraMap A (Localization.Away (a : A)))).obj U ⟶
        (changeBase (algebraMap A (Localization.Away (a : A)))).obj X),
      s' ≫ (changeBase (algebraMap A (Localization.Away (a : A)))).map q =
        (changeBase (algebraMap A (Localization.Away (a : A)))).map j := by
  obtain ⟨a, s', hs'⟩ := exists_map_after_localization M K s
  exact ⟨a, s', section_eq_of_generic_comparison
    (algebraMap A (Localization.Away (a : A))) (localizationComparison M K ⟨a⟩)
    (localizationComparison_injective M hκ a) (localizationComparison_comp M K a)
    q j ‹Flat U.hom› ‹IsSeparated Y.hom› s s' hs hs'⟩

end SectionDescent

variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [IsDomain A]

private theorem section_on_principal_open {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    (U : Y.left.affineOpens)
    (s : (changeBase (algebraMap A K)).obj (overOpen Y U.val) ⟶
      (changeBase (algebraMap A K)).obj X)
    (hs : s ≫ (changeBase (algebraMap A K)).map q =
      (changeBase (algebraMap A K)).map (overOpenι Y U.val)) :
    ∃ (a : nonZeroDivisors A) (s' : (changeBase (algebraMap A (Localization.Away (a : A)))).obj
        (overOpen Y U.val) ⟶ (changeBase (algebraMap A (Localization.Away (a : A)))).obj X),
      s' ≫ (changeBase (algebraMap A (Localization.Away (a : A)))).map q =
        (changeBase (algebraMap A (Localization.Away (a : A)))).map (overOpenι Y U.val) := by
  have : IsAffine (overOpen Y U.val).left := U.property
  have : Flat (overOpen Y U.val).hom := flat_overOpen U.val
  exact section_after_localization (nonZeroDivisors A) (IsFractionRing.injective A K)
    q (overOpenι Y U.val) s hs

private def restrictionMap (a b : A) (h : a ∣ b) :
    Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (IsLocalization.Away.isUnit_of_dvd b h)

private theorem restrictionMap_comp (a b : A) (h : a ∣ b) :
    (restrictionMap a b h).comp (algebraMap A (Localization.Away a)) =
      algebraMap A (Localization.Away b) :=
  IsLocalization.Away.lift_comp a _

private theorem section_eq_of_comparison
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    {F : C₀ ⥤ C₁} {L : C₁ ⥤ C₂} {K₀ : C₀ ⥤ C₂} (e : K₀ ≅ F ⋙ L)
    {U X Y : C₀} (q : X ⟶ Y) (j : U ⟶ Y) (s : F.obj U ⟶ F.obj X)
    (hs : s ≫ F.map q = F.map j) :
    (e.hom.app U ≫ L.map s ≫ e.inv.app X) ≫ K₀.map q = K₀.map j := by
  have h : L.map s ≫ (F ⋙ L).map q = (F ⋙ L).map j :=
    (L.map_comp s (F.map q)).symm.trans (congrArg (fun f => L.map f) hs)
  calc
    _ = e.hom.app U ≫ L.map s ≫ (e.inv.app X ≫ K₀.map q) := by simp only [Category.assoc]
    _ = e.hom.app U ≫ (F ⋙ L).map j ≫ e.inv.app Y := by
      rw [← e.inv.naturality q, ← Category.assoc (L.map s), h]
    _ = K₀.map j := by
      rw [← Category.assoc, ← e.hom.naturality j, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id]

private theorem range_principalProjection_mono {c b : A} (h : c ∣ b) (Y : SchemeOverRing A) :
    Set.range (fibreProjection (algebraMap A (Localization.Away b)) Y) ⊆
      Set.range (fibreProjection (algebraMap A (Localization.Away c)) Y) := by
  intro x hx
  change x ∈ Set.range (pullback.fst Y.hom
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))))) at hx
  change x ∈ Set.range (pullback.fst Y.hom
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away c)))))
  rw [Scheme.Pullback.range_fst, Set.mem_preimage] at hx ⊢
  change (Y.hom x : PrimeSpectrum A) ∈
    Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away b))) at hx
  change (Y.hom x : PrimeSpectrum A) ∈
    Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away c)))
  rw [PrimeSpectrum.localization_away_comap_range _ b] at hx
  rw [PrimeSpectrum.localization_away_comap_range _ c]
  intro hc
  exact hx (Ideal.mem_of_dvd _ h hc)

private theorem localSection_at_baseChange {D B : Type u} [CommRing D] [CommRing B]
    (α : A →+* D) (β : D →+* B) (φ : A →+* B)
    (e : changeBase φ ≅ changeBase α ⋙ changeBase β)
    {X Y U : SchemeOverRing A} (q : X ⟶ Y) (j : U ⟶ Y)
    (hj : IsOpenImmersion j.left)
    (s : (changeBase α).obj U ⟶ (changeBase α).obj X)
    (hs : s ≫ (changeBase α).map q = (changeBase α).map j)
    (y : ((changeBase φ).obj Y).left) (hy : fibreProjection φ Y y ∈ Set.range j.left) :
    ∃ r : (changeBase φ).obj U ⟶ (changeBase φ).obj X,
      IsOpenImmersion ((changeBase φ).map j).left ∧ y ∈ Set.range ((changeBase φ).map j).left ∧
        r ≫ (changeBase φ).map q = (changeBase φ).map j := by
  refine ⟨e.hom.app U ≫ (changeBase β).map s ≫ e.inv.app X,
    MorphismProperty.of_isPullback (changeBaseMap_isPullback φ j).flip hj, ?_,
    section_eq_of_comparison e q j s hs⟩
  rwa [range_changeBaseMap]

private theorem principal_cover_after_localization {Y : SchemeOverRing A}
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [NoetherianSpace Y.left]
    {I : Type u} [Finite I] (U : I → Y.left.affineOpens)
    (hcover : ∀ y : ((changeBase (algebraMap A K)).obj Y).left,
      ∃ i, fibreProjection (algebraMap A K) Y y ∈ (U i).val) :
    ∃ c : A, c ≠ 0 ∧ ∀ b : A, c ∣ b →
      ∀ y : ((changeBase (algebraMap A (Localization.Away b))).obj Y).left,
        ∃ i, fibreProjection (algebraMap A (Localization.Away b)) Y y ∈ (U i).val := by
  let bad := (⋃ i, ((U i).val : Set Y.left))ᶜ
  have hbad : IsConstructible bad :=
    (IsConstructible.iUnion fun i => (U i).property.isCompact.isConstructible (U i).val.isOpen).compl
  have hbη (y : Y.left) (hy : y ∈ bad) : Y.hom y ≠ (⊥ : PrimeSpectrum A) := by
    intro he
    have hmem : y ∈ Set.range (fibreProjection (algebraMap A K) Y) := by
      change y ∈ Set.range (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap A K))))
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, he]
      exact genericPoint_mem_range A K
    obtain ⟨z, rfl⟩ := hmem
    obtain ⟨i, hi⟩ := hcover z
    exact hy (Set.mem_iUnion.mpr ⟨i, hi⟩)
  obtain ⟨c, hc, havoid⟩ := exists_principal_open_avoiding Y.hom hbad hbη
  refine ⟨c, hc, fun b hcb y => ?_⟩
  let φ := algebraMap A (Localization.Away b)
  have hy : fibreProjection φ Y y ∉ bad :=
    fun hy => Set.disjoint_left.mp havoid hy (range_principalProjection_mono hcb Y ⟨y, rfl⟩)
  exact Set.mem_iUnion.mp (not_not.mp hy)

private theorem localSections_of_principal_cover {X Y : SchemeOverRing A} (q : X ⟶ Y)
    {I : Type u} (U : I → Y.left.affineOpens) (a : I → nonZeroDivisors A)
    (s : ∀ i, (changeBase (algebraMap A (Localization.Away (a i : A)))).obj (overOpen Y (U i).val) ⟶
      (changeBase (algebraMap A (Localization.Away (a i : A)))).obj X)
    (hs : ∀ i, s i ≫ (changeBase (algebraMap A (Localization.Away (a i : A)))).map q =
      (changeBase (algebraMap A (Localization.Away (a i : A)))).map (overOpenι Y (U i).val))
    (b : A) (hab : ∀ i, (a i : A) ∣ b)
    (hcover : ∀ y : ((changeBase (algebraMap A (Localization.Away b))).obj Y).left,
      ∃ i, fibreProjection (algebraMap A (Localization.Away b)) Y y ∈ (U i).val) :
    HasLocalSections ((changeBase (algebraMap A (Localization.Away b))).map q) := by
  intro y
  obtain ⟨i, hi⟩ := hcover y
  let φ := algebraMap A (Localization.Away b)
  let j := overOpenι Y (U i).val
  have hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (U i).val.ι)
  have hjy : fibreProjection φ Y y ∈ Set.range j.left := by
    change fibreProjection φ Y y ∈ Set.range (U i).val.ι
    rwa [Scheme.Opens.range_ι]
  let α := algebraMap A (Localization.Away (a i : A))
  let β := restrictionMap (a i : A) b (hab i)
  let e := changeBaseAlongComp α β (restrictionMap_comp (a i : A) b (hab i))
  obtain ⟨r, hOpen, hy', hr⟩ := localSection_at_baseChange α β φ e q j hj (s i) (hs i) y hjy
  exact ⟨_, (changeBase φ).map j, r, hOpen, hy', hr⟩

private theorem sections_over_common_stage {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [NoetherianSpace Y.left]
    {I : Type u} [Fintype I] (U : I → Y.left.affineOpens) (a : I → nonZeroDivisors A)
    (s : ∀ i, (changeBase (algebraMap A (Localization.Away (a i : A)))).obj (overOpen Y (U i).val) ⟶
      (changeBase (algebraMap A (Localization.Away (a i : A)))).obj X)
    (hs : ∀ i, s i ≫ (changeBase (algebraMap A (Localization.Away (a i : A)))).map q =
      (changeBase (algebraMap A (Localization.Away (a i : A)))).map (overOpenι Y (U i).val))
    (hcover : ∀ y : ((changeBase (algebraMap A K)).obj Y).left,
      ∃ i, fibreProjection (algebraMap A K) Y y ∈ (U i).val) :
    ∃ b : A, b ≠ 0 ∧ HasLocalSections ((changeBase (algebraMap A (Localization.Away b))).map q) := by
  classical
  obtain ⟨c, hc, hcover'⟩ := principal_cover_after_localization (K := K) U hcover
  let b := c * ∏ i, (a i : A)
  have hb : b ≠ 0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr
    fun i _ => mem_nonZeroDivisors_iff_ne_zero.mp (a i).property)
  have hd (i : I) : (a i : A) ∣ b :=
    (Finset.dvd_prod_of_mem (fun i => (a i : A)) (Finset.mem_univ i)).trans (dvd_mul_left _ _)
  exact ⟨b, hb, localSections_of_principal_cover q U a s hs b hd (hcover' b (dvd_mul_right _ _))⟩

/-- A Zariski cover by local sections spreads after one principal localization. -/
private theorem exists_localSections_after_localization {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation X.hom] [Flat Y.hom] [IsSeparated Y.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [NoetherianSpace Y.left]
    (h : HasLocalSections ((changeBase (algebraMap A K)).map q)) :
    ∃ b : A, b ≠ 0 ∧ HasLocalSections
      ((changeBase (algebraMap A (Localization.Away b))).map q) := by
  classical
  let κ := algebraMap A K
  let Yη := (changeBase κ).obj Y
  let p := fibreProjection κ Y
  have : QuasiCompact Yη.hom := baseChange_structureProperty @QuasiCompact κ Y inferInstance
  have : CompactSpace Yη.left := QuasiCompact.compactSpace_of_compactSpace Yη.hom
  choose U hyU s hs using affineNeighborhoodSection q (K := K) h
  let W (y : Yη.left) := p ⁻¹ᵁ (U y).val
  have hcover : (Set.univ : Set Yη.left) ⊆ ⋃ y, (W y : Set Yη.left) :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Yη.left))
    (fun y => (W y).isOpen) hcover
  choose a r hr using fun y : t => section_on_principal_open (K := K) q (U y) (s y) (hs y)
  apply sections_over_common_stage (K := K) q (fun y : t => U y) a r hr
  intro y
  obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact ⟨⟨w, hwt⟩, hw⟩

end SpreadSections

section SuccessiveBaseChanges

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase fibreProjection fibreProjection_over)
open Specs.SpreadProjectiveRightTorsor (rightMultiply HasLocalSections changeBaseComp)

variable {A B C K : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing K]

private theorem specMap_comp_eq (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) :
    Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom κ) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- The map from a fibre into an intermediate restriction of the scheme. -/
private def intermediateProjection (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    ((changeBase κ).obj X).left ⟶ ((changeBase φ).obj X).left :=
  pullback.lift (fibreProjection κ X)
    (((changeBase κ).obj X).hom ≫ Spec.map (CommRingCat.ofHom ψ)) (by
      rw [fibreProjection_over, Category.assoc, specMap_comp_eq φ ψ h])

private theorem intermediateProjection_fst (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    intermediateProjection φ ψ h X ≫ fibreProjection φ X = fibreProjection κ X :=
  pullback.lift_fst _ _ _

private theorem intermediateProjection_snd (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    intermediateProjection φ ψ h X ≫ ((changeBase φ).obj X).hom =
      ((changeBase κ).obj X).hom ≫ Spec.map (CommRingCat.ofHom ψ) :=
  pullback.lift_snd _ _ _

private theorem intermediateProjection_eq (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    intermediateProjection φ ψ h X =
      ((changeBaseAlongComp φ ψ h).hom.app X).left ≫ fibreProjection ψ ((changeBase φ).obj X) := by
  let e := (changeBaseAlongComp φ ψ h).hom.app X
  apply pullback.hom_ext
  · change intermediateProjection φ ψ h X ≫ fibreProjection φ X =
      (e.left ≫ fibreProjection ψ ((changeBase φ).obj X)) ≫ fibreProjection φ X
    rw [intermediateProjection_fst, Category.assoc, changeBaseAlongComp_hom_projections]
  · change intermediateProjection φ ψ h X ≫ ((changeBase φ).obj X).hom =
      (e.left ≫ fibreProjection ψ ((changeBase φ).obj X)) ≫ ((changeBase φ).obj X).hom
    rw [intermediateProjection_snd, Category.assoc, fibreProjection_over ψ, ← Category.assoc]
    exact congrArg (· ≫ Spec.map (CommRingCat.ofHom ψ)) (Over.w e).symm

private theorem intermediateProjection_trans (φ : A →+* B) (β : B →+* C) (χ : C →+* K)
    {ψ : B →+* K} {κ : A →+* K} (hβ : χ.comp β = ψ) (h : ψ.comp φ = κ)
    (h' : χ.comp (β.comp φ) = κ) (X : SchemeOverRing A) :
    intermediateProjection (β.comp φ) χ h' X ≫ intermediateProjection φ β rfl X =
      intermediateProjection φ ψ h X := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ fibreProjection φ X = _ ≫ fibreProjection φ X
    simp only [Category.assoc, intermediateProjection_fst]
  · change (_ ≫ _) ≫ ((changeBase φ).obj X).hom = _ ≫ ((changeBase φ).obj X).hom
    simp only [Category.assoc, intermediateProjection_snd]
    rw [← Category.assoc, intermediateProjection_snd, Category.assoc, specMap_comp_eq β χ hβ]

private theorem compatible_iff_projection (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) {X Y : SchemeOverRing A}
    (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Y) :
    let e := changeBaseAlongComp φ ψ h
    e.hom.app X ≫ (changeBase ψ).map q = q₀ ≫ e.hom.app Y ↔
      intermediateProjection φ ψ h X ≫ q.left ≫ fibreProjection φ Y =
        q₀.left ≫ fibreProjection κ Y := by
  let e := changeBaseAlongComp φ ψ h
  constructor
  · intro hh
    have hm := congrArg (fun f => f.left ≫ fibreProjection ψ ((changeBase φ).obj Y) ≫
      fibreProjection φ Y) hh
    simpa only [Over.comp_left, Category.assoc, map_fibreProjection_assoc,
      changeBaseAlongComp_hom_projections, intermediateProjection_eq] using hm
  · intro hh
    apply map_eq_of_projection_eq φ ψ h q₀ q
    simpa only [intermediateProjection_eq, Category.assoc] using hh

private def extendProjection (φ : A →+* B) (β : B →+* C)
    {X Y : SchemeOverRing A} (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y) :
    (changeBase (β.comp φ)).obj X ⟶ (changeBase (β.comp φ)).obj Y :=
  (changeBaseComp φ β).hom.app X ≫ (changeBase β).map q ≫ (changeBaseComp φ β).inv.app Y

private theorem extendProjection_comm (φ : A →+* B) (β : B →+* C)
    {X Y : SchemeOverRing A} (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y) :
    extendProjection φ β q ≫ (changeBaseComp φ β).hom.app Y =
      (changeBaseComp φ β).hom.app X ≫ (changeBase β).map q := by
  simp [extendProjection]

private theorem extendProjection_compatible (φ : A →+* B) (β : B →+* C) (χ : C →+* K)
    {ψ : B →+* K} {κ : A →+* K} (hβ : χ.comp β = ψ) (h : ψ.comp φ = κ)
    (h' : χ.comp (β.comp φ) = κ) {X Y : SchemeOverRing A}
    (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Y)
    (hq : (changeBaseAlongComp φ ψ h).hom.app X ≫ (changeBase ψ).map q =
      q₀ ≫ (changeBaseAlongComp φ ψ h).hom.app Y) :
    (changeBaseAlongComp (β.comp φ) χ h').hom.app X ≫
        (changeBase χ).map (extendProjection φ β q) =
      q₀ ≫ (changeBaseAlongComp (β.comp φ) χ h').hom.app Y := by
  have hq' := (compatible_iff_projection φ ψ h q q₀).mp hq
  apply (compatible_iff_projection (β.comp φ) χ h' _ _).mpr
  let e := changeBaseComp φ β
  have he : changeBaseAlongComp φ β rfl = e := by simp [changeBaseAlongComp, e]
  have hY := changeBaseAlongComp_inv_projections φ β rfl Y
  rw [he] at hY
  have hX := intermediateProjection_eq φ β rfl X
  rw [he] at hX
  change intermediateProjection (β.comp φ) χ h' X ≫
    (e.hom.app X).left ≫ ((changeBase β).map q).left ≫
      (e.inv.app Y).left ≫ fibreProjection (β.comp φ) Y = _
  rw [hY, map_fibreProjection_assoc, ← Category.assoc ((e.hom.app X).left), ← hX]
  rw [← Category.assoc (intermediateProjection (β.comp φ) χ h' X),
    intermediateProjection_trans φ β χ hβ h h' X]
  exact hq'

private theorem exists_extendedProjection (φ : A →+* B) (β : B →+* C) (χ : C →+* K)
    {ψ : B →+* K} {κ : A →+* K} (hβ : χ.comp β = ψ) (h : ψ.comp φ = κ)
    (h' : χ.comp (β.comp φ) = κ) {X Y : SchemeOverRing A}
    (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Y)
    (hq : ProjectionCompatibility φ ψ h q q₀) :
    ∃ p : (changeBase (β.comp φ)).obj X ⟶ (changeBase (β.comp φ)).obj Y,
      ProjectionCompatibility (β.comp φ) χ h' p q₀ :=
  ⟨extendProjection φ β q, ⟨extendProjection_compatible φ β χ hβ h h' q q₀ hq.comm⟩⟩

private theorem groupIsoWithUnderlyingComparison
    {D₀ D₁ D₂ : Type*} [Category* D₀] [Category* D₁] [Category* D₂]
    [CartesianMonoidalCategory D₀] [CartesianMonoidalCategory D₁] [CartesianMonoidalCategory D₂]
    {F : D₀ ⥤ D₁} {L : D₁ ⥤ D₂} {J : D₀ ⥤ D₂}
    [F.Monoidal] [L.Monoidal] [J.Monoidal] (e : J ≅ F ⋙ L) :
    ∃ eG : J.mapGrp ≅ F.mapGrp ⋙ L.mapGrp,
      ∀ G : Grp D₀, (eG.hom.app G).hom.hom = e.hom.app G.X := by
  refine ⟨Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso, fun G => ?_⟩
  change e.hom.app G.X ≫ 𝟙 _ = _
  exact Category.comp_id _

end SuccessiveBaseChanges

private theorem composedBaseChange_morphismProperty
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.IsStableUnderBaseChange] (φ : A →+* B) (β : B →+* C)
    {X Y : SchemeOverRing A} (q : X ⟶ Y) (hq : P ((changeBase φ).map q).left) :
    P ((changeBase (β.comp φ)).map q).left := by
  let e := changeBaseComp φ β
  exact (morphismProperty_transport P (e.app X) (e.app Y) _ _ (e.hom.naturality q)).mpr
    (baseChange_morphismProperty P β ((changeBase φ).map q) hq)

private theorem composedBaseChange_structureProperty
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.IsStableUnderBaseChange] (φ : A →+* B) (β : B →+* C)
    (Y : SchemeOverRing A) (hY : P ((changeBase φ).obj Y).hom) :
    P ((changeBase (β.comp φ)).obj Y).hom :=
  (structureProperty_transport P ((changeBaseComp φ β).app Y)).mpr
    (baseChange_structureProperty P β ((changeBase φ).obj Y) hY)

section SmoothRefinements

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase)
open Specs.ArithmeticProjectiveFiniteness (BaseRing)
open Specs.SpreadProjectiveRightTorsor (rationalMap)

private instance smoothRespectsIso : MorphismProperty.RespectsIso
    (@Smooth : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e f _ => smooth_comp e.hom f)
    (fun e f _ => smooth_comp f e.hom)

variable {A : Type u} [CommRing A] [IsDomain A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]

private abbrev baseObject (A : Type u) [CommRing A] : SchemeOverRing A :=
  Over.mk (𝟙 (Spec (CommRingCat.of A)))

private abbrev structureInSlice (Y : SchemeOverRing A) : Y ⟶ baseObject A :=
  Over.homMk Y.hom (Category.comp_id _)

private theorem smooth_structureInSlice_iff {D : Type u} [CommRing D] (φ : A →+* D)
    (Y : SchemeOverRing A) :
    Smooth ((changeBase φ).map (structureInSlice Y)).left ↔ Smooth ((changeBase φ).obj Y).hom := by
  have : IsIso ((changeBase φ).obj (baseObject A)).hom := by
    change IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of A))) (Spec.map (CommRingCat.ofHom φ)))
    infer_instance
  rw [← Over.w ((changeBase φ).map (structureInSlice Y))]
  exact (MorphismProperty.cancel_right_of_respectsIso @Smooth _ _).symm

private theorem exists_smooth_structure_restriction (Y : SchemeOverRing A)
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [NoetherianSpace Y.left]
    (hY : Smooth ((changeBase (algebraMap A K)).obj Y).hom) :
    ∃ b : A, b ≠ 0 ∧ Smooth ((changeBase (algebraMap A (Localization.Away b))).obj Y).hom := by
  have : LocallyOfFinitePresentation (structureInSlice Y).left := ‹LocallyOfFinitePresentation Y.hom›
  obtain ⟨b, hb, hpb⟩ := exists_smooth_principal_restriction A K (structureInSlice Y)
    ((smooth_structureInSlice_iff (algebraMap A K) Y).mpr hY)
  exact ⟨b, hb, (smooth_structureInSlice_iff _ Y).mp hpb⟩

private theorem smooth_principal_refinement {X Y : SchemeOverRing A} (q : X ⟶ Y)
    {a b : A} (h : a ∣ b)
    (hq : Smooth ((changeBase (algebraMap A (Localization.Away a))).map q).left) :
    Smooth ((changeBase (algebraMap A (Localization.Away b))).map q).left :=
  (restrictionMap_comp a b h) ▸
    composedBaseChange_morphismProperty @Smooth _ (restrictionMap a b h) q hq

private theorem smooth_structure_principal_refinement (Y : SchemeOverRing A)
    {a b : A} (h : a ∣ b) (hY : Smooth ((changeBase (algebraMap A (Localization.Away a))).obj Y).hom) :
    Smooth ((changeBase (algebraMap A (Localization.Away b))).obj Y).hom :=
  (restrictionMap_comp a b h) ▸
    composedBaseChange_structureProperty @Smooth _ (restrictionMap a b h) Y hY

/-- Both the projection and its target structure morphism become smooth
after the same principal restriction. -/
private theorem exists_smooth_model {X Y : SchemeOverRing A} (q : X ⟶ Y)
    [LocallyOfFinitePresentation q.left]
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [NoetherianSpace X.left]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [NoetherianSpace Y.left]
    (hq : Smooth ((changeBase (algebraMap A K)).map q).left)
    (hY : Smooth ((changeBase (algebraMap A K)).obj Y).hom) :
    ∃ c : A, c ≠ 0 ∧
      Smooth ((changeBase (algebraMap A (Localization.Away c))).map q).left ∧
      Smooth ((changeBase (algebraMap A (Localization.Away c))).obj Y).hom := by
  obtain ⟨a, ha, hqa⟩ := exists_smooth_principal_restriction A K q hq
  obtain ⟨b, hb, hYb⟩ := exists_smooth_structure_restriction Y hY
  exact ⟨a * b, mul_ne_zero ha hb, smooth_principal_refinement q (dvd_mul_right a b) hqa,
    smooth_structure_principal_refinement Y (dvd_mul_left b a) hYb⟩

end SmoothRefinements



section SpreadingAssembly

open Specs.FlagCohomology (SchemeOverRing)
open Specs.ArithmeticCohomologyBaseChange (changeBase)
open Specs.ArithmeticProjectiveFiniteness (BaseRing projectiveSpace)
open Specs.SpreadProjectiveRightTorsor (rightMultiply HasLocalSections changeBaseComp changeBaseGroup rationalMap Statement)

variable {A B K : Type u} [CommRing A] [CommRing B] [CommRing K]

private theorem finitePresentation_of_proper {R : Type u} [CommRing R] [IsNoetherianRing R]
    (Y : SchemeOverRing R) [IsProper Y.hom] : LocallyOfFinitePresentation Y.hom := inferInstance

private theorem locallyNoetherian_of_finiteType {R : Type u} [CommRing R] [IsNoetherianRing R]
    (Y : SchemeOverRing R) [LocallyOfFiniteType Y.hom] : IsLocallyNoetherian Y.left :=
  LocallyOfFiniteType.isLocallyNoetherian Y.hom

private theorem noetherian_of_finiteType {R : Type u} [CommRing R] [IsNoetherianRing R]
    (Y : SchemeOverRing R) [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    TopologicalSpace.NoetherianSpace Y.left := by
  have : IsLocallyNoetherian Y.left := locallyNoetherian_of_finiteType Y
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : IsNoetherian Y.left := .mk
  infer_instance

private theorem comparedProjection_morphismProperty
    {C : Type u} [CommRing C] (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (φ : A →+* B) (β : B →+* C)
    {X Y : SchemeOverRing A} (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (hq : P ((changeBase β).map q).left) :
    P (extendProjection φ β q).left :=
  (morphismProperty_transport P ((changeBaseComp φ β).app X)
    ((changeBaseComp φ β).app Y) _ _ (extendProjection_comm φ β q)).mpr hq

private theorem composedBaseChange_localSections
    {C : Type u} [CommRing C] (φ : A →+* B) (β : B →+* C)
    {X Y : SchemeOverRing A} (q : X ⟶ Y)
    (hq : HasLocalSections ((changeBase φ).map q)) :
    HasLocalSections ((changeBase (β.comp φ)).map q) := by
  let e := changeBaseComp φ β
  exact localSections_transport (e.app X).symm (e.app Y).symm _ _
    (e.inv.naturality q) (changeBase_openSections β _ hq)

private theorem invert_comparison {D : Type*} [Category* D] {X X' Y Y' : D}
    (x : X ≅ X') (y : Y ≅ Y') (q : X ⟶ Y) (p : X' ⟶ Y')
    (h : x.hom ≫ p = q ≫ y.hom) : p ≫ y.inv = x.inv ≫ q := by
  apply (cancel_epi x.hom).mp
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem comparedProjection_localSections
    {C : Type u} [CommRing C] (φ : A →+* B) (β : B →+* C)
    {X Y : SchemeOverRing A} (q : (changeBase φ).obj X ⟶ (changeBase φ).obj Y)
    (hq : HasLocalSections ((changeBase β).map q)) :
    HasLocalSections (extendProjection φ β q) := by
  let e := changeBaseComp φ β
  exact localSections_transport (e.app X).symm (e.app Y).symm _ _
    (invert_comparison (e.app X) (e.app Y) (extendProjection φ β q) ((changeBase β).map q)
      (extendProjection_comm φ β q).symm) hq

private theorem projectedClosedImmersion (φ : A →+* B) {Y : SchemeOverRing A} (d : ℕ)
    (j : Y ⟶ projectiveSpace A d) (hj : IsClosedImmersion j.left) :
    ∃ j' : (changeBase φ).obj Y ⟶ projectiveSpace B d, IsClosedImmersion j'.left := by
  let e := arithmeticProjectiveBaseChange φ d
  refine ⟨(changeBase φ).map j ≫ e.inv, ?_⟩
  have := baseChange_morphismProperty @IsClosedImmersion φ j hj
  change IsClosedImmersion (((changeBase φ).map j).left ≫ e.inv.left)
  infer_instance

private abbrev principalBaseMap {R : Type u} [CommRing R] (a : R) :
    R →+* Localization.Away a := algebraMap R (Localization.Away a)

private theorem arithmeticProjection_of_stage {m : ℕ} (hm : m ≠ 0)
    {X Y : SchemeOverRing (BaseRing.{u} m)}
    (q : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Y)
    (a : BaseRing.{u} m) (ha : a ≠ 0) (ψ : Localization.Away a →+* ULift.{u} ℚ)
    (hψ : ψ.comp (principalBaseMap a) = rationalMap hm)
    (p : (changeBase (principalBaseMap a)).obj X ⟶ (changeBase (principalBaseMap a)).obj Y)
    (hp : ProjectionCompatibility (principalBaseMap a) ψ hψ p q) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Y),
      ProjectionCompatibility φ (rationalMap hn) hφ p q := by
  obtain ⟨n, hn, hmn, r, hInt, hκ, _⟩ := exists_arithmetic_refinement hm a ha
  let α := principalBaseMap a
  let β : Localization.Away a →+* BaseRing.{u} n := r.toRingHom
  have ht : (rationalMap hn).comp β = ψ := by
    apply IsLocalization.ringHom_ext (S := Localization.Away a) (P := ULift.{u} ℚ)
      (j := (rationalMap hn).comp β) (k := ψ) (Submonoid.powers a)
    change ((rationalMap hn).comp β).comp α = ψ.comp α
    rw [RingHom.comp_assoc]
    exact hκ.trans hψ.symm
  refine ⟨n, hn, hmn, r.toRingHom.comp (principalBaseMap a), ?_, ?_, ?_⟩
  · exact hInt
  · exact hκ
  · exact exists_extendedProjection α β (rationalMap hn) (X := X) (Y := Y) ht hψ hκ p q hp

private theorem exists_arithmetic_projection {m : ℕ} (hm : m ≠ 0)
    {X Y : SchemeOverRing (BaseRing.{u} m)} [CompactSpace X.left]
    [QuasiSeparatedSpace X.left] [LocallyOfFinitePresentation Y.hom]
    (q : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Y) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Y),
      ProjectionCompatibility φ (rationalMap hn) hφ p q := by
  let R := BaseRing.{u} m
  let F := ULift.{u} ℚ
  letI : Algebra R F := (rationalMap hm).toAlgebra
  have : IsDomain R := arithmeticBase_isDomain m hm
  have : IsFractionRing R F := arithmeticGeneric_isFractionRing m hm
  obtain ⟨a, p, hp⟩ := exists_compatible_projection (nonZeroDivisors R) F q
  have ha : (a : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp a.property
  exact arithmeticProjection_of_stage hm (X := X) (Y := Y) q a ha
    (localizationComparison (nonZeroDivisors R) F ⟨a⟩)
    (localizationComparison_comp (nonZeroDivisors R) F a) p hp

private theorem exists_smooth_arithmetic_restriction {m : ℕ} (hm : m ≠ 0)
    {X Y : SchemeOverRing (BaseRing.{u} m)} (q : X ⟶ Y)
    [IsAffine X.left] [Smooth X.hom] [IsProper Y.hom]
    (hq : Smooth ((changeBase (rationalMap hm)).map q).left)
    (hY : Smooth ((changeBase (rationalMap hm)).obj Y).hom) :
    ∃ (n : ℕ) (_ : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n)),
      Smooth ((changeBase φ).map q).left ∧ Smooth ((changeBase φ).obj Y).hom := by
  let R := BaseRing.{u} m
  let F := ULift.{u} ℚ
  letI : Algebra R F := (rationalMap hm).toAlgebra
  have : IsDomain R := arithmeticBase_isDomain m hm
  have : IsFractionRing R F := arithmeticGeneric_isFractionRing m hm
  have : IsNoetherianRing R := arithmeticBase_isNoetherian m
  have : IsLocallyNoetherian Y.left := locallyNoetherian_of_finiteType Y
  have : QuasiCompact X.hom := inferInstance
  have : NoetherianSpace X.left := noetherian_of_finiteType X
  have : NoetherianSpace Y.left := noetherian_of_finiteType Y
  have : LocallyOfFiniteType (q.left ≫ Y.hom) :=
    (Over.w q).symm ▸ (inferInstance : LocallyOfFiniteType X.hom)
  have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left Y.hom
  have : LocallyOfFinitePresentation q.left := inferInstance
  obtain ⟨b, hb, hqb, hYb⟩ := exists_smooth_model (A := R) (K := F) q hq hY
  obtain ⟨n, hn, hmn, r, hInt, _, _⟩ := exists_arithmetic_refinement hm b hb
  let α := principalBaseMap b
  let β : Localization.Away (b : BaseRing.{u} m) →+* BaseRing.{u} n := r.toRingHom
  refine ⟨n, hn, hmn, r.toRingHom.comp (principalBaseMap b), ?_, ?_, ?_⟩
  · exact hInt
  · exact composedBaseChange_morphismProperty @Smooth α β (X := X) (Y := Y) q hqb
  · exact composedBaseChange_structureProperty @Smooth α β Y hYb

private theorem exists_split_arithmetic_restriction {m : ℕ} (hm : m ≠ 0)
    {X Y : SchemeOverRing (BaseRing.{u} m)} (q : X ⟶ Y)
    [Smooth X.hom] [Smooth Y.hom] [IsProper Y.hom]
    (hq : HasLocalSections ((changeBase (rationalMap hm)).map q)) :
    ∃ (n : ℕ) (_ : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n)),
      HasLocalSections ((changeBase φ).map q) := by
  let R := BaseRing.{u} m
  let F := ULift.{u} ℚ
  letI : Algebra R F := (rationalMap hm).toAlgebra
  have : IsDomain R := arithmeticBase_isDomain m hm
  have : IsFractionRing R F := arithmeticGeneric_isFractionRing m hm
  have : IsNoetherianRing R := arithmeticBase_isNoetherian m
  have : NoetherianSpace Y.left := noetherian_of_finiteType Y
  obtain ⟨b, hb, hqb⟩ := exists_localSections_after_localization (A := R) (K := F) q hq
  obtain ⟨n, hn, hmn, r, hInt, _, _⟩ := exists_arithmetic_refinement hm b hb
  let α := principalBaseMap b
  let β : Localization.Away (b : BaseRing.{u} m) →+* BaseRing.{u} n := r.toRingHom
  refine ⟨n, hn, hmn, r.toRingHom.comp (principalBaseMap b), ?_, ?_⟩
  · exact hInt
  · exact composedBaseChange_localSections α β (X := X) (Y := Y) q hqb

private theorem affineBaseChange (φ : A →+* B) (X : SchemeOverRing A) [IsAffine X.left] :
    IsAffine ((changeBase φ).obj X).left := by
  change IsAffine (pullback X.hom (Spec.map (CommRingCat.ofHom φ)))
  infer_instance

private theorem kernelPair_on_arithmetic_model {m : ℕ} (hm : m ≠ 0)
    {G H : Grp (SchemeOverRing (BaseRing.{u} m))} (i : H ⟶ G)
    {Y : SchemeOverRing (BaseRing.{u} m)} (q : G.X ⟶ Y)
    [Smooth G.X.hom] [Smooth H.X.hom] [IsClosedImmersion i.hom.hom.left]
    [IsSeparated Y.hom] [Smooth q.left]
    (h : IsPullback prod.fst (rightMultiply ((changeBaseGroup (rationalMap hm)).map i))
      ((changeBase (rationalMap hm)).map q) ((changeBase (rationalMap hm)).map q)) :
    IsPullback prod.fst (rightMultiply i) q q := by
  let R := BaseRing.{u} m
  let F := ULift.{u} ℚ
  letI : Algebra R F := (rationalMap hm).toAlgebra
  have : IsDomain R := arithmeticBase_isDomain m hm
  have : IsFractionRing R F := arithmeticGeneric_isFractionRing m hm
  exact kernelPair_of_generic (A := R) (K := F) i q h

private theorem integerMap_comp {l m n : ℕ}
    (φ : BaseRing.{u} l →+* BaseRing.{u} m) (β : BaseRing.{u} m →+* BaseRing.{u} n)
    (hφ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} l)) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} m))
    (hβ : β.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} n)) :
    (β.comp φ).comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} l)) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} n) := by
  rw [RingHom.comp_assoc, hφ, hβ]

set_option maxHeartbeats 400000

section GenericProps
variable {A B K : Type u} [CommRing A] [CommRing B] [CommRing K]

private theorem targetIsoProperties {X Y Z : SchemeOverRing A} (q : X ⟶ Y) (e : Y ≅ Z)
    (hY : Smooth Y.hom) (hq : Smooth q.left) (hs : HasLocalSections q) :
    Smooth Z.hom ∧ Smooth (q ≫ e.hom).left ∧ HasLocalSections (q ≫ e.hom) := by
  have h : q ≫ e.hom = (Iso.refl X).hom ≫ (q ≫ e.hom) := (Category.id_comp _).symm
  exact ⟨(structureProperty_transport @Smooth e).mp hY,
    (morphismProperty_transport @Smooth (Iso.refl X) e _ _ h).mp hq,
    localSections_transport (Iso.refl X) e _ _ h hs⟩

private theorem smoothStructure_of_baseComparison (φ : A →+* B) (ψ : B →+* K)
    {κ : A →+* K} (h : ψ.comp φ = κ) (Z : SchemeOverRing A)
    (hZ : Smooth ((changeBase κ).obj Z).hom) :
    Smooth ((changeBase ψ).obj ((changeBase φ).obj Z)).hom :=
  (structureProperty_transport @Smooth ((changeBaseAlongComp φ ψ h).app Z)).mp hZ

private theorem smoothProjection_of_baseComparison (φ : A →+* B) (ψ : B →+* K)
    {κ : A →+* K} (h : ψ.comp φ = κ) {X Z : SchemeOverRing A}
    (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Z)
    (hp : ProjectionCompatibility φ ψ h p q₀) (hq : Smooth q₀.left) :
    Smooth ((changeBase ψ).map p).left := by
  subst κ
  let e := changeBaseComp φ ψ
  have he : changeBaseAlongComp φ ψ rfl = e := by simp [changeBaseAlongComp, e]
  have hd := ProjectionCompatibility.comm hp
  rw [he] at hd
  let a : (changeBase (ψ.comp φ)).obj X ≅ (changeBase ψ).obj ((changeBase φ).obj X) := e.app X
  let b : (changeBase (ψ.comp φ)).obj Z ≅ (changeBase ψ).obj ((changeBase φ).obj Z) := e.app Z
  have hh : q₀ ≫ b.hom = a.hom ≫ (changeBase ψ).map p := hd.symm
  exact (morphismProperty_transport @Smooth a b q₀ ((changeBase ψ).map p) hh).mp hq

private theorem sections_of_baseComparison (φ : A →+* B) (ψ : B →+* K)
    {κ : A →+* K} (h : ψ.comp φ = κ) {X Z : SchemeOverRing A}
    (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Z)
    (hp : ProjectionCompatibility φ ψ h p q₀) (hs : HasLocalSections q₀) :
    HasLocalSections ((changeBase ψ).map p) := by
  subst κ
  let e := changeBaseComp φ ψ
  have he : changeBaseAlongComp φ ψ rfl = e := by simp [changeBaseAlongComp, e]
  have hd := ProjectionCompatibility.comm hp
  rw [he] at hd
  let a : (changeBase (ψ.comp φ)).obj X ≅ (changeBase ψ).obj ((changeBase φ).obj X) := e.app X
  let b : (changeBase (ψ.comp φ)).obj Z ≅ (changeBase ψ).obj ((changeBase φ).obj Z) := e.app Z
  have hh : q₀ ≫ b.hom = a.hom ≫ (changeBase ψ).map p := hd.symm
  exact localSections_transport a b q₀ ((changeBase ψ).map p) hh hs

end GenericProps

section RefinedProjectionProperties

variable {A B C K : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing K]

private theorem smooth_of_refined_projection
    (φ : A →+* B) (β : B →+* C) (χ : C →+* K) {ψ : B →+* K} {κ : A →+* K}
    (hβ : χ.comp β = ψ) (h : ψ.comp φ = κ) (h' : χ.comp (β.comp φ) = κ)
    {X Z : SchemeOverRing A}
    (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Z)
    (hp : ProjectionCompatibility φ ψ h p q₀)
    (hq : Smooth ((changeBase β).map p).left) (hZ : Smooth ((changeBase β).obj ((changeBase φ).obj Z)).hom) :
    ∃ p' : (changeBase (β.comp φ)).obj X ⟶ (changeBase (β.comp φ)).obj Z,
      ProjectionCompatibility (β.comp φ) χ h' p' q₀ ∧
        Smooth p'.left ∧ Smooth ((changeBase (β.comp φ)).obj Z).hom :=
  ⟨extendProjection φ β p,
    ProjectionCompatibility.mk (extendProjection_compatible φ β χ hβ h h' p q₀ (ProjectionCompatibility.comm hp)),
    comparedProjection_morphismProperty @Smooth φ β p hq,
    (structureProperty_transport @Smooth ((changeBaseComp φ β).app Z)).mpr hZ⟩

private theorem split_of_refined_projection
    (φ : A →+* B) (β : B →+* C) (χ : C →+* K) {ψ : B →+* K} {κ : A →+* K}
    (hβ : χ.comp β = ψ) (h : ψ.comp φ = κ) (h' : χ.comp (β.comp φ) = κ)
    {X Z : SchemeOverRing A}
    (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z)
    (q₀ : (changeBase κ).obj X ⟶ (changeBase κ).obj Z)
    (hp : ProjectionCompatibility φ ψ h p q₀)
    (hq : Smooth p.left) (hZ : Smooth ((changeBase φ).obj Z).hom)
    (hs : HasLocalSections ((changeBase β).map p)) :
    ∃ p' : (changeBase (β.comp φ)).obj X ⟶ (changeBase (β.comp φ)).obj Z,
      ProjectionCompatibility (β.comp φ) χ h' p' q₀ ∧
        Smooth p'.left ∧ Smooth ((changeBase (β.comp φ)).obj Z).hom ∧ HasLocalSections p' :=
  ⟨extendProjection φ β p,
    ProjectionCompatibility.mk (extendProjection_compatible φ β χ hβ h h' p q₀ (ProjectionCompatibility.comm hp)),
    comparedProjection_morphismProperty @Smooth φ β p (baseChange_morphismProperty @Smooth β p hq),
    composedBaseChange_structureProperty @Smooth φ β Z hZ,
    comparedProjection_localSections φ β p hs⟩

end RefinedProjectionProperties

private structure ArithmeticProjectionStage {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)}
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z) where
  index : ℕ
  nonzero : index ≠ 0
  divides : m ∣ index
  ringMap : BaseRing.{u} m →+* BaseRing.{u} index
  integers : ringMap.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
    algebraMap (ULift.{u} ℤ) (BaseRing.{u} index)
  rational : (rationalMap nonzero).comp ringMap = rationalMap hm
  projection : (changeBase ringMap).obj X ⟶ (changeBase ringMap).obj Z
  comparison : ProjectionCompatibility ringMap (rationalMap nonzero) rational projection q₀

private theorem exists_arithmetic_projection_stage {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)} [CompactSpace X.left]
    [QuasiSeparatedSpace X.left] [LocallyOfFinitePresentation Z.hom]
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z) :
    Nonempty (ArithmeticProjectionStage hm q₀) := by
  obtain ⟨n, hn, hd, φ, hInt, hφ, p, hp⟩ := exists_arithmetic_projection (X := X) (Y := Z) hm q₀
  exact ⟨⟨n, hn, hd, φ, hInt, hφ, p, hp⟩⟩

private theorem refine_smooth_projection {m m₁ : ℕ} (hm : m ≠ 0) (hm₁ : m₁ ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)}
    (φ₁ : BaseRing.{u} m →+* BaseRing.{u} m₁) (hd₁ : m ∣ m₁)
    (hInt₁ : φ₁.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} m₁))
    (hφ₁ : (rationalMap hm₁).comp φ₁ = rationalMap hm)
    (p₁ : (changeBase φ₁).obj X ⟶ (changeBase φ₁).obj Z)
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hp₁ : ProjectionCompatibility φ₁ (rationalMap hm₁) hφ₁ p₁ q₀)
    [IsAffine ((changeBase φ₁).obj X).left]
    [Smooth ((changeBase φ₁).obj X).hom] [IsProper ((changeBase φ₁).obj Z).hom]
    (hp₁η : Smooth ((changeBase (rationalMap hm₁)).map p₁).left)
    (hZ₁ : Smooth ((changeBase (rationalMap hm₁)).obj ((changeBase φ₁).obj Z)).hom) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z),
      ProjectionCompatibility φ (rationalMap hn) hφ p q₀ ∧
        Smooth p.left ∧ Smooth ((changeBase φ).obj Z).hom := by
  obtain ⟨n, hn, hd₂, β, hInt₂, hpβ, hZβ⟩ :=
    exists_smooth_arithmetic_restriction hm₁ p₁ hp₁η hZ₁
  let φ := β.comp φ₁
  have hInt := integerMap_comp φ₁ β hInt₁ hInt₂
  have hφ := rationalMap_comp_refinement hm hn φ hInt
  have hβ := rationalMap_comp_refinement hm₁ hn β hInt₂
  refine ⟨n, hn, hd₁.trans hd₂, φ, hInt, hφ, ?_⟩
  exact smooth_of_refined_projection φ₁ β (rationalMap hn) hβ hφ₁ hφ p₁ q₀ hp₁ hpβ hZβ

private theorem restrict_smooth_stage {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)} [IsAffine X.left] [Smooth X.hom] [IsProper Z.hom]
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hZ : Smooth ((changeBase (rationalMap hm)).obj Z).hom)
    (hq : Smooth q₀.left)
    (stage : ArithmeticProjectionStage hm q₀) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z),
      ProjectionCompatibility φ (rationalMap hn) hφ p q₀ ∧
        Smooth p.left ∧ Smooth ((changeBase φ).obj Z).hom := by
  let φ₁ := stage.ringMap
  let κ₁ := rationalMap stage.nonzero
  let p₁ := stage.projection
  have hZ₁ := smoothStructure_of_baseComparison φ₁ κ₁ stage.rational Z hZ
  have hp₁η := smoothProjection_of_baseComparison φ₁ κ₁ stage.rational p₁ q₀ stage.comparison hq
  have : IsAffine ((changeBase φ₁).obj X).left := affineBaseChange φ₁ X
  have : Smooth ((changeBase φ₁).obj X).hom := baseChange_structureProperty @Smooth φ₁ X inferInstance
  have : IsProper ((changeBase φ₁).obj Z).hom := baseChange_structureProperty @IsProper φ₁ Z inferInstance
  exact refine_smooth_projection hm stage.nonzero φ₁ stage.divides stage.integers
    stage.rational p₁ q₀ stage.comparison hp₁η hZ₁

private theorem exists_smooth_arithmetic_projection {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)} [IsAffine X.left] [Smooth X.hom] [IsProper Z.hom]
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hZ : Smooth ((changeBase (rationalMap hm)).obj Z).hom)
    (hq : Smooth q₀.left) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z),
      ProjectionCompatibility φ (rationalMap hn) hφ p q₀ ∧
        Smooth p.left ∧ Smooth ((changeBase φ).obj Z).hom := by
  have : IsNoetherianRing (BaseRing.{u} m) := arithmeticBase_isNoetherian m
  have : LocallyOfFinitePresentation Z.hom := finitePresentation_of_proper Z
  obtain ⟨stage⟩ := exists_arithmetic_projection_stage (X := X) (Z := Z) hm q₀
  exact restrict_smooth_stage hm q₀ hZ hq stage

private theorem exists_smooth_projection_stage {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)} [IsAffine X.left] [Smooth X.hom] [IsProper Z.hom]
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hZ : Smooth ((changeBase (rationalMap hm)).obj Z).hom)
    (hq : Smooth q₀.left) :
    ∃ stage : ArithmeticProjectionStage hm q₀,
      Smooth stage.projection.left ∧ Smooth ((changeBase stage.ringMap).obj Z).hom := by
  obtain ⟨n, hn, hd, φ, hInt, hφ, p, hp, hpSmooth, hZ'⟩ :=
    exists_smooth_arithmetic_projection hm q₀ hZ hq
  exact ⟨⟨n, hn, hd, φ, hInt, hφ, p, hp⟩, hpSmooth, hZ'⟩

private theorem refine_split_projection {m m₁ : ℕ} (hm : m ≠ 0) (hm₁ : m₁ ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)}
    (φ₁ : BaseRing.{u} m →+* BaseRing.{u} m₁) (hd₁ : m ∣ m₁)
    (hInt₁ : φ₁.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
      algebraMap (ULift.{u} ℤ) (BaseRing.{u} m₁))
    (hφ₁ : (rationalMap hm₁).comp φ₁ = rationalMap hm)
    (p₁ : (changeBase φ₁).obj X ⟶ (changeBase φ₁).obj Z)
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hp₁ : ProjectionCompatibility φ₁ (rationalMap hm₁) hφ₁ p₁ q₀)
    [Smooth ((changeBase φ₁).obj X).hom] [IsProper ((changeBase φ₁).obj Z).hom]
    [Smooth ((changeBase φ₁).obj Z).hom] (hq₁ : Smooth p₁.left)
    (hs₁η : HasLocalSections ((changeBase (rationalMap hm₁)).map p₁)) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z),
      ProjectionCompatibility φ (rationalMap hn) hφ p q₀ ∧
        Smooth p.left ∧ Smooth ((changeBase φ).obj Z).hom ∧ HasLocalSections p := by
  obtain ⟨n, hn, hd₂, β, hInt₂, hpβ⟩ := exists_split_arithmetic_restriction hm₁ p₁ hs₁η
  let φ := β.comp φ₁
  have hInt := integerMap_comp φ₁ β hInt₁ hInt₂
  have hφ := rationalMap_comp_refinement hm hn φ hInt
  have hβ := rationalMap_comp_refinement hm₁ hn β hInt₂
  refine ⟨n, hn, hd₁.trans hd₂, φ, hInt, hφ, ?_⟩
  exact split_of_refined_projection φ₁ β (rationalMap hn) hβ hφ₁ hφ p₁ q₀ hp₁ hq₁ inferInstance hpβ

private theorem restrict_split_stage {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)} [IsAffine X.left] [Smooth X.hom] [IsProper Z.hom]
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hs : HasLocalSections q₀)
    (stage : ArithmeticProjectionStage hm q₀)
    (hq₁ : Smooth stage.projection.left) (hZ₁ : Smooth ((changeBase stage.ringMap).obj Z).hom) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z),
      ProjectionCompatibility φ (rationalMap hn) hφ p q₀ ∧
        Smooth p.left ∧ Smooth ((changeBase φ).obj Z).hom ∧ HasLocalSections p := by
  let φ₁ := stage.ringMap
  let κ₁ := rationalMap stage.nonzero
  let p₁ := stage.projection
  have hs₁η := sections_of_baseComparison φ₁ κ₁ stage.rational p₁ q₀ stage.comparison hs
  have : Smooth ((changeBase φ₁).obj X).hom := baseChange_structureProperty @Smooth φ₁ X inferInstance
  have : Smooth ((changeBase φ₁).obj Z).hom := hZ₁
  have : IsProper ((changeBase φ₁).obj Z).hom := baseChange_structureProperty @IsProper φ₁ Z inferInstance
  exact refine_split_projection hm stage.nonzero φ₁ stage.divides stage.integers
    stage.rational p₁ q₀ stage.comparison hq₁ hs₁η

private theorem exists_split_arithmetic_projection {m : ℕ} (hm : m ≠ 0)
    {X Z : SchemeOverRing (BaseRing.{u} m)} [IsAffine X.left] [Smooth X.hom] [IsProper Z.hom]
    (q₀ : (changeBase (rationalMap hm)).obj X ⟶ (changeBase (rationalMap hm)).obj Z)
    (hZ : Smooth ((changeBase (rationalMap hm)).obj Z).hom)
    (hq : Smooth q₀.left) (hs : HasLocalSections q₀) :
    ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n) (φ : BaseRing.{u} m →+* BaseRing.{u} n)
      (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
        algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
      (hφ : (rationalMap hn).comp φ = rationalMap hm)
      (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z),
      ProjectionCompatibility φ (rationalMap hn) hφ p q₀ ∧
        Smooth p.left ∧ Smooth ((changeBase φ).obj Z).hom ∧ HasLocalSections p := by
  obtain ⟨stage, hq₁, hZ₁⟩ := exists_smooth_projection_stage hm q₀ hZ hq
  exact restrict_split_stage hm q₀ hs stage hq₁ hZ₁

section FinalCompatibility

variable {A B K : Type u} [CommRing A] [CommRing B] [CommRing K]

private theorem genericKernelPair_of_comparedProjection (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) {G H : Grp (SchemeOverRing A)} (i : H ⟶ G)
    {Z : SchemeOverRing A} {Y : SchemeOverRing K} (eY : Y ≅ (changeBase κ).obj Z)
    (q : ((changeBaseGroup κ).obj G).X ⟶ Y)
    (p : ((changeBaseGroup φ).obj G).X ⟶ (changeBase φ).obj Z)
    (hp : ProjectionCompatibility φ ψ h p (q ≫ eY.hom))
    (hi : IsPullback prod.fst (rightMultiply ((changeBaseGroup κ).map i)) q q) :
    IsPullback prod.fst
      (rightMultiply ((changeBaseGroup ψ).map ((changeBaseGroup φ).map i)))
      ((changeBase ψ).map p) ((changeBase ψ).map p) := by
  subst κ
  let e := changeBaseComp φ ψ
  have he : changeBaseAlongComp φ ψ rfl = e := by simp [changeBaseAlongComp, e]
  have hd := ProjectionCompatibility.comm hp
  rw [he] at hd
  obtain ⟨eG, heG⟩ := groupIsoWithUnderlyingComparison e
  let e' := eY ≪≫ e.app Z
  have hcomp : q ≫ e'.hom = (groupIsoUnderlying (eG.app G)).hom ≫ (changeBase ψ).map p := by
    change q ≫ (eY.hom ≫ e.hom.app Z) = (eG.hom.app G).hom.hom ≫ (changeBase ψ).map p
    rw [heG G, ← Category.assoc]
    exact hd.symm
  exact kernelPair_transport _ _ (eG.app G) (eG.app H) (eG.hom.naturality i) e' _ _ hcomp hi

private theorem rationalFibre_of_comparedModel (φ : A →+* B) (ψ : B →+* K) {κ : A →+* K}
    (h : ψ.comp φ = κ) {X Z : SchemeOverRing A} {Y : SchemeOverRing K}
    (eY : Y ≅ (changeBase κ).obj Z)
    (q : (changeBase κ).obj X ⟶ Y)
    (p : (changeBase φ).obj X ⟶ (changeBase φ).obj Z)
    (hp : ProjectionCompatibility φ ψ h p (q ≫ eY.hom)) :
    RationalFibreComparison φ ψ h p q := by
  subst κ
  let e := changeBaseComp φ ψ
  have he : changeBaseAlongComp φ ψ rfl = e := by simp [changeBaseAlongComp, e]
  have hd := ProjectionCompatibility.comm hp
  unfold RationalFibreComparison
  rw [he] at hd ⊢
  exact ⟨eY ≪≫ e.app Z, hd.trans (Category.assoc _ _ _)⟩

end FinalCompatibility

/-- A smooth, locally split projective right torsor on the rational fibre
spreads over one further arithmetic localization. -/
theorem spreadProjectiveRightTorsor : Statement.{u} := by
  intro m hm G H i hGa hHa hG hH hI Y hY V _ _ _ j hj q hq hqs hpair hsec
  let R := BaseRing.{u} m
  let F := ULift.{u} ℚ
  let κ := rationalMap hm
  letI : Algebra R F := κ.toAlgebra
  have : IsDomain R := arithmeticBase_isDomain m hm
  have : IsFractionRing R F := arithmeticGeneric_isFractionRing m hm
  let T : SchemeOverRing F := Over.mk (𝟙 (Spec (CommRingCat.of F)))
  let x : T ⟶ ((changeBaseGroup κ).obj G).X := 1
  let y := q.left (x.left (⊥ : PrimeSpectrum F))
  obtain ⟨d, Z, j₀, hj₀, hZ, _, eY, _⟩ := exists_projective_model (nonZeroDivisors R) y V j hj
  change Y ≅ (changeBase (rationalMap hm)).obj Z at eY
  as_aux_lemma =>
    have : IsAffine G.X.left := hGa
    have : Smooth G.X.hom := hG
    have : IsProper Z.hom := hZ
    obtain ⟨hZη, hq₀, hs₀⟩ := targetIsoProperties q eY hY hq hsec
    obtain ⟨n, hn, hd, φ, hInt, hφ, p, hp, hpSmooth, hY', hpSections⟩ :=
      exists_split_arithmetic_projection (X := G.X) hm (q ≫ eY.hom) hZη hq₀ hs₀
    as_aux_lemma =>
      let G' := (changeBaseGroup φ).obj G
      let H' := (changeBaseGroup φ).obj H
      let Y' := (changeBase φ).obj Z
      let i' : H' ⟶ G' := (changeBaseGroup φ).map i
      have hG' : Smooth G'.X.hom := baseChange_structureProperty @Smooth φ G.X hG
      have hH' : Smooth H'.X.hom := baseChange_structureProperty @Smooth φ H.X hH
      have hi' : IsClosedImmersion i'.hom.hom.left := baseChange_morphismProperty @IsClosedImmersion φ i.hom.hom hI
      have : IsProper Y'.hom := baseChange_structureProperty @IsProper φ Z hZ
      have hsep : IsSeparated Y'.hom := inferInstance
      have hpairη : IsPullback prod.fst
          (rightMultiply ((changeBaseGroup (rationalMap hn)).map ((changeBaseGroup φ).map i)))
          ((changeBase (rationalMap hn)).map p) ((changeBase (rationalMap hn)).map p) := by
        as_aux_lemma =>
          exact genericKernelPair_of_comparedProjection φ (rationalMap hn) hφ i eY q p hp hpair
      have hpPair : IsPullback prod.fst (rightMultiply i') p p :=
        @kernelPair_on_arithmetic_model n hn G' H' i' Y' p hG' hH' hi' hsep hpSmooth hpairη
      have hcmp : RationalFibreComparison φ (rationalMap hn) hφ p q :=
        rationalFibre_of_comparedModel φ (rationalMap hn) hφ eY q p hp
      obtain ⟨j', hj'⟩ := projectedClosedImmersion φ d j₀ hj₀
      have hflat : Flat Y'.hom := by
        letI : Smooth Y'.hom := hY'
        infer_instance
      exact ⟨n, hn, hd, φ, hInt, hφ, Y', hY', hflat,
        ⟨d, j', hj'⟩, p, hpSmooth, surjective_of_localSections p hpSections, hpPair, hpSections, hcmp⟩

end SpreadingAssembly

end

end LinearAlgebraicGroups.Representation.SpreadProjectiveRightTorsor
