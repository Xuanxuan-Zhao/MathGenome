import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepIntersectionComplex
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionUnitCone
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace Topology
open scoped ZeroObject
set_option linter.style.haveILetI false

namespace RepTheorySurvey.Geometric.ConvolutionSplitting

open Analytic LocalSheaf
open Analytic.IntersectionComplex (shiftedConstant point)
open ConvolutionUnitConeSpecs ConvolutionSplittingSpecs
open LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionSurfaceSpecs

open private closedShriekOpenIso embeddingIsoOfRange embeddingIsoOfRange_comp
  pullbackStalkIso pullbackCohomologyIso plusIsGE_iff locallyConstantFiniteRank_of_iso
  zero_locallyConstantFiniteRank supportedShriekIso exactCohomologyIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
open private cohomologyOfShiftedPlus univShriekIso shiftedCohomologyZero
  shiftedCohomologyAtDegree locallyConstantRational rationalStalk from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TwoStepIntersectionComplex

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

set_option backward.isDefEq.respectTransparency false in
private theorem splittingFor {x : surface} {hx : IsClosed ({x} : Set surface)}
    (e : unitCone ≅ pointSkyscraper x hx)
    (hT : unitTriangle ∈ distTriang (Derived surface))
    (hδ : unitTriangle.mor₃ = 0)
    (hHom : Subsingleton (pointSkyscraper x hx ⟶ unitTriangle.obj₁)) : SplittingFor e := by
  obtain ⟨b, hb₁, hb₂⟩ := exists_iso_binaryBiproduct_of_distTriang unitTriangle hT hδ
  let f := biprod.mapIso (Iso.refl unitTriangle.obj₁) e.symm ≪≫ b.symm
  let s : pointSkyscraper x hx ⟶ convolution.obj := biprod.inr ≫ f.hom
  have hq : f.hom ≫ quotientMap e = biprod.snd := by
    simp only [f, Iso.trans_hom, Iso.symm_hom, quotientMap, Category.assoc]
    rw [hb₂]
    simp
  have hs : s ≫ quotientMap e = 𝟙 _ := by
    rw [show s = biprod.inr ≫ f.hom from rfl, Category.assoc, hq, biprod.inr_snd]
  refine ⟨s, hs, ?_, f, ?_, rfl⟩
  · intro s' hs'
    have hz : (s' - s) ≫ unitTriangle.mor₂ = 0 := by
      apply (cancel_mono e.hom).mp
      rw [Category.assoc, zero_comp]
      change (s' - s) ≫ quotientMap e = 0
      rw [Preadditive.sub_comp, hs', hs, sub_self]
    obtain ⟨r, hr⟩ := unitTriangle.coyoneda_exact₂ hT (s' - s) hz
    rw [hHom.elim r 0, zero_comp] at hr
    exact sub_eq_zero.mp hr
  · have hu : biprod.inl ≫ b.inv = unitTriangle.mor₁ := by
      rw [← hb₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change biprod.inl ≫ (biprod.map (𝟙 unitTriangle.obj₁) e.inv ≫ b.inv) = unitTriangle.mor₁
    rw [biprod.inl_map_assoc]
    exact (Category.id_comp _).trans hu

/-- The scheme-point and short-window lattice topologies both use the same
embedding in the Grassmannian. The comparison preserves the scalar lattice. -/
private theorem surfaceComparison (x : surface) (hx : ScalarTerminalPoint x) :
    ∃ (h : scalarPoint ∈ colength 2) (e : surface ≃ₜ TwoStepIntersectionComplexSpecs.X),
      e x = TwoStepIntersectionComplexSpecs.vertex h := by
  obtain ⟨h, _, E, P, _, _, _, _, _, hP, _, hE⟩ :=
    TwoStepIntersectionComplex.smoothOpenOrbit
  let incl := fun q : surface => q ≫ twoStepSchemeInGrassmannian
  have hp : IsInducing (P : surface → TwoStepPoints) := by
    constructor
    change TopologicalSpace.induced incl _ =
      TopologicalSpace.induced P (TopologicalSpace.induced (fun p : TwoStepPoints => p.val) _)
    rw [induced_compose]
    congr 1
    exact (funext hP).symm
  let e := (IsEmbedding.mk hp P.injective).toHomeomorphOfSurjective P.surjective
  refine ⟨h, e.trans E.symm, ?_⟩
  change E.symm (P x) = _
  apply (Homeomorph.symm_apply_eq E).mpr
  apply Subtype.ext
  apply grassmannianSubspace_injective twoStepBasis twoStepRank
  exact (congrArg (grassmannianSubspace twoStepBasis twoStepRank) (hP x)).trans
    (hx.2.1.trans (hE (TwoStepIntersectionComplexSpecs.vertex h)).1.symm)

private def shiftedPullback {Y X : TopCat} (m : Y ⟶ X) (d : ℕ) :
    (boundedBelowInverseImage m).obj (shiftedConstant X d) ≅ shiftedConstant Y d :=
  ObjectProperty.isoMk _ (shiftedConstantPullback m d)

private abbrev shiftedCostalk (x : surface) (hx : IsClosed ({x} : Set surface))
    (d : ℕ) (q : ℤ) : Coeff.{0} :=
  (DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk (⟨x, rfl⟩ : ({x} : Set surface))).obj
    ((derivedExtraordinaryInverseImage hx).obj (shiftedConstant surface d))

private theorem normalizedCostalk (x : surface) (hx : IsClosed ({x} : Set surface))
    (hscalar : ScalarTerminalPoint x) (q : ℤ) (hq : q ≠ 2) :
    IsZero (shiftedCostalk x hx 2 q) := by
  obtain ⟨h, E, hE⟩ := surfaceComparison x hscalar
  let y := TwoStepIntersectionComplexSpecs.vertex h
  let k := (TopCat.isoOfHomeo E).inv
  have hk : IsOpenEmbedding k := E.symm.isOpenEmbedding
  have hyx : k y = x := E.symm_apply_eq.mpr hE.symm
  have hy : IsClosed ({y} : Set TwoStepIntersectionComplexSpecs.X) := by
    have he : k ⁻¹' ({x} : Set surface) = {y} := by
      ext a
      change k a = x ↔ a = y
      exact ⟨fun ha => E.symm.injective (ha.trans hyx.symm), fun ha => ha ▸ hyx⟩
    rw [← he]
    exact hx.preimage k.hom.continuous
  let i := closedInclusion ({x} : Set surface)
  let j := closedInclusion ({y} : Set TwoStepIntersectionComplexSpecs.X)
  have hj : IsEmbedding (j ≫ k) := hk.isEmbedding.comp IsEmbedding.subtypeVal
  have hr : Set.range i = Set.range (j ≫ k) := by
    rw [show Set.range i = {x} from Subtype.range_coe]
    ext a
    constructor
    · intro ha
      exact ⟨⟨y, rfl⟩, hyx.trans (Set.mem_singleton_iff.mp ha).symm⟩
    · rintro ⟨z, rfl⟩
      change k z.val = x
      rw [Set.mem_singleton_iff.mp z.property, hyx]
  let v := embeddingIsoOfRange i (j ≫ k) IsEmbedding.subtypeVal hj hr
  let z : ({x} : Set surface) := ⟨x, rfl⟩
  let w : ({y} : Set TwoStepIntersectionComplexSpecs.X) := ⟨y, rfl⟩
  have hw : v.hom z = w := Subtype.ext (Set.mem_singleton_iff.mp (v.hom z).property)
  let F := shiftedConstant surface 2
  let G := (derivedExtraordinaryInverseImage hy).obj ((boundedBelowInverseImage k).obj F)
  let d := closedShriekOpenIso hx hy k hk v
    (embeddingIsoOfRange_comp i (j ≫ k) IsEmbedding.subtypeVal hj hr) F
  have e₁ : shiftedCostalk x hx 2 q ≅
      (DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk w).obj G := by
    rw [← hw]
    exact (DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk z).mapIso d ≪≫
      pullbackStalkIso v.hom G q z
  let e₂ := (DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk w).mapIso
    ((derivedExtraordinaryInverseImage hy).mapIso (shiftedPullback k 2))
  exact ((TwoStepIntersectionComplex.vertexCohomology h hy).2.2.2.2 q hq).of_iso (e₁ ≪≫ e₂)

private def costalkShiftIso (x : surface) (hx : IsClosed ({x} : Set surface)) (d : ℕ) (q : ℤ) :
    shiftedCostalk x hx d q ≅ pointCostalk x hx (q + (d : ℤ)) := by
  let F := sheafInDegreeZero (rational surface)
  let R := derivedExtraordinaryInverseImage hx
  let I := DerivedCategory.Plus.ι (C := Sheaves surface)
  let z : ({x} : Set surface) := ⟨x, rfl⟩
  letI : R.CommShift ℤ := by unfold R derivedExtraordinaryInverseImage; infer_instance
  let e : shiftedConstant surface d ≅ F⟦(d : ℤ)⟧ :=
    I.preimageIso ((I.commShiftIso (d : ℤ)).app F).symm
  exact (DerivedCategory.Plus.homologyFunctor _ q ⋙ stalk z).mapIso
    (R.mapIso e ≪≫ (R.commShiftIso (d : ℤ)).app F) ≪≫
    (stalk z).mapIso (cohomologyOfShiftedPlus (R.obj F) q (d : ℤ))

private theorem costalkVanishes (x : surface) (hx : IsClosed ({x} : Set surface))
    (hscalar : ScalarTerminalPoint x) (q : ℤ) (hq : q ≠ 4) : IsZero (pointCostalk x hx q) := by
  have h := normalizedCostalk x hx hscalar (q - 2) (by omega)
  have e := costalkShiftIso x hx 2 (q - 2)
  simp only [Nat.cast_ofNat, sub_add_cancel] at e
  exact h.of_iso e.symm

private theorem vanishingCostalkHom (x : surface) (hx : IsClosed ({x} : Set surface))
    (hscalar : ScalarTerminalPoint x) (d : ℕ) (hd : (d : ℤ) < 4) :
    VanishingCostalkHom x hx d := by
  let Z := TopCat.of ({x} : Set surface)
  let z : Z := ⟨x, rfl⟩
  let F := shiftedConstant surface d
  let G := point x
  let R := derivedExtraordinaryInverseImage hx
  let L := closedExtensionPlus hx
  let a := DerivedLocalSheaves.derivedExtraordinaryAdjunctionData hx
  letI : (closedExtensionPlus hx).Additive := by
    unfold closedExtensionPlus exactDerivedPlus
    infer_instance
  have hG : G.IsLE 0 := inferInstanceAs
    (((DerivedCategory.Plus.singleFunctor (Sheaves Z) 0).obj (rational Z)).IsLE 0)
  have hR : (R.obj F).IsGE 1 := (plusIsGE_iff _ _).mpr fun q hq => by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro t
    have ht : t = z := Subtype.ext (Set.mem_singleton_iff.mp t.property)
    subst t
    exact (costalkVanishes x hx hscalar (q + (d : ℤ)) (by omega)).of_iso
      (costalkShiftIso x hx d q)
  have hs (f : pointSkyscraper x hx ⟶ F.obj) : f = 0 := by
    let f' : L.obj G ⟶ F := ObjectProperty.homMk f
    suffices hf : f' = 0 from congrArg (fun k : L.obj G ⟶ F => k.hom) hf
    apply (a.homEquiv G F).injective
    rw [a.homAddEquiv_zero]
    exact DerivedCategory.Plus.TStructure.t.zero_of_isLE_of_isGE _ 0 1 (by decide) hG hR
  letI : Subsingleton (pointSkyscraper x hx ⟶ F.obj) := ⟨fun f g => (hs f).trans (hs g).symm⟩
  have hz := costalkVanishes x hx hscalar (d : ℤ) hd.ne
  letI : Subsingleton (pointCostalk x hx (d : ℤ)) := ModuleCat.isZero_iff_subsingleton.mp hz
  let H := DerivedCategory.Plus.homologyFunctor (Sheaves Z) 0 ⋙ stalk z
  let e : ModuleCat.of ℚ ℚ ≅ H.obj G :=
    (rationalStalk z).symm ≪≫
      (stalk z).mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _).symm
  let c : H.obj (R.obj F) ≅ pointCostalk x hx (d : ℤ) := by
    simpa only [zero_add] using costalkShiftIso x hx d 0
  exact ⟨⟨{ toFun := fun f =>
              (e.hom ≫ H.map (a.homEquiv G F (ObjectProperty.homMk f)) ≫ c.hom) (1 : ℚ)
            invFun := fun _ => 0
            left_inv := fun _ => Subsingleton.elim _ _
            right_inv := fun _ => Subsingleton.elim _ _
            map_add' := fun _ _ => Subsingleton.elim _ _ }⟩, hz, inferInstance⟩

private def closedOrbitPointIso (x : surface) (hx : IsClosed ({x} : Set surface)) :
    TopCat.of ({x} : Set surface) ≅ (closedOrbitStratum x hx).space :=
  embeddingIsoOfRange (closedInclusion {x}) (closedOrbitStratum x hx).inclusion
    IsEmbedding.subtypeVal
    ((closedOrbitStratum x hx).ambientOpen.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
    (Subtype.range_coe.trans (closedOrbitStratum_range x hx).symm)

private theorem closedOrbitPointIso_comp (x : surface) (hx : IsClosed ({x} : Set surface)) :
    (closedOrbitPointIso x hx).hom ≫ (closedOrbitStratum x hx).inclusion = closedInclusion {x} :=
  embeddingIsoOfRange_comp _ _ _ _ _

/-- The open stratum uses ordinary restriction. On the closed stratum use the
extraordinary inverse image along the closed singleton. -/
private theorem middlePerverseOfOrbitBounds {x : surface} {hx : IsClosed ({x} : Set surface)}
    (F : BoundedBelow surface)
    (hF : IsConstructible (orbitStratification x hx) F.obj)
    (hbelow : ∀ q : ℤ, q < -2 → IsZero ((cohomology surface q).obj F.obj))
    (habove : ∀ q : ℤ, 0 < q → IsZero ((cohomology surface q).obj F.obj))
    (hopen : ∀ q : ℤ, -2 < q → IsZero
      (((cohomology surface q) ⋙ inverseImage (openOrbitStratum x hx).inclusion).obj F.obj))
    (hclosed : ∀ q : ℤ, q < 0 →
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((derivedExtraordinaryInverseImage hx).obj F))) :
    IsMiddlePerverse (orbitStratification x hx) F.obj := by
  refine ⟨hF, F.property, ?_⟩
  rintro (_ | _)
  · let S := closedOrbitStratum x hx
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · change 0 < q at hq
      exact ((inverseImage S.inclusion).map_isZero (habove q hq)).of_iso
        (pullbackCohomologyIso S.inclusion F q)
    · change q < 0 at hq
      let k := openInclusion S.ambientOpen
      let v := closedOrbitPointIso x hx
      let d := closedShriekOpenIso hx S.closed k S.ambientOpen.isOpenEmbedding v
        (closedOrbitPointIso_comp x hx) F
      apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
      intro y
      let H := DerivedCategory.Plus.homologyFunctor (Sheaves (TopCat.of ({x} : Set surface))) q
      let z := v.inv y
      have hy : v.hom z = y := congrArg (fun f : S.space ⟶ S.space => f y) v.inv_hom_id
      have e := (H ⋙ stalk z).mapIso d ≪≫ pullbackStalkIso v.hom (S.shriek.obj F) q z
      rw [hy] at e
      exact ((stalk z).map_isZero (hclosed q hq)).of_iso e.symm
  · let S := openOrbitStratum x hx
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · change -2 < q at hq
      exact (hopen q hq).of_iso (pullbackCohomologyIso S.inclusion F q)
    · change q < -2 at hq
      let A := TopCat.of S.ambientOpen
      let j := openInclusion S.ambientOpen
      let i : S.space ⟶ A := closedInclusion (Set.univ : Set A)
      let G := (boundedBelowInverseImage j).obj F
      let e : S.shriek.obj F ≅ (boundedBelowInverseImage i).obj G := (univShriekIso A).app G
      exact ((inverseImage i).map_isZero
        (((inverseImage j).map_isZero (hbelow q hq)).of_iso (pullbackCohomologyIso j F q))).of_iso
          ((DerivedCategory.Plus.homologyFunctor (Sheaves S.space) q).mapIso e ≪≫
            pullbackCohomologyIso i G q)

private theorem constructibleOfCohomology {x : surface} {hx : IsClosed ({x} : Set surface)}
    (F : BoundedBelow surface)
    (hF : ∀ q : ℤ, q ≠ -2 → q ≠ 0 → IsZero ((cohomology surface q).obj F.obj))
    (hr : ∀ (b : Bool) (q : ℤ),
      LocallyConstantFiniteRank
        ((inverseImage ((orbitStratification x hx).stratum b).inclusion).obj
          ((cohomology surface q).obj F.obj))) :
    IsConstructible (orbitStratification x hx) F.obj := by
  refine ⟨((Set.finite_singleton (0 : ℤ)).insert (-2)).subset ?_, hr⟩
  intro q hq
  by_contra h
  exact hq (hF q (fun hq' => h (Or.inl hq')) (fun hq' => h (Or.inr hq')))

private theorem normalizedPerverse (x : surface) (hx : IsClosed ({x} : Set surface))
    (hscalar : ScalarTerminalPoint x) :
    IsMiddlePerverse (orbitStratification x hx) (shiftedConstant surface 2).obj := by
  let F := shiftedConstant surface 2
  have hz (q : ℤ) (h : q ≠ -2) : IsZero ((cohomology surface q).obj F.obj) :=
    shiftedCohomologyZero surface q h
  apply middlePerverseOfOrbitBounds F
  · refine constructibleOfCohomology F (fun q hq _ => hz q hq) ?_
    intro b q
    let m := ((orbitStratification x hx).stratum b).inclusion
    by_cases hq : q = -2
    · subst q
      let e := (inverseImage m).mapIso (shiftedCohomologyAtDegree surface) ≪≫ constantPullback m
      exact locallyConstantFiniteRank_of_iso e.symm (locallyConstantRational _)
    · exact zero_locallyConstantFiniteRank ((inverseImage m).map_isZero (hz q hq))
  · exact fun q hq => hz q (by omega)
  · exact fun q hq => hz q (by omega)
  · exact fun q hq => (inverseImage _).map_isZero (hz q (by omega))
  · intro q hq
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro z
    have h : z = (⟨x, rfl⟩ : ({x} : Set surface)) :=
      Subtype.ext (Set.mem_singleton_iff.mp z.property)
    subst z
    exact normalizedCostalk x hx hscalar q (by omega)

private abbrev skyscraperPlus (x : surface) (hx : IsClosed ({x} : Set surface)) :
    BoundedBelow surface :=
  (closedExtensionPlus hx).obj (point x)

private theorem pointCohomologyZero (x : surface) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj (point x)) := by
  let Z := TopCat.of ({x} : Set surface)
  let G := (DerivedCategory.Plus.singleFunctor (Sheaves Z) 0).obj (rational Z)
  rcases lt_or_gt_of_ne hq with h | h
  · have hG : G.IsGE 0 := inferInstanceAs
      (((DerivedCategory.Plus.singleFunctor (Sheaves Z) 0).obj (rational Z)).IsGE 0)
    exact (DerivedCategory.isGE_iff G.obj 0).mp
      ((DerivedCategory.Plus.isGE_ι_obj_iff G 0).mpr hG) q h
  · have hG : G.IsLE 0 := inferInstanceAs
      (((DerivedCategory.Plus.singleFunctor (Sheaves Z) 0).obj (rational Z)).IsLE 0)
    exact (DerivedCategory.isLE_iff G.obj 0).mp
      ((DerivedCategory.Plus.isLE_ι_obj_iff G 0).mpr hG) q h

private theorem skyscraperCohomologyZero (x : surface) (hx : IsClosed ({x} : Set surface))
    (q : ℤ) (hq : q ≠ 0) :
    IsZero ((cohomology surface q).obj (skyscraperPlus x hx).obj) := by
  let i := directImage (closedInclusion ({x} : Set surface))
  letI := (extraordinaryAdjunction hx).isLeftAdjoint
  exact (i.map_isZero (pointCohomologyZero x q hq)).of_iso (exactCohomologyIso i (point x) q)

private def skyscraperCohomologyAtZero (x : surface) (hx : IsClosed ({x} : Set surface)) :
    (cohomology surface 0).obj (skyscraperPlus x hx).obj ≅
      (directImage (closedInclusion ({x} : Set surface))).obj (rational (TopCat.of ({x} : Set surface))) := by
  let i := directImage (closedInclusion ({x} : Set surface))
  letI := (extraordinaryAdjunction hx).isLeftAdjoint
  exact exactCohomologyIso i (point x) 0 ≪≫
    i.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _)

private theorem skyscraperOpenZero (x : surface) (hx : IsClosed ({x} : Set surface)) (q : ℤ) :
    IsZero ((inverseImage (openOrbitStratum x hx).inclusion).obj
      ((cohomology surface q).obj (skyscraperPlus x hx).obj)) := by
  let m := (openOrbitStratum x hx).inclusion
  by_cases hq : q = 0
  · subst q
    let G := rational (TopCat.of ({x} : Set surface))
    let H := (directImage (closedInclusion ({x} : Set surface))).obj G
    apply IsZero.of_iso ?_ ((inverseImage m).mapIso (skyscraperCohomologyAtZero x hx))
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro y
    have hy : m y ∉ ({x} : Set surface) := y.val.property
    exact (closedDirectImage_supported hx G (m y) hy).of_iso
      (inverseImageStalkIso m H y).symm
  · exact (inverseImage m).map_isZero (skyscraperCohomologyZero x hx q hq)

private theorem skyscraperPerverse (x : surface) (hx : IsClosed ({x} : Set surface)) :
    IsMiddlePerverse (orbitStratification x hx) (skyscraperPlus x hx).obj := by
  let F := skyscraperPlus x hx
  have hz := skyscraperCohomologyZero x hx
  apply middlePerverseOfOrbitBounds F
  · refine constructibleOfCohomology F (fun q _ hq => hz q hq) ?_
    rintro (_ | _) q
    · let S := closedOrbitStratum x hx
      by_cases hq : q = 0
      · subst q
        let v := closedOrbitPointIso x hx
        let i := closedInclusion ({x} : Set surface)
        let A := rational (TopCat.of ({x} : Set surface))
        let H := (directImage i).obj A
        have hi : S.inclusion = v.inv ≫ i := by
          change S.inclusion = v.inv ≫ closedInclusion {x}
          rw [← closedOrbitPointIso_comp x hx, ← Category.assoc, v.inv_hom_id, Category.id_comp]
        let e := (inverseImage S.inclusion).mapIso (skyscraperCohomologyAtZero x hx) ≪≫
          eqToIso (congrArg (fun f => (inverseImage f).obj H) hi) ≪≫
          (inverseImageComposition v.inv i).app H ≪≫
          (inverseImage v.inv).mapIso
            (letI := inducedCounit_isIso (f := i) IsInducing.subtypeVal A
             asIso ((inverseDirectAdjunction i).counit.app A)) ≪≫ constantPullback v.inv
        exact locallyConstantFiniteRank_of_iso e.symm (locallyConstantRational _)
      · exact zero_locallyConstantFiniteRank ((inverseImage S.inclusion).map_isZero (hz q hq))
    · exact zero_locallyConstantFiniteRank (skyscraperOpenZero x hx q)
  · exact fun q hq => hz q (by omega)
  · exact fun q hq => hz q (by omega)
  · exact fun q _ => skyscraperOpenZero x hx q
  · intro q hq
    let e : point x ≅ (derivedExtraordinaryInverseImage hx).obj F :=
      supportedShriekIso hx (Iso.refl F)
    exact (pointCohomologyZero x q (by omega)).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ q).mapIso e.symm)

private theorem perverseOfSplit {x : surface} {hx : IsClosed ({x} : Set surface)}
    (h₁ : IsMiddlePerverse (orbitStratification x hx) (shiftedConstant surface 2).obj)
    (h₂ : IsMiddlePerverse (orbitStratification x hx) (skyscraperPlus x hx).obj)
    (e : ((shiftedConstant surface 2).obj ⊞ pointSkyscraper x hx) ≅ convolution.obj) :
    IsMiddlePerverse (orbitStratification x hx) convolution.obj := by
  let Q := orbitStratification x hx
  let F := shiftedConstant surface 2
  let G := skyscraperPlus x hx
  let I := DerivedCategory.Plus.ι (C := Sheaves surface)
  let b : F ⊞ G ≅ convolution := I.preimageIso (I.mapBiprod F G ≪≫ e)
  have hcoh (q : ℤ) :
      (cohomology surface q).obj convolution.obj ≅
        ((cohomology surface q).obj F.obj ⊞ (cohomology surface q).obj G.obj) :=
    (cohomology surface q).mapIso e.symm ≪≫ (cohomology surface q).mapBiprod _ _
  refine ⟨constructibleOfCohomology convolution ?_ ?_, convolution.property, ?_⟩
  · intro q hq hq'
    exact ((biprod_isZero_iff _ _).mpr
      ⟨shiftedCohomologyZero surface q hq, skyscraperCohomologyZero x hx q hq'⟩).of_iso (hcoh q)
  · intro s q
    let L := inverseImage (Q.stratum s).inclusion
    let d := L.mapIso (hcoh q) ≪≫ L.mapBiprod _ _
    by_cases hq : q = -2
    · let hz := L.map_isZero (skyscraperCohomologyZero x hx q (by omega))
      exact locallyConstantFiniteRank_of_iso ((isoBiprodZero hz) ≪≫ d.symm) (h₁.1.2 s q)
    · let hz := L.map_isZero (shiftedCohomologyZero surface q hq)
      exact locallyConstantFiniteRank_of_iso ((isoZeroBiprod hz) ≪≫ d.symm) (h₂.1.2 s q)
  · intro s
    let S := Q.stratum s
    constructor
    · intro q hq
      let H := S.star ⋙ cohomology S.space q
      haveI : H.Additive := by unfold H Stratum.star derivedInverseImage; infer_instance
      let d := H.mapIso e.symm ≪≫ H.mapBiprod _ _
      exact ((biprod_isZero_iff _ _).mpr
        ⟨(h₁.2.choose_spec s).1 q hq, (h₂.2.choose_spec s).1 q hq⟩).of_iso d
    · intro q hq
      let H := S.shriek ⋙ DerivedCategory.Plus.homologyFunctor _ q
      let k := openInclusion S.ambientOpen
      letI : (boundedBelowInverseImage k).Additive := by
        letI : (derivedInverseImage k).Additive := by
          unfold derivedInverseImage
          infer_instance
        constructor
        intro A B f g
        apply ObjectProperty.hom_ext
        exact (derivedInverseImage k).map_add (f := f.hom) (g := g.hom)
      let R : BoundedBelow (TopCat.of S.ambientOpen) ⥤ BoundedBelow S.space :=
        derivedExtraordinaryInverseImage S.closed
      letI : R.Additive := by
        letI : R.IsRightAdjoint :=
          (DerivedLocalSheaves.derivedExtraordinaryAdjunctionData
            (X := TopCat.of S.ambientOpen) S.closed).isRightAdjoint
        exact Functor.additive_of_preserves_binary_products R
      haveI : H.Additive := by
        change ((boundedBelowInverseImage k ⋙ R) ⋙
          DerivedCategory.Plus.homologyFunctor _ q).Additive
        infer_instance
      let d := H.mapIso b.symm ≪≫ H.mapBiprod _ _
      exact ((biprod_isZero_iff _ _).mpr
        ⟨(h₁.2.choose_spec s).2 q hq, (h₂.2.choose_spec s).2 q hq⟩).of_iso d

/-- Split the ordinary derived unit triangle assuming the computation of its cone. -/
theorem convolutionSplitting_conditional
    (h : ConvolutionUnitConeSpecs.Expected.ConvolutionUnitCone) :
    ConvolutionSplittingSpecs.Expected.ConvolutionSplitting := by
  obtain ⟨_, _, x, hx, hscalar, _, _, _, hT, _, profile⟩ := h
  have h₂ := vanishingCostalkHom x hx hscalar 2 (by decide)
  have h₃ := vanishingCostalkHom x hx hscalar 3 (by decide)
  obtain ⟨e⟩ := profile.2.2
  have hδ : unitTriangle.mor₃ = 0 := by
    let d : (shiftedConstant surface 3).obj ≅ unitTriangle.obj₁⟦(1 : ℤ)⟧ :=
      (shiftFunctorAdd (Derived surface) (2 : ℤ) (1 : ℤ)).app
        ((sheafInDegreeZero (rational surface)).obj)
    have hz : e.inv ≫ unitTriangle.mor₃ ≫ d.inv = 0 := h₃.2.2.elim _ _
    apply (cancel_epi e.inv).mp
    apply (cancel_mono d.inv).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using hz
  have hs (a : unitCone ≅ pointSkyscraper x hx) : SplittingFor a :=
    splittingFor a hT hδ h₂.2.2
  have hA := normalizedPerverse x hx hscalar
  have hB := skyscraperPerverse x hx
  obtain ⟨_, _, _, f, _, _⟩ := hs e
  exact ⟨x, hx, hscalar, ⟨e⟩, h₂, h₃, hδ, hs, hA, hB, perverseOfSplit hA hB f⟩

/-- The canonical convolution unit splits with a unique section for each
identification of the cone with the rational skyscraper. -/
theorem convolutionSplitting : ConvolutionSplittingSpecs.Expected.ConvolutionSplitting :=
  convolutionSplitting_conditional ConvolutionUnitCone.convolutionUnitCone

end RepTheorySurvey.Geometric.ConvolutionSplitting
