import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertProjectionBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace Topology Geometry Set Opposite
open scoped ZeroObject

namespace RepTheorySurvey.Geometric.SchubertProjectionBaseChange

open Analytic Analytic.IntersectionComplex LocalSheaf
open SchubertProjectionBaseChangeSpecs
open SimplicialConstructibleDirectImage

open private openCounitIsIso pullbackStalkIso derivedIsZero closedInverseAdjunction
  rightDerivedExactIso constantPullbackIso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
open private pullbackCommShift pullbackTriangulated from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
open private derivedDirectImageOpenRestrictionIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

attribute [local instance] pullbackCommShift pullbackTriangulated

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

private def withParameter (T : TopCat.{0}) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    TopCat.of (T × X) ⟶ TopCat.of (T × Y) :=
  TopCat.ofHom ⟨fun p => (p.1, f p.2),
    continuous_fst.prodMk (f.hom.continuous.comp continuous_snd)⟩

private def projection (T X : TopCat.{0}) : TopCat.of (T × X) ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

private theorem projectionSquare (T : TopCat.{0}) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    withParameter T f ≫ projection T Y = projection T X ≫ f :=
  TopCat.ext (fun _ => rfl)

private theorem withParameter_open {X Y : TopCat.{0}} {f : X ⟶ Y}
    (T : TopCat.{0}) (hf : IsOpenEmbedding f) : IsOpenEmbedding (withParameter T f) :=
  IsOpenEmbedding.id.prodMap hf

/-- Restriction detects isomorphisms between objects in the image of an open direct image. -/
private theorem isIso_of_openRestriction {U X : TopCat.{0}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) {F G : BoundedBelow X} (m : F ⟶ G)
    (hF : (derivedDirectImage j).essImage F) (hG : (derivedDirectImage j).essImage G)
    (hm : IsIso ((boundedBelowInverseImage j).map m)) : IsIso m := by
  let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData j
  haveI (E : BoundedBelow U) : IsIso (a.counit.app E) := openCounitIsIso hj a E
  haveI : IsIso a.counit := NatIso.isIso_of_isIso_app _
  let ff := a.fullyFaithfulROfIsIsoCounit
  letI := ff.full
  letI := ff.faithful
  haveI : IsIso (a.unit.app F) := a.isIso_unit_app_iff_mem_essImage.mpr hF
  haveI : IsIso (a.unit.app G) := a.isIso_unit_app_iff_mem_essImage.mpr hG
  haveI : IsIso (m ≫ a.unit.app G) := by
    change IsIso ((𝟭 (BoundedBelow X)).map m ≫ a.unit.app G)
    rw [a.unit.naturality m]
    change IsIso (a.unit.app F ≫
      (derivedDirectImage j).map ((boundedBelowInverseImage j).map m))
    letI : IsIso ((boundedBelowInverseImage j).map m) := hm
    infer_instance
  exact IsIso.of_isIso_comp_right m (a.unit.app G)

private theorem isIso_map_adjointSquareMap {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R : D ⥤ B}
    (α : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (F : D)
    (ha : IsIso (a.counit.app (V.obj F))) (hb : IsIso (b.counit.app F)) :
    IsIso (J.map (adjointSquareMap α a b F)) := by
  let m := adjointSquareMap α a b F
  have hfac : J.map m ≫ a.counit.app (V.obj F) =
      α.hom.app (R.obj F) ≫ V.map (b.counit.app F) := by
    rw [← a.homEquiv_counit _ _ m]
    exact (a.homEquiv _ _).symm_apply_apply _
  haveI : IsIso (J.map m ≫ a.counit.app (V.obj F)) := by rw [hfac]; infer_instance
  exact IsIso.of_isIso_comp_right _ (a.counit.app (V.obj F))

private theorem comparison_isIso_on_open {U X V Y : TopCat.{0}} {j : U ⟶ X} {k : V ⟶ Y}
    {e : X ⟶ Y} {v : U ⟶ V} (h : j ≫ e = v ≫ k)
    (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage k ⊣ derivedDirectImage k) (F : BoundedBelow V) :
    IsIso ((boundedBelowInverseImage j).map (directImageComparison h a b F)) :=
  isIso_map_adjointSquareMap (pullbackSquare h) a b F
    (openCounitIsIso hj a _) (openCounitIsIso hk b F)

/-- Derived pullback along maps whose images cover detects isomorphisms. -/
private theorem isIso_of_pullback_cover {I : Type*} {X : TopCat.{0}} {U : I → TopCat.{0}}
    (a : ∀ i, U i ⟶ X) (cover : ∀ x : X, ∃ i y, a i y = x)
    {F G : BoundedBelow X} (m : F ⟶ G)
    (hm : ∀ i, IsIso ((boundedBelowInverseImage (a i)).map m)) : IsIso m := by
  obtain ⟨H, g, h, ht⟩ := distinguished_cocone_triangle m
  let T := Triangle.mk m g h
  have hz (i : I) : IsZero ((boundedBelowInverseImage (a i)).obj H) := by
    let L := boundedBelowInverseImage (a i)
    exact Triangle.isZero₃_of_isIso₁ (L.mapTriangle.obj T) (L.map_distinguished T ht)
      (show IsIso (L.map m) from hm i)
  have hH : IsZero H := derivedIsZero H (fun q => by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
    intro x
    obtain ⟨i, y, rfl⟩ := cover x
    exact IsZero.of_iso ((stalk y).map_isZero
      ((DerivedCategory.Plus.homologyFunctor _ q).map_isZero (hz i)))
      (pullbackStalkIso (a i) H q y).symm)
  exact (Triangle.isZero₃_iff_isIso₁ T ht).mp hH

private def ContractibleOpenBasis (X : TopCat.{0}) : Prop :=
  ∀ (x : X) (U : Opens X), x ∈ U →
    ∃ W : Opens X, W ≤ U ∧ x ∈ W ∧ ContractibleSpace (TopCat.of W)

private def HasContractiblePreimages {X Y : TopCat.{0}} (f : X ⟶ Y) : Prop :=
  ∀ (y : Y) (U : Opens Y), y ∈ U →
    ∃ W : Opens Y, W ≤ U ∧ y ∈ W ∧ ContractibleSpace (TopCat.of ((Opens.map f).obj W))

private theorem contractibleOpenBasis_of_coordinates {T : TopCat.{0}} {e : ℕ}
    {V : Opens (Fin e → ℂ)} (c : T ≃ₜ V) : ContractibleOpenBasis T := by
  intro t U ht
  let f : T → (Fin e → ℂ) := Subtype.val ∘ c
  have hf : IsOpenEmbedding f := V.isOpenEmbedding'.comp c.isOpenEmbedding
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hf.isOpenMap _ U.isOpen) (f t) ⟨t, ht, rfl⟩
  let W : Opens T := ⟨f ⁻¹' Metric.ball (f t) r, Metric.isOpen_ball.preimage hf.continuous⟩
  refine ⟨W, ?_, Metric.mem_ball_self hr, ?_⟩
  · intro y hy
    obtain ⟨z, hz, he⟩ := hball hy
    exact hf.injective he ▸ hz
  · have hsub : Metric.ball (f t) r ⊆ Set.range f :=
      hball.trans (Set.image_subset_range _ _)
    haveI : ContractibleSpace (Metric.ball (f t) r) :=
      (convex_ball (f t) r).contractibleSpace ⟨f t, Metric.mem_ball_self hr⟩
    exact (hf.isEmbedding.homeomorphOfSubsetRange hsub).contractibleSpace

private theorem hasContractiblePreimages_product {T X Y : TopCat.{0}} (f : X ⟶ Y)
    (hT : ContractibleOpenBasis T) (hf : HasContractiblePreimages f) :
    HasContractiblePreimages (withParameter T f) := by
  rintro ⟨t, y⟩ U h
  obtain ⟨A, B, hA, hB, htA, hyB, hAB⟩ := isOpen_prod_iff.mp U.isOpen t y h
  obtain ⟨A', hA', ht, hAc⟩ := hT t ⟨A, hA⟩ htA
  obtain ⟨B', hB', hy, hBc⟩ := hf y ⟨B, hB⟩ hyB
  let W : Opens (TopCat.of (T × Y)) := ⟨(A' : Set T) ×ˢ (B' : Set Y), A'.isOpen.prod B'.isOpen⟩
  refine ⟨W, (Set.prod_mono hA' hB').trans hAB, ⟨ht, hy⟩, ?_⟩
  let C := (Opens.map f).obj B'
  change ContractibleSpace (TopCat.of ((A' : Set T) ×ˢ (C : Set X)))
  letI := hAc
  letI := hBc
  exact (Homeomorph.Set.prod (A' : Set T) (C : Set X)).contractibleSpace

private theorem contractibleOpenBasis_product (T X : TopCat.{0})
    (hT : ContractibleOpenBasis T) (hX : ContractibleOpenBasis X) :
    ContractibleOpenBasis (TopCat.of (T × X)) := by
  rintro ⟨t, x⟩ U hx
  obtain ⟨A, B, hA, hB, htA, hxB, hAB⟩ := isOpen_prod_iff.mp U.isOpen t x hx
  obtain ⟨A', hA', ht, hAc⟩ := hT t ⟨A, hA⟩ htA
  obtain ⟨B', hB', hx', hBc⟩ := hX x ⟨B, hB⟩ hxB
  let W : Opens (TopCat.of (T × X)) := ⟨(A' : Set T) ×ˢ (B' : Set X), A'.isOpen.prod B'.isOpen⟩
  letI := hAc
  letI := hBc
  exact ⟨W, (Set.prod_mono hA' hB').trans hAB, ⟨ht, hx'⟩,
    (Homeomorph.Set.prod (A' : Set T) (B' : Set X)).contractibleSpace⟩

open private derivedOpenSectionsCohomologyIso constantDirectImageMap from
  MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

/-- Cofinal contractible preimages give the constant derived direct image. -/
private def derivedConstantImage {X : Type} [MetricSpace X] {Y : TopCat.{0}}
    (f : TopCat.of X ⟶ Y) (hX : ContractibleOpenBasis (TopCat.of X))
    (hf : HasContractiblePreimages f) (V : Coeff.{0}) :
    (derivedDirectImage f).obj (sheafInDegreeZero (constant (TopCat.of X) V)) ≅
      sheafInDegreeZero (constant Y V) := by
  have hconst : IsIso (constantDirectImageMap f V) := by
    apply isIso_constantDirectImageMap
    intro y U hy
    obtain ⟨W, hWU, hyW, hW⟩ := hf y U hy
    letI := hW
    exact ⟨W, hyW, hWU, isConnected_iff_connectedSpace.mpr inferInstance⟩
  let F := sheafInDegreeZero (constant (TopCat.of X) V)
  have hv (n : ℕ) : IsZero ((cohomology Y (n + 1 : ℕ)).obj ((derivedDirectImage f).obj F).obj) := by
    apply directImageCohomology_isZero_of_cofinal
    intro y U hy
    obtain ⟨W, hWU, hyW, hW⟩ := hf y U hy
    let O := (Opens.map f).obj W
    letI : ContractibleSpace (TopCat.of O) := hW
    exact ⟨W, hWU, hyW, (derivedSectionsConstant_isZero_pos X V hX O n).of_iso
      (derivedOpenSectionsCohomologyIso O (n + 1 : ℕ) F)⟩
  exact (derivedDirectImage_singleIso_of_positiveVanishing f _ hv).symm ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso (asIso (constantDirectImageMap f V)).symm

/-- Pullback of a closed extension is the closed extension on the inverse image. -/
private def pullbackClosedExtension {X Y : TopCat.{0}} (p : X ⟶ Y) {Z : Set Y}
    (hZ : IsClosed Z) (F : BoundedBelow (TopCat.of Z)) :
    (boundedBelowInverseImage p).obj ((closedExtensionPlus hZ).obj F) ≅
      (closedExtensionPlus (hZ.preimage p.hom.continuous)).obj
        ((boundedBelowInverseImage (TopCat.ofHom (p.hom.restrictPreimage Z))).obj F) := by
  let Z' : Set X := p ⁻¹' Z
  let hZ' : IsClosed Z' := hZ.preimage p.hom.continuous
  let i := closedInclusion Z
  let i' := closedInclusion Z'
  let v : TopCat.of Z' ⟶ TopCat.of Z := TopCat.ofHom (p.hom.restrictPreimage Z)
  let G := (closedExtensionPlus hZ).obj F
  let E := (boundedBelowInverseImage p).obj G
  have hG : DerivedSupportedOn Z G :=
    (DerivedLocalSheaves.derivedSupportedEssentialImage hZ G).mp ⟨F, ⟨Iso.refl G⟩⟩
  have hE : DerivedSupportedOn Z' E := by
    intro q x hx
    exact (hG q (p x) hx).of_iso (pullbackStalkIso p G q x)
  have hImage := (DerivedLocalSheaves.derivedSupportedEssentialImage hZ' E).mpr hE
  let D := Classical.choose hImage
  let a := Classical.choice (Classical.choose_spec hImage)
  let b := closedInverseAdjunction hZ
  let b' := closedInverseAdjunction hZ'
  haveI : (closedExtensionPlus hZ).Full :=
    (Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ)).full
  haveI : (closedExtensionPlus hZ).Faithful :=
    (Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ)).faithful
  haveI : (closedExtensionPlus hZ').Full :=
    (Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ')).full
  haveI : (closedExtensionPlus hZ').Faithful :=
    (Classical.choice (DerivedLocalSheaves.derivedClosedExtensionFullyFaithful hZ')).faithful
  have hc : i' ≫ p = v ≫ i := TopCat.ext (fun _ => rfl)
  let d : D ≅ (boundedBelowInverseImage i').obj E :=
    (asIso (b'.counit.app D)).symm ≪≫ (boundedBelowInverseImage i').mapIso a
  let e : (boundedBelowInverseImage i').obj E ≅ (boundedBelowInverseImage v).obj F :=
    (pullbackSquare hc).app G ≪≫
      (boundedBelowInverseImage v).mapIso (asIso (b.counit.app F))
  exact a.symm ≪≫ (closedExtensionPlus hZ').mapIso (d ≪≫ e)

private def pullbackSingle {X Y : TopCat.{0}} (p : X ⟶ Y) (M : Sheaves Y) :
    (boundedBelowInverseImage p).obj (sheafInDegreeZero M) ≅
      sheafInDegreeZero ((inverseImage p).obj M) := by
  let Xι := DerivedCategory.Plus.ι (C := Sheaves X)
  let L := derivedInverseImage p
  let eY := (DerivedCategory.Plus.singleFunctorιIso (C := Sheaves Y) 0).app M
  let eX := (DerivedCategory.Plus.singleFunctorιIso (C := Sheaves X) 0).app ((inverseImage p).obj M)
  exact Xι.preimageIso (L.mapIso eY ≪≫ ((inverseImage p).mapDerivedCategorySingleFunctor 0).app M ≪≫ eX.symm)

private def productClosedHomeomorph (T X : TopCat.{0}) (Z : Set X) :
    (T × TopCat.of Z) ≃ₜ (projection T X ⁻¹' Z) where
  toFun x := ⟨(x.1, x.2.val), x.2.property⟩
  invFun x := (x.val.1, ⟨x.val.2, x.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

private theorem hasContractiblePreimages_comp_homeomorph {X Y Z : TopCat.{0}} (f : X ⟶ Y)
    (e : Y ≃ₜ Z) (hf : HasContractiblePreimages f) :
    HasContractiblePreimages (f ≫ TopCat.ofHom ⟨e, e.continuous⟩) := by
  intro z U hz
  let A : Opens Y := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  obtain ⟨B, hBA, hzB, hB⟩ := hf (e.symm z) A (by simpa [A] using hz)
  let W : Opens Z := ⟨e '' B, e.isOpenMap _ B.isOpen⟩
  refine ⟨W, ?_, ⟨e.symm z, hzB, e.apply_symm_apply z⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hBA hy
  · have h : (Opens.map (f ≫ TopCat.ofHom ⟨e, e.continuous⟩)).obj W =
      (Opens.map f).obj B := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        change f x ∈ B
        change e y = e (f x) at he
        rw [← e.injective he]
        exact hy
      · intro hx
        exact ⟨f x, hx, rfl⟩
    rwa [h]

open private StageFace stageFaceInclusion faceInClosedPiece
  exists_contractible_open_preimage_face convex_contractibleBasis stageFaceDirectImageIso
  rightDerivedSingleIsoOfExact from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

private def derivedProductFaceImage {A : Type} [MetricSpace A]
    (hT : ContractibleOpenBasis (TopCat.of A))
    {σ : Type} [Fintype σ] {K : SimplicialComplex ℝ (σ → ℝ)}
    (Y : Opens (TopCat.of K.space)) (s : StageFace Y) (V : Coeff.{0}) :
    (derivedDirectImage (withParameter (TopCat.of A) (stageFaceInclusion Y s))).obj
        (sheafInDegreeZero (constant (TopCat.of (A × TopCat.of (faceInterior s.val.val))) V)) ≅
      (closedExtensionPlus ((isClosed_closedFacePiece K Y s.val).preimage
        (projection (TopCat.of A) (TopCat.of Y)).hom.continuous)).obj
          (sheafInDegreeZero (constant
            (TopCat.of (projection (TopCat.of A) (TopCat.of Y) ⁻¹' closedFacePiece K Y s.val)) V)) := by
  let T := TopCat.of A
  let X := TopCat.of Y
  let Z := closedFacePiece K Y s.val
  let Z' := projection T X ⁻¹' Z
  let hZ' : IsClosed Z' :=
    (isClosed_closedFacePiece K Y s.val).preimage (projection T X).hom.continuous
  let S := TopCat.of (faceInterior s.val.val)
  let f := faceInClosedPiece s.val Y s.property
  let e := productClosedHomeomorph T X Z
  let u : TopCat.of (T × TopCat.of Z) ⟶ TopCat.of Z' :=
    TopCat.ofHom ⟨e, e.continuous⟩
  let g := withParameter T f ≫ u
  let i := closedInclusion Z'
  have hg : withParameter T (stageFaceInclusion Y s) = g ≫ i := TopCat.ext (fun _ => rfl)
  let ambient : Z → (σ → ℝ) := fun z => z.val.val.val
  have hf : HasContractiblePreimages f :=
    exists_contractible_open_preimage_face (K.nonempty_of_mem_faces s.val.property)
      ambient (Isometry.of_dist_eq (fun _ _ => rfl))
      (by rintro _ ⟨x, rfl⟩; exact x.property) f (fun _ => rfl)
  have hS : ContractibleOpenBasis S := convex_contractibleBasis (convex_faceInterior _)
  have hgc : HasContractiblePreimages g :=
    @hasContractiblePreimages_comp_homeomorph _ (TopCat.of (T × TopCat.of Z))
      (TopCat.of Z') (withParameter T f) e (hasContractiblePreimages_product f hT hf)
  have hc : (derivedDirectImage g).obj (sheafInDegreeZero (constant (TopCat.of (T × S)) V)) ≅
      sheafInDegreeZero (constant (TopCat.of Z') V) := by
    exact derivedConstantImage g (contractibleOpenBasis_product _ _ hT hS) hgc V
  rw [hg]
  letI := (extraordinaryAdjunction hZ').isLeftAdjoint
  exact (derivedDirectImageComposition g i).symm.app _ ≪≫ (derivedDirectImage i).mapIso hc ≪≫
    (rightDerivedExactIso (directImage i)).app _

private theorem productFace_directImage_essImage {A : Type} [MetricSpace A]
    (hA : ContractibleOpenBasis (TopCat.of A))
    {σ : Type} [Fintype σ] {K : Geometry.SimplicialComplex ℝ (σ → ℝ)}
    {U Y : Opens (TopCat.of K.space)} (h : U ≤ Y) (s : StageFace U) (V : Coeff.{0}) :
    (derivedDirectImage (withParameter (TopCat.of A) (stageInclusion h))).essImage
      ((boundedBelowInverseImage (projection (TopCat.of A) (TopCat.of Y))).obj
        ((derivedDirectImage (stageInclusion h)).obj (sheafInDegreeZero
          ((directImage (stageFaceInclusion U s)).obj
            (constant (TopCat.of (faceInterior s.val.val)) V))))) := by
  let T := TopCat.of A
  let j := stageInclusion h
  let jT := withParameter T j
  let r : StageFace Y := ⟨s.val, s.property.trans h⟩
  let Z := closedFacePiece K Y s.val
  let hZ := isClosed_closedFacePiece K Y s.val
  let i := closedInclusion (X := TopCat.of Y) Z
  let p := projection T (TopCat.of Y)
  let v := TopCat.ofHom (p.hom.restrictPreimage Z)
  let S := TopCat.of (faceInterior s.val.val)
  let E := sheafInDegreeZero (constant (TopCat.of (T × S)) V)
  let F := sheafInDegreeZero ((directImage (stageFaceInclusion U s)).obj (constant S V))
  let C := constant (TopCat.of Z) V
  letI := (extraordinaryAdjunction (X := TopCat.of Y) (Z := Z) hZ).isLeftAdjoint
  let e₀ : (derivedDirectImage j).obj F ≅ (closedExtensionPlus (X := TopCat.of Y) (Z := Z) hZ).obj (sheafInDegreeZero C) :=
    stageFaceDirectImageIso h s V ≪≫ (rightDerivedSingleIsoOfExact (directImage i) C).symm ≪≫
      (rightDerivedExactIso (directImage i)).app _
  let e₁ := pullbackClosedExtension p hZ (sheafInDegreeZero C)
  let e₂ := (closedExtensionPlus (hZ.preimage p.hom.continuous)).mapIso
    (pullbackSingle v C ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso (constantPullbackIso v V))
  let e₃ := derivedProductFaceImage hA Y r V
  have hcomp : withParameter T (stageFaceInclusion U s) ≫ jT =
      withParameter T (stageFaceInclusion Y r) := TopCat.ext (fun _ => rfl)
  refine ⟨(derivedDirectImage (withParameter T (stageFaceInclusion U s))).obj E, ⟨?_⟩⟩
  exact (derivedDirectImageComposition _ _).app E ≪≫
    eqToIso (congrArg (fun f => (derivedDirectImage f).obj E) hcomp) ≪≫
    e₃ ≪≫ e₂.symm ≪≫ e₁.symm ≪≫ (boundedBelowInverseImage p).mapIso e₀.symm

open private stageFace_connected stageFaces_cover stageFace_elementary_restrictions
  stageFace_restriction_constant stagePieceInclusion faceInStage_isInducing
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SimplicialConstructibleDirectImage

/-- On a simplicial attachment, the projected direct image lies in the image of
the product open direct image. This property is stable under triangles. -/
private theorem simplicial_projection_essImage {A : Type} [MetricSpace A]
    (hA : ContractibleOpenBasis (TopCat.of A))
    {σ : Type} [Fintype σ] {K : Geometry.SimplicialComplex ℝ (σ → ℝ)} (hK : K.faces.Finite)
    {U Y : Opens (TopCat.of K.space)} (h : U ≤ Y)
    (hU : IsUnionOfFaceInteriors K (U : Set K.space))
    (F : BoundedBelow (TopCat.of U))
    (hF : IsConstructibleOnFaceInteriors K (openInclusion U ≫ complexInclusion K) F) :
    (derivedDirectImage (withParameter (TopCat.of A) (stageInclusion h))).essImage
      ((boundedBelowInverseImage (projection (TopCat.of A) (TopCat.of Y))).obj
        ((derivedDirectImage (stageInclusion h)).obj F)) := by
  let T := TopCat.of A
  let j := stageInclusion h
  let jT := withParameter T j
  let H := (directImage j).rightDerivedFunctorPlus ⋙
    boundedBelowInverseImage (projection T (TopCat.of Y))
  let R := (directImage jT).rightDerivedFunctorPlus
  let P (G : BoundedBelow (TopCat.of U)) := R.essImage (H.obj G)
  letI : H.CommShift ℤ := by dsimp only [H]; infer_instance
  letI : H.IsTriangulated := by dsimp only [H]; infer_instance
  letI : R.CommShift ℤ := by dsimp only [R]; infer_instance
  letI : R.IsTriangulated := by dsimp only [R]; infer_instance
  let a := DerivedLocalSheaves.derivedInverseDirectAdjunctionData jT
  haveI (G : BoundedBelow (TopCat.of (T × TopCat.of U))) : IsIso (a.counit.app G) :=
    openCounitIsIso (withParameter_open T (stageInclusion_isOpenEmbedding h)) a G
  haveI : IsIso a.counit := NatIso.isIso_of_isIso_app _
  letI : R.Full := a.fullyFaithfulROfIsIsoCounit.full
  have hZero : P 0 := ⟨0, ⟨R.mapZeroObject ≪≫ H.mapZeroObject.symm⟩⟩
  have hIso {G G' : BoundedBelow (TopCat.of U)} (e : G ≅ G') (hG : P G) : P G' :=
    R.essImage.prop_of_iso (H.mapIso e) hG
  have hShift (G : BoundedBelow (TopCat.of U)) (n : ℤ) (hG : P G) : P (G⟦n⟧) := by
    obtain ⟨E, ⟨e⟩⟩ := hG
    exact ⟨E⟦n⟧, ⟨(R.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso e ≪≫
      ((H.commShiftIso n).app G).symm⟩⟩
  have hTriangle (D : Triangle (BoundedBelow (TopCat.of U))) (hD : D ∈ distTriang _) :
      (P D.obj₁ → P D.obj₃ → P D.obj₂) ∧
      (P D.obj₁ → P D.obj₂ → P D.obj₃) ∧
      (P D.obj₂ → P D.obj₃ → P D.obj₁) :=
    ⟨R.essImage.ext_of_isTriangulatedClosed₂ _ (H.map_distinguished D hD),
     R.essImage.ext_of_isTriangulatedClosed₃ _ (H.map_distinguished D hD),
     R.essImage.ext_of_isTriangulatedClosed₁ _ (H.map_distinguished D hD)⟩
  let J := DerivedCategory.Plus.singleFunctor (Sheaves (TopCat.of U)) 0
  let Q (M : Sheaves (TopCat.of U)) := P (J.obj M)
  have hQZero : Q 0 := hIso J.mapZeroObject.symm hZero
  have hQIso ⦃M N : Sheaves (TopCat.of U)⦄ (e : M ≅ N) (hM : Q M) : Q N :=
    hIso (J.mapIso e) hM
  have hQShort (S : ShortComplex (Sheaves (TopCat.of U))) (hs : S.ShortExact) :
      (Q S.X₁ → Q S.X₂ → Q S.X₃) ∧ (Q S.X₁ → Q S.X₃ → Q S.X₂) ∧
        (Q S.X₂ → Q S.X₃ → Q S.X₁) := by
    let D := Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.plusTriangle
      (Sheaves (TopCat.of U)) hs
    have hP := hTriangle D (AdvancedHomologicalAlgebra.ClassicalDerivedValues.plusTriangle_distinguished hs)
    exact ⟨hP.2.1, hP.1, hP.2.2⟩
  have hQElementary (s : StageFace U) (V : Coeff.{0}) (_ : Module.Finite ℚ V) :
      Q ((directImage (stageFaceInclusion U s)).obj (constant (TopCat.of (faceInterior s.val.val)) V)) :=
    productFace_directImage_essImage hA h s V
  haveI : Finite K.faces := hK.to_subtype
  haveI (s : StageFace U) : ConnectedSpace (TopCat.of (faceInterior s.val.val)) :=
    stageFace_connected U s
  have hSingle (M : Sheaves (TopCat.of U))
      (hM : ∀ s : K.faces, LocallyConstantFiniteRank ((inverseImage (stagePieceInclusion U s)).obj M)) :
      P (sheafInDegreeZero M) :=
    FiniteFaceDevissage.finiteFaceGeneration (StageFace U) (TopCat.of U)
      (fun s => TopCat.of (faceInterior s.val.val)) (stageFaceInclusion U)
      (fun s => faceInStage_isInducing s.val U s.property) (stageFaces_cover hK U hU)
      (stageFace_elementary_restrictions U) Q hQZero hQIso hQShort hQElementary M
      (fun s => stageFace_restriction_constant U s M hM)
  exact ConstructibleTriangles.constructible_truncation_induction (stagePieceInclusion U)
    P hZero hIso hShift (fun D hD => (hTriangle D hD).1) hSingle F hF

private theorem withParameter_range {X Y : TopCat.{0}} (T : TopCat.{0}) (j : X ⟶ Y) :
    Set.range (withParameter T j) = projection T Y ⁻¹' Set.range j := by
  ext p
  rcases p with ⟨t, y⟩
  constructor
  · rintro ⟨⟨u, x⟩, h⟩
    exact ⟨x, congrArg Prod.snd h⟩
  · rintro ⟨x, hx⟩
    exact ⟨(t, x), Prod.ext rfl hx⟩

private theorem local_comparison_isIso
    {T U Y U' Y' : TopCat.{0}} {j : U ⟶ Y} {j' : U' ⟶ Y'}
    (hj' : IsOpenEmbedding j') (s : U' ⟶ U) (t : Y' ⟶ Y)
    (hs : IsOpenEmbedding s) (ht : IsOpenEmbedding t)
    (hc : j' ≫ t = s ≫ j) (hrange : Set.range s = j ⁻¹' Set.range t)
    (F : BoundedBelow U)
    (hF : (derivedDirectImage (withParameter T j')).essImage
      ((boundedBelowInverseImage (projection T Y')).obj
        ((derivedDirectImage j').obj ((boundedBelowInverseImage s).obj F))))
    (a : boundedBelowInverseImage (withParameter T j) ⊣ derivedDirectImage (withParameter T j))
    (b : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (hm : IsIso ((boundedBelowInverseImage (withParameter T j)).map
      (directImageComparison (projectionSquare T j) a b F))) :
    IsIso ((boundedBelowInverseImage (withParameter T t)).map
      (directImageComparison (projectionSquare T j) a b F)) := by
  let jT := withParameter T j
  let j'T := withParameter T j'
  let sT := withParameter T s
  let tT := withParameter T t
  let m := directImageComparison (projectionSquare T j) a b F
  have hcT : j'T ≫ tT = sT ≫ jT :=
    TopCat.ext (fun z => Prod.ext rfl (congrArg (fun l : U' ⟶ Y => l z.2) hc))
  have hrangeT : Set.range sT = jT ⁻¹' Set.range tT := by
    rw [withParameter_range T s, withParameter_range T t, hrange]
    rfl
  obtain ⟨e⟩ := derivedDirectImageOpenRestrictionIso j j' s t hs ht hc hrange F
  obtain ⟨e'⟩ := derivedDirectImageOpenRestrictionIso jT j'T sT tT
    (withParameter_open T hs) (withParameter_open T ht) hcT hrangeT
    ((boundedBelowInverseImage (projection T U)).obj F)
  let eL := (pullbackSquare (projectionSquare T t)).app ((derivedDirectImage j).obj F) ≪≫
    (boundedBelowInverseImage (projection T Y')).mapIso e
  have hL : (derivedDirectImage j'T).essImage
      ((boundedBelowInverseImage tT).obj
        ((boundedBelowInverseImage (projection T Y)).obj ((derivedDirectImage j).obj F))) :=
    (derivedDirectImage j'T).essImage.prop_of_iso eL.symm hF
  have hR : (derivedDirectImage j'T).essImage
      ((boundedBelowInverseImage tT).obj
        ((derivedDirectImage jT).obj ((boundedBelowInverseImage (projection T U)).obj F))) :=
    ⟨_, ⟨e'.symm⟩⟩
  apply isIso_of_openRestriction (withParameter_open T hj') _ hL hR
  haveI : IsIso ((boundedBelowInverseImage jT).map m) := hm
  have hright : IsIso ((boundedBelowInverseImage (sT ≫ jT)).map m) :=
    (NatIso.isIso_map_iff (boundedBelowPullbackComposition sT jT) m).mpr
      (Functor.map_isIso (boundedBelowInverseImage sT) _)
  rw [← hcT] at hright
  exact (NatIso.isIso_map_iff (boundedBelowPullbackComposition j'T tT) m).mp hright

open LatticeModelSpecs RankTwoSchubertStrataSpecs SchubertIntersectionConstructibilitySpecs
open private exists_triangulatedAttachment constructible_on_smaller_faces
  normalizedOrbitIC_realizes normalizedOrbitIC_perverse
  TriangulatedAttachment.coordinates TriangulatedAttachment.finiteCoordinates
  TriangulatedAttachment.finiteFaces TriangulatedAttachment.nested TriangulatedAttachment.smallerUnion
  TriangulatedAttachment.source TriangulatedAttachment.target
  TriangulatedAttachment.sourceOpen TriangulatedAttachment.targetOpen
  TriangulatedAttachment.commutes TriangulatedAttachment.preimageRange TriangulatedAttachment.contains
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

theorem smoothProjectionBaseChange : Expected.SmoothProjectionBaseChange := by
  intro T e hT ab N hN k U Y j f P Q s D stage prev
  change ∀ a b, IsIso (directImageComparison (projectionSquare T j) a b (complex D))
  intro a b
  obtain ⟨V, ⟨chart⟩⟩ := hT
  letI : MetricSpace T := chart.isEmbedding.comapMetricSpace chart
  have hBasis : ContractibleOpenBasis T := contractibleOpenBasis_of_coordinates chart
  have hprev := normalizedOrbitIC_realizes prev
  have hj : IsOpenEmbedding j := IsOpenEmbedding.of_comp _ stage.1 hprev.1
  let F := complex D
  let m := directImageComparison (projectionSquare T j) a b F
  have hm : IsIso ((boundedBelowInverseImage (withParameter T j)).map m) :=
    comparison_isIso_on_open (projectionSquare T j) (withParameter_open T hj) hj a b F
  let patch (y : Y) := Classical.choice (exists_triangulatedAttachment
    RankTwoSchubertStrata.boundedSchubertComparison RankTwoSchubertStrata.schubertStratification
    RankTwoSchubertStrata.smithClassification hj stage hprev y)
  let target (y : Y) := withParameter T (TriangulatedAttachment.target (patch y))
  have cover : ∀ x : TopCat.of (T × Y), ∃ y v, target y v = x := by
    rintro ⟨t, y⟩
    obtain ⟨v, hv⟩ := TriangulatedAttachment.contains (patch y)
    exact ⟨y, (t, v), Prod.ext rfl hv⟩
  refine isIso_of_pullback_cover target cover m ?_
  intro y
  let A := patch y
  letI : Finite (TriangulatedAttachment.coordinates A) :=
    TriangulatedAttachment.finiteCoordinates A
  letI : Fintype (TriangulatedAttachment.coordinates A) :=
    Fintype.ofFinite (TriangulatedAttachment.coordinates A)
  let F' := (boundedBelowInverseImage (TriangulatedAttachment.source A)).obj F
  have hF' := constructible_on_smaller_faces A hprev F (normalizedOrbitIC_perverse prev).1
  have h := simplicial_projection_essImage (A := T) hBasis (TriangulatedAttachment.finiteFaces A)
    (TriangulatedAttachment.nested A) (TriangulatedAttachment.smallerUnion A) F' hF'
  exact local_comparison_isIso (stageInclusion_isOpenEmbedding (TriangulatedAttachment.nested A))
    (TriangulatedAttachment.source A) (TriangulatedAttachment.target A)
    (TriangulatedAttachment.sourceOpen A) (TriangulatedAttachment.targetOpen A)
    (TriangulatedAttachment.commutes A) (TriangulatedAttachment.preimageRange A) F h a b hm

end RepTheorySurvey.Geometric.SchubertProjectionBaseChange
