import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertProductAttachments
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertProjectionBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace Topology

namespace RepTheorySurvey.Geometric.SchubertProductAttachments

open Analytic Analytic.IntersectionComplex
open SchubertProductAttachmentsSpecs SchubertIntersectionConstructibilitySpecs

open private pullbackCommShift pullbackTriangulated pullbackCohomologyIso
  pullbackIsLE pullbackIsGE truncationTriangle truncationTriangle_distinguished
  truncationTriangle_isLE truncationTriangle_isGE truncationTriangleIso₁
  locallyConstantFiniteRank_of_iso pullback_locallyConstantFiniteRank
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

open private normalizedOrbitIC_perverse
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

attribute [local instance] pullbackCommShift pullbackTriangulated

universe u

private def productBoundaryProjection (T : TopCat.{0}) {U X : TopCat.{0}}
    (j : U ⟶ X) : TopCat.of (boundary (productMap T j)) ⟶ TopCat.of (boundary j) :=
  TopCat.ofHom ⟨fun z => ⟨z.val.2, by
    rintro ⟨x, hx⟩
    exact z.property ⟨(z.val.1, x), Prod.ext rfl hx⟩⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

private theorem productBoundarySquare (T : TopCat.{0}) {U X : TopCat.{0}} (j : U ⟶ X) :
    closedInclusion (boundary (productMap T j)) ≫ productProjection T X =
      productBoundaryProjection T j ≫ closedInclusion (boundary j) :=
  TopCat.ext (fun _ => rfl)

private def shiftCohomologyIso {X : TopCat.{u}} (F : BoundedBelow X) (n q : ℤ) :
    (cohomology X q).obj (F⟦n⟧).obj ≅ (cohomology X (q + n)).obj F.obj :=
  (cohomology X q).mapIso (((DerivedCategory.Plus.ι (C := Sheaves X)).commShiftIso n).app F) ≪≫
    (shiftCohomology X q n).app F.obj

private theorem productBoundaryConstructible (T : TopCat.{0}) {U X : TopCat.{0}}
    (j : U ⟶ X) (n : ℤ) (F : BoundedBelow X)
    (G : BoundedBelow (TopCat.of (T × X)))
    (c : ((boundedBelowInverseImage (productProjection T X)).obj F)⟦n⟧ ≅ G)
    (h : IsConstructibleOnBoundary j F) :
    IsConstructibleOnBoundary (productMap T j) G := by
  let i := closedInclusion (boundary j)
  let iT := closedInclusion (boundary (productMap T j))
  let p := productBoundaryProjection T j
  let L := boundedBelowInverseImage iT
  let A := (boundedBelowInverseImage i).obj F
  let B := (boundedBelowInverseImage p).obj A
  let d : L.obj G ≅ B⟦n⟧ :=
    L.mapIso c.symm ≪≫ (L.commShiftIso n).app _ ≪≫
      (shiftFunctor _ n).mapIso ((pullbackSquare (productBoundarySquare T j)).app F)
  have isoAt (q : ℤ) : (cohomology _ q).obj (L.obj G).obj ≅
      (inverseImage p).obj ((cohomology _ (q + n)).obj A.obj) :=
    (cohomology _ q).mapIso ((DerivedCategory.Plus.ι (C := Sheaves _)).mapIso d) ≪≫
      shiftCohomologyIso B n q ≪≫ pullbackCohomologyIso p A (q + n)
  obtain ⟨hfin, hloc⟩ := h
  change Set.Finite {q : ℤ | ¬ IsZero ((cohomology _ q).obj (L.obj G).obj)} ∧
    ∀ q : ℤ, LocallyConstantFiniteRank ((cohomology _ q).obj (L.obj G).obj)
  constructor
  · have hinj : Function.Injective (fun q : ℤ => q + n) := fun _ _ eq => add_right_cancel eq
    apply (hfin.preimage hinj.injOn).subset
    intro q hq hz
    exact hq (((inverseImage p).map_isZero hz).of_iso (isoAt q))
  · intro q
    exact locallyConstantFiniteRank_of_iso (isoAt q).symm
      (pullback_locallyConstantFiniteRank p (hloc (q + n)))

/-- Exact inverse image followed by a shift carries the ordinary truncation triangle
to one with cutoff decreased by the shift. -/
private def shiftedPullbackTruncation {Y X : TopCat.{u}} (p : Y ⟶ X) (m n : ℤ)
    (F : BoundedBelow X) (H : BoundedBelow Y)
    (c : ((boundedBelowInverseImage p).obj F)⟦n⟧ ≅ H) :
    ((boundedBelowInverseImage p).obj ((truncLE X m).obj F))⟦n⟧ ≅
      (truncLE Y (m - n)).obj H := by
  let L := boundedBelowInverseImage p
  let A := L.mapTriangle.obj (truncationTriangle m F)
  let t := DerivedCategory.Plus.TStructure.t (C := Sheaves Y)
  have hA : A ∈ distTriang (BoundedBelow Y) :=
    L.map_distinguished _ (truncationTriangle_distinguished m F)
  haveI : t.IsLE A.obj₁ m := pullbackIsLE p _ m (truncationTriangle_isLE m F)
  haveI : t.IsGE A.obj₃ (m + 1) := pullbackIsGE p _ (m + 1) (truncationTriangle_isGE m F)
  exact truncationTriangleIso₁ (A.shift_distinguished hA n)
    (truncationTriangle_distinguished _ _)
    (t.isLE_shift A.obj₁ m n (m - n)) (truncationTriangle_isLE _ _)
    (t.isGE_shift A.obj₃ (m + 1) n (m - n + 1)) (truncationTriangle_isGE _ _) c

private def shiftedDirectImage {U X : TopCat.{u}} (j : U ⟶ X)
    (F : BoundedBelow U) (n : ℤ) :
    ((derivedDirectImage j).obj F)⟦n⟧ ≅ (derivedDirectImage j).obj (F⟦n⟧) :=
  (((directImage j).rightDerivedFunctorPlus.commShiftIso n).app F).symm

/-- Lift the correction on the open part through the strict restriction functor. -/
private theorem normalizeRestriction {U X : TopCat.{u}} {j : U ⟶ X}
    (hj : IsOpenEmbedding j) (s : ℕ) {E : BoundedBelow X} {G : BoundedBelow U}
    (hE : IsStrictExtension hj s E)
    (r : (boundedBelowInverseImage j).obj E ≅ G)
    {C : Derived X} (c₀ : C ≅ E.obj)
    (v : (derivedInverseImage j).obj C ≅ G.obj) :
    ∃ c : C ≅ E.obj, (derivedInverseImage j).map c.hom ≫ r.hom.hom = v.hom := by
  let L := derivedInverseImage j
  let i := DerivedCategory.Plus.ι (C := Sheaves U)
  let d : L.obj E.obj ≅ L.obj E.obj := L.mapIso c₀.symm ≪≫ v ≪≫ (i.mapIso r).symm
  let d' : (boundedBelowInverseImage j).obj E ≅ (boundedBelowInverseImage j).obj E :=
    ObjectProperty.isoMk _ d
  obtain ⟨ff⟩ := MiddleExtension.strictRestrictionFullyFaithful j hj s
  let E' : (show ObjectProperty (BoundedBelow X) from IsStrictExtension hj s).FullSubcategory :=
    ⟨E, hE⟩
  let w : E' ≅ E' := ff.preimageIso d'
  let a : E.obj ≅ E.obj :=
    DerivedCategory.Plus.ι.mapIso ((ObjectProperty.ι _).mapIso w)
  have ha : L.map a.hom = d.hom := by
    have hw : (strictRestriction hj s).map w.hom = d'.hom :=
      ff.map_preimage (X := E') (Y := E') d'.hom
    have hd : i.map d'.hom = d.hom := rfl
    exact (congrArg i.map hw).trans hd
  refine ⟨c₀ ≪≫ a, ?_⟩
  change L.map (c₀.hom ≫ a.hom) ≫ (i.mapIso r).hom = v.hom
  rw [L.map_comp, ha]
  simp only [d, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ← L.map_comp, Iso.hom_inv_id, L.map_id, Category.id_comp]
  change v.hom ≫ (i.mapIso r).inv ≫ (i.mapIso r).hom = v.hom
  rw [Iso.inv_hom_id, Category.comp_id]

/-- At a Schubert attachment, smooth shifted pullback respects the middle extension
and its specified identification over the preceding open stage. -/
theorem shiftedProductAttachment : Expected.ShiftedProductAttachment := by
  intro T e hT ab N hN k U X j hj f Q P d D hD hStage s F hAttach hBoundary
    jT pX pU n QT PT hAttachT G hG g a b E ET r rT
  have hF : IsMiddlePerverse Q F.obj := normalizedOrbitIC_perverse hD
  have hr : IsIso r :=
    (MiddleExtension.attachmentIsMiddleExtension j hj s Q P hAttach F hF hBoundary).2.2 b
  have hBC : IsIso (directImageComparison (projectionSquare T j) a b F) :=
    SchubertProjectionBaseChange.smoothProjectionBaseChange T e hT ab N hN k j f P Q D
      hStage hD a b
  let FU := (boundedBelowInverseImage pU).obj F
  let gPlus : FU⟦n⟧ ≅ G :=
    ObjectProperty.isoMk _
      (((DerivedCategory.Plus.ι (C := Sheaves _)).commShiftIso n).app FU ≪≫ g)
  let cDirect : ((boundedBelowInverseImage pX).obj ((derivedDirectImage j).obj F))⟦n⟧ ≅
      (derivedDirectImage jT).obj G :=
    (shiftFunctor _ n).mapIso (asIso (directImageComparison (projectionSquare T j) a b F)) ≪≫
      shiftedDirectImage jT FU n ≪≫ (derivedDirectImage jT).mapIso gPlus
  have hBoundaryT : IsConstructibleOnBoundary jT ((derivedDirectImage jT).obj G) :=
    productBoundaryConstructible T j n _ _ cDirect hBoundary
  obtain ⟨hET, hStrict, hRest⟩ :=
    MiddleExtension.attachmentIsMiddleExtension jT (productMap_open T hj) (s + e)
      QT PT hAttachT G hG hBoundaryT
  have hrT : IsIso rT := hRest a
  let m : ℤ := -(s : ℤ) - 1
  have hm : m - n = -((s + e : ℕ) : ℤ) - 1 := by
    simp only [m, n, Nat.cast_add]
    omega
  let cPlus : ((boundedBelowInverseImage pX).obj E)⟦n⟧ ≅ ET :=
    shiftedPullbackTruncation pX m n _ _ cDirect ≪≫
      eqToIso (congrArg (fun q => (truncLE (TopCat.of (T × X)) q).obj
        ((derivedDirectImage jT).obj G)) hm)
  let c₀ : ((derivedInverseImage pX).obj E.obj)⟦n⟧ ≅ ET.obj :=
    (((DerivedCategory.Plus.ι (C := Sheaves _)).commShiftIso n).app
      ((boundedBelowInverseImage pX).obj E)).symm ≪≫ DerivedCategory.Plus.ι.mapIso cPlus
  let v : (derivedInverseImage jT).obj (((derivedInverseImage pX).obj E.obj)⟦n⟧) ≅ G.obj :=
    ((inverseImage jT).mapDerivedCategory.commShiftIso n).app ((derivedInverseImage pX).obj E.obj) ≪≫
      (shiftFunctor (Derived (TopCat.of (T × U))) n).mapIso
        ((DerivedPullbackPasting.derivedPullbackSquare (projectionSquare T j)).app E.obj ≪≫
          (derivedInverseImage pU).mapIso (DerivedCategory.Plus.ι.mapIso (asIso r))) ≪≫ g
  refine ⟨hET, hStrict, hrT, ?_⟩
  exact normalizeRestriction (productMap_open T hj) (s + e) hStrict (asIso rT) c₀ v

end RepTheorySurvey.Geometric.SchubertProductAttachments
