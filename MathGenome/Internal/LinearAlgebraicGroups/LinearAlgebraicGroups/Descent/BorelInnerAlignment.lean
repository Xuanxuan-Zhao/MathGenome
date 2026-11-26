import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.BorelInnerAlignment
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SmoothPoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.Parabolics
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.BorelInnerAlignment

open LinearAlgebraicGroups.Specs
open Specs.AutomorphismSequence
open Specs.BorelInnerAlignment
open Specs.AdjointBorelCohomology (ImageBorel)
open Specs.AdjointCocharacters (IsAdjointQuotient)
open Specs.Fppf (schemeTopology IsFppf)
open Specs.GeometricBorelConjugacy (IsBorel IsKBorel)
open Specs.GeometricRadicals (IsReductive)
open Specs.BorelProper (IsParabolic)
open NonabelianCohomology

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G H L : GroupScheme k} {T U : SchemeOver k}

private abbrev evaluate (i : relativePoints G T ≅ relativePoints H T)
    {V : SchemeOver k} (v : V ⟶ T) (x : V ⟶ G.X) : V ⟶ H.X :=
  (i.hom.app (op (Over.mk v))).hom x

/-- The comparison identifies the two closed subgroup functors on the whole slice. -/
private def Relates (B : ClosedSubgroup G) (C : ClosedSubgroup H)
    (i : relativePoints G T ≅ relativePoints H T) : Prop :=
  ∀ (V : SchemeOver k) (v : V ⟶ T) (x : V ⟶ G.X),
    (∃ y : V ⟶ C.group.X, y ≫ C.inclusion.hom.hom = evaluate i v x) ↔
    ∃ y : V ⟶ B.group.X, y ≫ B.inclusion.hom.hom = x

private theorem evaluate_symm (i : relativePoints G T ≅ relativePoints H T)
    {V : SchemeOver k} (v : V ⟶ T) (x : V ⟶ H.X) :
    evaluate i v (evaluate i.symm v x) = x :=
  (i.app (op (Over.mk v))).groupIsoToMulEquiv.apply_symm_apply x

private theorem Relates.symm {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    {i : relativePoints G T ≅ relativePoints H T} (h : Relates B C i) :
    Relates C B i.symm := by
  intro V v x
  simpa only [evaluate_symm] using (h V v (evaluate i.symm v x)).symm

private theorem Relates.trans {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    {D : ClosedSubgroup L} {i : relativePoints G T ≅ relativePoints H T}
    {j : relativePoints H T ≅ relativePoints L T} (hi : Relates B C i) (hj : Relates C D j) :
    Relates B D (i ≪≫ j) := fun V v x => (hj V v (evaluate i v x)).trans (hi V v x)

private theorem Relates.restrict {B : ClosedSubgroup G} {C : ClosedSubgroup H}
    {i : relativePoints G T ≅ relativePoints H T} (h : Relates B C i) (a : U ⟶ T) :
    Relates B C (restrictIso a i) := fun V v x => h V (v ≫ a) x

open private smooth_extend_iff normalizes_iff_sections extendSubgroup
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer

private theorem borelParabolic (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (B : ClosedSubgroup A.val) (hB : IsKBorel B) : IsParabolic A B := by
  obtain ⟨hc, hB⟩ := hB
  exact ⟨hA, (smooth_extend_iff (AlgebraicClosure k) B.group.X).mp hB.1.1,
    hc, _, hB, ⟨𝟙 _, Category.id_comp _⟩⟩

open private range_of_local_sections groupSectionsMap groupSectionsMap_locallySurjective
  groupSections_isSheaf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private theorem factors_adjoint_borel {A Q : AffineAlgebraicGroup k}
    {B : ClosedSubgroup A.val} (hB : IsParabolic A B) {Z : ClosedSubgroup A.val}
    {q : A.val ⟶ Q.val} (hq : IsAdjointQuotient Z q) (W : ImageBorel B q)
    (inn : groupSections Q.val ⟶ automorphisms A.val)
    (onLift : ∀ (V : SchemeOver k) (g : V ⟶ A.val.X),
      inn.app (op V) ⟨g ≫ q.hom.hom⟩ = innerAut g)
    (x : T ⟶ Q.val.X) (hx : Relates B B (inn.app (op T) ⟨x⟩).asIso) :
    ∃ y : T ⟶ W.subgroup.group.X, y ≫ W.subgroup.inclusion.hom.hom = x := by
  let J := schemeTopology k
  let p := groupSectionsMap q
  let m := groupSectionsMap W.subgroup.inclusion
  let : Presheaf.IsLocallySurjective J p :=
    groupSectionsMap_locallySurjective q ⟨hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2⟩
  have hm (V : (SchemeOver k)ᵒᵖ) : Function.Injective (m.app V) := by
    intro y z e
    let := W.subgroup.isClosedImmersion
    let : Mono W.subgroup.inclusion.hom.hom := Over.mono_of_mono_left _
    exact ULift.ext ((cancel_mono W.subgroup.inclusion.hom.hom).mp (congrArg ULift.down e))
  have h := range_of_local_sections m (groupSections_isSheaf W.subgroup.group) hm
    (ULift.up x) (groupSections_isSheaf Q.val) (Presheaf.imageSieve_mem J p (ULift.up x)) (by
      rintro V v ⟨⟨g⟩, hg⟩
      have he : restrictAut v (inn.app (op T) ⟨x⟩) = innerAut g := by
        change (automorphisms A.val).map v.op (inn.app (op T) ⟨x⟩) = _
        rw [← NatTrans.naturality_apply inn, ← hg]
        exact onLift V g
      have hr : Relates B B (innerAut g).asIso := by
        rw [← he]
        exact hx.restrict v
      have hn : Normalizes B.inclusion g := (normalizes_iff_sections B g).mpr (fun Y a b => by
        have h₁ := (hr Y a (b ≫ B.inclusion.hom.hom)).mpr ⟨b, rfl⟩
        have h₂ := (hr.symm Y a (b ≫ B.inclusion.hom.hom)).mpr ⟨b, rfl⟩
        change (∃ y : Y ⟶ B.group.X, y ≫ B.inclusion.hom.hom =
          (a ≫ g)⁻¹ * (b ≫ B.inclusion.hom.hom) * ((a ≫ g)⁻¹)⁻¹) at h₂
        exact ⟨h₁, by simpa only [inv_inv] using h₂⟩)
      obtain ⟨b, hb⟩ :=
        (Flag.StandardParabolics.groundFieldParabolicNormalizer A B hB V g).mp hn
      refine ⟨⟨b ≫ W.projection.hom.hom⟩, ?_⟩
      rw [← hg]
      apply ULift.ext
      have hf := congrArg (fun f => f.hom.hom) W.factor.1
      change W.projection.hom.hom ≫ W.subgroup.inclusion.hom.hom =
        B.inclusion.hom.hom ≫ q.hom.hom at hf
      change (b ≫ W.projection.hom.hom) ≫ W.subgroup.inclusion.hom.hom = g ≫ q.hom.hom
      rw [Category.assoc, hf, ← Category.assoc, hb])
  obtain ⟨⟨y⟩, hy⟩ := h
  exact ⟨y, congrArg ULift.down hy⟩

section Geometry

open Specs.ParabolicFamilyTransporter
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)

open private relativeSchemeIso relativeSchemeIso_natural relativeSectionEquiv
  relativeSection_natural relativeSectionGroupEquiv from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private pullback_map_square borel_extended_sections from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeBorelAlignment
open private familyAmbient_left factors_relative_iff relativePoint overBase from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicFamilyTransporter
open private borelUnderIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.ParabolicIntersection
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private isKBorel_iff_of_isAlgClosed smoothConnectedSolvable_extend_iff
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open private solvable_iff_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricRadicals
open private group_geometricallyIrreducible from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CocharacterOpenCell
open private compareRepresentatives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private borel_of_containing_borel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private def transportedFamily (C : ClosedSubgroup H) (hC : Smooth C.group.X.hom)
    (i : relativePoints H T ≅ relativePoints G T) : Family G T := by
  let m := (Over.pullback T.hom).mapGrp.map C.inclusion
  let j := (relativeSchemeIso i).hom
  haveI : IsClosedImmersion m.hom.hom.left :=
    MorphismProperty.of_isPullback
      (pullback_map_square (S := T) C.inclusion.hom.hom).flip C.isClosedImmersion
  haveI : IsIso j.hom.hom.left :=
    ((Grp.forget _ ⋙ Over.forget _).mapIso (relativeSchemeIso i)).isIso_hom
  exact ⟨relativeGroup C.group T, m ≫ j, IsClosedImmersion.comp _ _,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback C.group.X.hom T.hom) hC⟩

private theorem factors_transportedFamily (C : ClosedSubgroup H) (hC : Smooth C.group.X.hom)
    (i : relativePoints H T ≅ relativePoints G T)
    (V : SchemeOver k) (v : V ⟶ T) (z : V ⟶ G.X) :
    (∃ y : V ⟶ (transportedFamily C hC i).overField,
      y ≫ (transportedFamily C hC i).ambient = lift z v) ↔
      ∃ p : V ⟶ C.group.X, evaluate i v (p ≫ C.inclusion.hom.hom) = z := by
  let Q := transportedFamily C hC i
  let A := (Over.iteratedSliceForward T).obj (Over.mk v)
  let j := Q.inclusion.hom.hom
  let e := relativeSectionEquiv (Over.mk v) G.X
  let f := relativeSectionEquiv (Over.mk v) C.group.X
  let Z : SchemeOver k := (Over.map T.hom).obj A
  let d : V ≅ Z := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (v.left ≫ T.hom) = V.hom
    rw [Category.id_comp, Over.w])
  have he : relativePoint (e.symm z) = d.inv ≫ z := by
    apply Over.OverMorphism.ext
    exact congrArg (·.left) (e.apply_symm_apply z)
  have hv : overBase T A = d.inv ≫ v := by
    apply Over.OverMorphism.ext
    change v.left = 𝟙 _ ≫ v.left
    simp
  have h := factors_relative_iff j (familyAmbient_left Q) (p := e.symm z)
  rw [he, hv, ← comp_lift] at h
  have hh : (∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z v) ↔
      ∃ y : Z ⟶ Q.overField, y ≫ Q.ambient = d.inv ≫ lift z v := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨d.inv ≫ y, by rw [Category.assoc, hy]⟩
    · rintro ⟨y, hy⟩
      exact ⟨d.hom ≫ y, by rw [Category.assoc, hy, d.hom_inv_id_assoc]⟩
  change (∃ y : V ⟶ Q.overField, y ≫ Q.ambient = lift z v) ↔ _
  rw [hh, ← h]
  have hp (p : A ⟶ Q.group.X) : e (p ≫ j) = evaluate i v (f p ≫ C.inclusion.hom.hom) := by
    change e (p ≫ ((Over.pullback T.hom).map C.inclusion.hom.hom ≫
      (relativeSchemeIso i).hom.hom.hom)) = _
    rw [← Category.assoc]
    exact (relativeSchemeIso_natural i (Over.mk v) _).trans
      (congrArg (evaluate i v) (relativeSection_natural (Over.mk v) C.inclusion.hom.hom p))
  constructor
  · rintro ⟨p, hp'⟩
    exact ⟨f p, (hp p).symm.trans ((congrArg e hp').trans (e.apply_symm_apply z))⟩
  · rintro ⟨p, hp'⟩
    refine ⟨f.symm p, e.injective ?_⟩
    rw [hp, f.apply_symm_apply, e.apply_symm_apply, hp']

private theorem extendedBorel (A : AffineAlgebraicGroup k) (hA : IsReductive A)
    (B : ClosedSubgroup A.val) (hB : IsKBorel B)
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] : IsBorel (extendSubgroup K B) := by
  let A' := baseChangedAlgebraicGroup K A
  let B' := extendSubgroup K B
  have hP := borelParabolic A hA B hB
  have hs : Smooth A'.val.X.hom := (smooth_extend_iff K A.val.X).mpr hA.1
  have hc : ConnectedSpace A'.val.X.left := by
    let := hA.2.1
    let : GeometricallyConnected A'.val.X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd A.val.X.hom (fieldSpecMap k K)))
    exact GeometricallyConnected.connectedSpace_of_subsingleton A'.val.X.hom
  have hsB : Smooth B'.group.X.hom := (smooth_extend_iff K B.group.X).mpr hP.2.1
  have hcB : ConnectedSpace B'.group.X.left := by
    obtain ⟨h, hb⟩ := hB
    let D := closedSubgroupAlgebraicGroup B
    let a := fieldSpecMap k (AlgebraicClosure k)
    have hsur : Surjective a := ⟨fun x => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ x⟩⟩
    let : ConnectedSpace (pullback B.group.X.hom a : Scheme.{u}) := hb.1.2.1
    let : ConnectedSpace D.val.X.left :=
      ((MorphismProperty.pullback_fst _ _ hsur).surj.connectedSpace
        (pullback.fst B.group.X.hom a).continuous)
    let := group_geometricallyIrreducible D
    let : Smooth D.val.X.hom := hP.2.1
    exact inferInstanceAs (ConnectedSpace (pullback D.val.X.hom (fieldSpecMap k K) : Scheme.{u}))
  have hvB : Specs.SchemeDerivedGroup.IsSolvable B'.group :=
    (solvable_iff_sections (closedSubgroupAlgebraicGroup (G := A') B') hsB hcB).mpr
      (borel_extended_sections B hB K)
  obtain ⟨Q⟩ := (LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient k A B).1
  have hconn : ConnectedSpace A.val.X.left := by
    let := hA.2.1
    exact GeometricallyConnected.connectedSpace_of_subsingleton A.val.X.hom
  have hproper : IsProper Q.scheme.hom :=
    (LinearAlgebraicGroups.BorelProper.quotientProperIff A hA.1 hconn B hP.2.1 Q).mpr hP.2.2
  obtain ⟨_, e, _⟩ := LinearAlgebraicGroups.HomogeneousQuotient.quotientBaseChange k K Q
  obtain ⟨Q'⟩ := (LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient K A' B').1
  let j : Q'.scheme ≅ (baseChange k K).obj Q.scheme := compareRepresentatives Q' e
  have hproper' : IsProper Q'.scheme.hom := by
    have : IsIso j.hom.left := ((Over.forget _).mapIso j).isIso_hom
    rw [← Over.w j.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper j.hom.left _).mpr
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback Q.scheme.hom (fieldSpecMap k K)) hproper)
  obtain ⟨h, D, hD, hDB⟩ := (LinearAlgebraicGroups.BorelProper.quotientProperIff A' hs hc B' hsB Q').mp hproper'
  exact (isKBorel_iff_of_isAlgClosed A' B').mp
    ⟨h, borel_of_containing_borel hD
      ((smoothConnectedSolvable_extend_iff (closedSubgroupAlgebraicGroup (G := A') B')).mpr
        ⟨hsB, hcB, hvB⟩) hDB⟩

private theorem relativeSection_precomp {V W : Over T} (f : V ⟶ W) {X : SchemeOver k}
    (p : (Over.iteratedSliceForward T).obj W ⟶ (Over.pullback T.hom).obj X) :
    relativeSectionEquiv V X ((Over.iteratedSliceForward T).map f ≫ p) =
      f.left ≫ relativeSectionEquiv W X p := by
  apply Over.OverMorphism.ext
  exact Category.assoc _ _ _

private theorem transportedFamily_geometricType (A D : AffineAlgebraicGroup k)
    (hA : IsReductive A) (hD : IsReductive D) (B : ClosedSubgroup A.val)
    (C : ClosedSubgroup D.val) (hB : IsKBorel B) (hC : IsKBorel C)
    (i : relativePoints D.val T ≅ relativePoints A.val T) :
    SameGeometricType B (transportedFamily C (borelParabolic D hD C hC).2.1 i) := by
  intro K _ _ _ a
  let X := fieldTest k K
  let A' := baseChangedAlgebraicGroup K A
  let B' := extendSubgroup K B
  let C' := extendSubgroup K C
  let E : (groupBaseChange k K).obj D.val ≅ A'.val := relativeSchemeIso (restrictIso a i)
  let C'' := transportSubgroup E C'
  have hs : Smooth A'.val.X.hom := (smooth_extend_iff K A.val.X).mpr hA.1
  have hc : ConnectedSpace A'.val.X.left := by
    let := hA.2.1
    let : GeometricallyConnected A'.val.X.hom :=
      inferInstanceAs (GeometricallyConnected (pullback.snd A.val.X.hom (fieldSpecMap k K)))
    exact GeometricallyConnected.connectedSpace_of_subsingleton A'.val.X.hom
  obtain ⟨g₀, j, hj⟩ := LinearAlgebraicGroups.GeometricBorelConjugacy.borelsConjugate A' hs hc B' C''
    (extendedBorel A hA B hB K) (borelUnderIso E (extendedBorel D hD C hC K))
  let O : Over X := Over.mk (𝟙 X)
  let g : X ⟶ A.val.X := relativeSectionGroupEquiv O A.val g₀
  refine ⟨g, Relative.ParabolicFamilyTransporter.conjugates_iff_factorizations.mpr ?_⟩
  intro V v z
  rw [factors_transportedFamily]
  let W : Over X := Over.mk v
  let W' := (Over.iteratedSliceForward X).obj W
  let α := relativeSectionGroupEquiv W A.val
  let β := relativeSectionGroupEquiv W B.group
  let sectionC := relativeSectionGroupEquiv W C.group
  have hv : α (toUnit W' ≫ g₀) = v ≫ g := by
    let f : W ⟶ O := Over.homMk v (by simp [W, O])
    have h : (Over.iteratedSliceForward X).map f = toUnit W' :=
      (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
    exact h ▸ relativeSection_precomp f g₀
  have he (p : W' ⟶ C'.group.X) :
      α (p ≫ C''.inclusion.hom.hom) = evaluate i (v ≫ a) (sectionC p ≫ C.inclusion.hom.hom) := by
    change α (p ≫ ((Over.pullback X.hom).map C.inclusion.hom.hom ≫ E.hom.hom.hom)) = _
    rw [← Category.assoc]
    exact (relativeSchemeIso_natural (restrictIso a i) W _).trans
      (congrArg _ (relativeSection_natural W C.inclusion.hom.hom p))
  have hj' (p : W' ⟶ B'.group.X) :
      α ((p ≫ j.hom.hom.hom) ≫ C''.inclusion.hom.hom) =
        (v ≫ g) * (β p ≫ B.inclusion.hom.hom : V ⟶ A.val.X) * (v ≫ g)⁻¹ := by
    have hj'' : j.hom.hom.hom ≫ C''.inclusion.hom.hom = _ := hj
    rw [Category.assoc, hj'', MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
    have h : p ≫ toUnit B'.group.X = toUnit W' :=
      (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
    have h' : p ≫ toUnit B'.group.X ≫ g₀ = toUnit W' ≫ g₀ := by
      rw [← Category.assoc, h]
    simp only [h', map_mul, map_inv, hv]
    exact congrArg (fun x : V ⟶ A.val.X => (v ≫ g) * x * (v ≫ g)⁻¹)
      (relativeSection_natural W B.inclusion.hom.hom p)
  constructor
  · rintro ⟨p, hp⟩
    let r : W' ⟶ B'.group.X := sectionC.symm p ≫ j.inv.hom.hom
    refine ⟨β r, (hj' r).symm.trans ?_⟩
    have hji : j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 C''.group.X :=
      ((Grp.forget (SchemeOver K)).mapIso j).inv_hom_id
    have hr : r ≫ j.hom.hom.hom = sectionC.symm p := by
      change (sectionC.symm p ≫ j.inv.hom.hom) ≫ j.hom.hom.hom = _
      rw [Category.assoc, hji]
      exact Category.comp_id _
    rw [hr, he, sectionC.apply_symm_apply, hp]
  · rintro ⟨p, hp⟩
    refine ⟨sectionC (β.symm p ≫ j.hom.hom.hom), ?_⟩
    rw [← he, hj', β.apply_symm_apply, hp]

private theorem alignBorels {S : Type u} [Field S] [Algebra k S] [IsSepClosure k S]
    (A D : AffineAlgebraicGroup k) (hA : IsReductive A) (hD : IsReductive D)
    (B : ClosedSubgroup A.val) (C : ClosedSubgroup D.val) (hB : IsKBorel B) (hC : IsKBorel C)
    (i : relativePoints A.val (fieldTest k S) ≅ relativePoints D.val (fieldTest k S)) :
    ∃ g : fieldTest k S ⟶ A.val.X, Relates B C ((innerAut g).asIso ≪≫ i) := by
  let X := fieldTest k S
  let F := transportedFamily C (borelParabolic D hD C hC).2.1 i.symm
  have hF : SameGeometricType B F := transportedFamily_geometricType A D hA hD B C hB hC i.symm
  obtain ⟨Y, j, _, hj, hs, _, hsur, _, hqc, _⟩ :=
    Relative.ParabolicFamilyTransporter.parabolicTransporter A B
      (borelParabolic A hA B hB) (CommAlgCat.of k S) F hF
  let a : Y ⟶ X := j ≫ snd _ _
  have hY : Nonempty Y.left := ⟨(hsur.surj (IsLocalRing.closedPoint S)).choose⟩
  let : Smooth a.left := hs
  let : QuasiCompact a.left := hqc
  let : IsSepClosed S := IsSepClosure.sep_closed k
  obtain ⟨s, hs'⟩ := exists_rational_point_of_smooth (k := S) a.left hY
  let t : X ⟶ Y := Over.homMk s (by
    rw [← Over.w a, ← Category.assoc, hs']
    exact Category.id_comp _)
  have ht : t ≫ a = 𝟙 X := Over.OverMorphism.ext hs'
  let g : X ⟶ A.val.X := (t ≫ j) ≫ fst A.val.X X
  have hg : Conjugates B F (𝟙 X) g := (hj X (𝟙 X) g).mpr ⟨t, by
    apply CartesianMonoidalCategory.hom_ext
    · exact (lift_fst _ _).symm
    · simpa only [Category.assoc, lift_snd] using ht⟩
  refine ⟨g, ?_⟩
  have hc' := Relative.ParabolicFamilyTransporter.conjugates_iff_factorizations.mp hg
  intro V v x
  let y := (v ≫ g) * x * (v ≫ g)⁻¹
  have e := hc' V v y
  rw [Category.comp_id, factors_transportedFamily] at e
  change (∃ p : V ⟶ C.group.X, p ≫ C.inclusion.hom.hom = evaluate i v y) ↔ _
  constructor
  · rintro ⟨p, hp⟩
    have h := congrArg (evaluate i.symm v) hp
    have hy : evaluate i.symm v (evaluate i v y) = y := evaluate_symm i.symm v y
    rw [hy] at h
    obtain ⟨b, hb⟩ := e.mp ⟨p, h⟩
    change (v ≫ g) * (b ≫ B.inclusion.hom.hom) * (v ≫ g)⁻¹ =
      (v ≫ g) * x * (v ≫ g)⁻¹ at hb
    exact ⟨b, mul_left_cancel (mul_right_cancel hb)⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨p, hp⟩ := e.mpr ⟨b, rfl⟩
    exact ⟨p, by rw [← hp, evaluate_symm]⟩

end Geometry

section Cohomology

variable {S : Type u} [Field S] [Algebra k S]

local instance : TopologicalSpace (Gal(S/k)) := krullTopology k S

local instance (A : GroupScheme k) : TopologicalSpace (RelativeAut A (fieldTest k S)) := ⊥

private theorem displacement_mul (i : relativePoints G (fieldTest k S) ≅
    relativePoints H (fieldTest k S)) (t : RelativeAut G (fieldTest k S)) (σ : Gal(S/k)) :
    displacement k S (t.asIso ≪≫ i) σ =
      t⁻¹ * displacement k S i σ * automorphismAction k S G σ t := by
  apply Aut.ext
  apply Iso.ext
  change ((restrictIso (fieldMap k S σ) (t.asIso ≪≫ i)).hom ≫
      (t.asIso ≪≫ i).inv) =
    (restrictIso (fieldMap k S σ) t.asIso).hom ≫
      (((restrictIso (fieldMap k S σ) i).hom ≫ i.inv) ≫ t.asIso.inv)
  apply NatTrans.ext
  funext V
  rfl

private theorem coboundary_adjustment {M : Type u} [Group M] [TopologicalSpace M]
    (ρ : Gal(S/k) →* MulAut M) (f : M →* RelativeAut G (fieldTest k S))
    (hf : ∀ σ x, f (ρ σ x) = automorphismAction k S G σ (f x))
    (a : Cocycle (automorphismAction k S G))
    (ha : ∀ σ, a σ ∈ f.range) (hi : Function.Injective f)
    (hc : ∀ c : H1 ρ, c = basepoint ρ) :
    ∃ t : RelativeAut G (fieldTest k S), ∀ σ,
      t⁻¹ * a σ * automorphismAction k S G σ t = 1 := by
  classical
  obtain ⟨g, hg⟩ := hi.hasLeftInverse
  have hfg (σ) : f (g (a σ)) = a σ := by
    obtain ⟨x, hx⟩ := ha σ
    rw [← hx, hg x]
  let : DiscreteTopology (RelativeAut G (fieldTest k S)) := ⟨rfl⟩
  let c : Cocycle ρ := ⟨fun σ => g (a σ),
    continuous_of_discreteTopology.comp a.property.1, fun σ τ => by
      apply hi
      rw [map_mul, hf, hfg, hfg, hfg]
      exact a.property.2 σ τ⟩
  obtain ⟨b, hb⟩ := classOf_eq_iff.mp (hc (classOf c))
  refine ⟨f b, fun σ => ?_⟩
  have e : (1 : M) = b⁻¹ * g (a σ) * ρ σ b := hb σ
  simpa only [map_one, map_mul, map_inv, hf, hfg] using (congrArg f e).symm

private theorem changeCocycle {Γ M : Type*} [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M] [ContinuousMul M] (ρ : Γ →* MulAut M)
    (hρ : Continuous (fun x : Γ × M => ρ x.1 x.2)) (a : Cocycle ρ) (t : M) :
    ∃ b : Cocycle ρ, ChangesBy a b t := by
  refine ⟨⟨fun σ => t⁻¹ * a σ * ρ σ t, ?_, ?_⟩, fun _ => rfl⟩
  · exact (continuous_const.mul a.property.1).mul
      (hρ.comp (continuous_id.prodMk continuous_const))
  · intro σ τ
    change t⁻¹ * a (σ * τ) * ρ (σ * τ) t =
      t⁻¹ * a σ * ρ σ t * ρ σ (t⁻¹ * a τ * ρ τ t)
    rw [a.property.2, map_mul ρ, MulAut.mul_apply]
    simp only [map_mul, map_inv]
    group

private def coefficientHom {A D : GroupScheme k} (W : ClosedSubgroup D)
    (inn : groupSections D ⟶ automorphisms A) :
    NonabelianCohomology.Points k S W.group.X →* RelativeAut A (fieldTest k S) :=
  (inn.app (op (fieldTest k S))).hom.comp
    ((groupSectionsMap W.inclusion).app (op (fieldTest k S))).hom |>.comp
      { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }

set_option maxHeartbeats 800000 in
private theorem coefficientHom_action {A D : GroupScheme k} (W : ClosedSubgroup D)
    (inn : groupSections D ⟶ automorphisms A) (σ : Gal(S/k)) (x : NonabelianCohomology.Points k S W.group.X) :
    coefficientHom W inn (pointAction k S W.group.X σ x) =
      automorphismAction k S A σ (coefficientHom W inn x) := by
  let m := groupSectionsMap W.inclusion ≫ inn
  let a := (fieldMap k S σ).op
  let y : (groupSections W.group).obj (op (fieldTest k S)) := ⟨x⟩
  change m.app _ ((groupSections W.group).map a y) = (automorphisms A).map a (m.app _ y)
  exact NatTrans.naturality_apply m a y

/-- Align the Borels over the separable closure and remove their inner displacement. -/
theorem borelInnerAlignment : Specs.BorelInnerAlignment.Statement.{u} := by
  intro k S _ _ _ _ A D Q hA hD B C hB hC Z q hq W inn onLift hinj hH1 hρ i a hai ha
  let T := fieldTest k S
  obtain ⟨g, hg⟩ := alignBorels A D hA hD B C hB hC i
  let t := innerAut g
  let j := t.asIso ≪≫ i
  let ρ := automorphismAction k S A.val
  let : DiscreteTopology (RelativeAut A.val T) := ⟨rfl⟩
  let : ContinuousMul (RelativeAut A.val T) := ⟨continuous_of_discreteTopology⟩
  obtain ⟨b, hb⟩ := changeCocycle ρ hρ a t
  have hdis (σ : Gal(S/k)) : b σ = displacement k S j σ := by
    rw [displacement_mul, ← hai]
    exact hb σ
  let p := (inn.app (op T)).hom
  have ht : t ∈ p.range := ⟨⟨g ≫ q.hom.hom⟩, onLift T g⟩
  have hr (σ : Gal(S/k)) : ρ σ t ∈ p.range := by
    obtain ⟨x, hx⟩ := ht
    refine ⟨(groupSections Q.val).map (fieldMap k S σ).op x, ?_⟩
    rw [NatTrans.naturality_apply inn]
    exact congrArg (ρ σ) hx
  have hbr (σ : Gal(S/k)) : b σ ∈ p.range := by
    rw [hb σ]
    exact p.range.mul_mem (p.range.mul_mem (p.range.inv_mem ht) (ha σ)) (hr σ)
  let M := NonabelianCohomology.Points k S W.subgroup.group.X
  let : TopologicalSpace M := ⊥
  let f := coefficientHom (S := S) W.subgroup inn
  have hf : Function.Injective f := by
    intro x y h
    have e := congrArg ULift.down (hinj (op T) h)
    let := W.subgroup.isClosedImmersion
    let : Mono W.subgroup.inclusion.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono W.subgroup.inclusion.hom.hom).mp e
  have hbf (σ : Gal(S/k)) : b σ ∈ f.range := by
    obtain ⟨x, hx⟩ := hbr σ
    have hrel : Relates B B (inn.app (op T) x).asIso := by
      change inn.app (op T) x = b σ at hx
      rw [hx, hdis]
      exact (hg.restrict (fieldMap k S σ)).trans hg.symm
    obtain ⟨z, hz⟩ := factors_adjoint_borel (borelParabolic A hA B hB) hq W inn
      onLift x.down hrel
    refine ⟨z, ?_⟩
    change inn.app (op T) ⟨z ≫ W.subgroup.inclusion.hom.hom⟩ = b σ
    rw [hz]
    exact hx
  obtain ⟨s, hs⟩ := coboundary_adjustment _ f (coefficientHom_action W.subgroup inn) b hbf hf hH1
  refine ⟨s.asIso ≪≫ j, fun σ => ?_⟩
  have e : displacement k S (s.asIso ≪≫ j) σ = 1 := by
    rw [displacement_mul, ← hdis]
    exact hs σ
  apply Iso.ext
  have he := congrArg (fun z : RelativeAut A.val T => z.asIso.hom) e
  change (restrictIso (fieldMap k S σ) (s.asIso ≪≫ j)).hom ≫ (s.asIso ≪≫ j).inv =
    𝟙 _ at he
  exact (cancel_mono (s.asIso ≪≫ j).inv).mp (he.trans
    (s.asIso ≪≫ j).hom_inv_id.symm)

end Cohomology

end

end LinearAlgebraicGroups.Descent.BorelInnerAlignment
