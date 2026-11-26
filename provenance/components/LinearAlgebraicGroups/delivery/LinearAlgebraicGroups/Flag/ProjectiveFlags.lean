import Specs.LinearAlgebraicGroups.Flag.ProjectiveFlags
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.BorelProper
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.ProjectiveFlags

open _root_.LinearAlgebraicGroups.Specs
open Specs.ProjectiveSpaces (projectiveSpace)

open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private baseChangeMapIsPullback from LinearAlgebraicGroups.Flag.HomogeneousQuotient

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

set_option backward.isDefEq.respectTransparency false in
/-- A geometric group element translates the base change of an equivariant image. -/
private theorem translateImages {G : GroupScheme k} {X : SchemeOver k}
    (a : ModObj G.X X) (q : G.X ⟶ X)
    (hq : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul)
    (p r : 𝟙_ (SchemeOver K) ⟶ (baseChange k K).obj G.X) :
    ∃ e : (baseChange k K).obj X ≅ (baseChange k K).obj X,
      p ≫ (baseChange k K).map q ≫ e.hom = r ≫ (baseChange k K).map q := by
  let := a
  let : ModObj G.X G.X := ModObj.regular G.X
  let : IsModHom G.X q := ⟨hq⟩
  let B := baseChange k K
  let F := Over.map (fieldSpecMap k K)
  let A : F ⊣ B := Over.mapPullbackAdj _
  let T : SchemeOver K := 𝟙_ _
  let C := B.obj X
  let π : F.obj C ⟶ X := A.counit.app X
  let p₀ : F.obj T ⟶ G.X := (A.homEquiv T G.X).symm p
  let r₀ : F.obj T ⟶ G.X := (A.homEquiv T G.X).symm r
  let g := r₀ * p₀⁻¹
  let translate (s : F.obj T ⟶ G.X) : C ⟶ C :=
    A.homEquiv C X ((F.map (toUnit C) ≫ s) • π)
  have htranslate (s : F.obj T ⟶ G.X) :
      F.map (translate s) ≫ π = (F.map (toUnit C) ≫ s) • π := by
    exact (A.homEquiv C X).symm_apply_apply _
  have hcomp {s t : F.obj T ⟶ G.X} (hst : s * t = 1) :
      translate t ≫ translate s = 𝟙 C := by
    apply (A.homEquiv C X).symm.injective
    rw [A.homEquiv_symm_apply, A.homEquiv_symm_apply, F.map_comp, Category.assoc,
      htranslate s, ModObj.comp_smul, htranslate t, ← Functor.map_comp_assoc, comp_toUnit,
      F.map_id, Category.id_comp, ← mul_smul, ← MonObj.comp_mul, hst, MonObj.comp_one, one_smul]
  let e : C ≅ C :=
    ⟨translate g, translate g⁻¹, hcomp (inv_mul_cancel g), hcomp (mul_inv_cancel g)⟩
  refine ⟨e, ?_⟩
  change p ≫ B.map q ≫ translate g = r ≫ B.map q
  have hp : F.map (p ≫ B.map q) ≫ π = p₀ ≫ q := by
    exact A.homEquiv_naturality_right_symm _ _
  have hr : F.map (r ≫ B.map q) ≫ π = r₀ ≫ q := by
    exact A.homEquiv_naturality_right_symm _ _
  apply (A.homEquiv T X).symm.injective
  rw [A.homEquiv_symm_apply, A.homEquiv_symm_apply, hr, ← Category.assoc, F.map_comp,
    Category.assoc, htranslate, ModObj.comp_smul, hp, ← Functor.map_comp_assoc, comp_toUnit,
    toUnit_unique (toUnit T) (𝟙 T), F.map_id, Category.id_comp, ← IsModHom.map_smul]
  change (g * p₀) ≫ q = r₀ ≫ q
  rw [show g * p₀ = r₀ by simp [g]]

private theorem reduced_of_flat_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact isReduced_of_injective (f.stalkMap x).hom ‹RingHom.FaithfullyFlat _›.injective

set_option backward.isDefEq.respectTransparency false in
private theorem closedPoint_lift {K : Type u} [Field K] [IsAlgClosed K]
    {X Y : SchemeOver K} [LocallyOfFiniteType X.hom]
    (q : X ⟶ Y) [Surjective q.left] {y : Y.left} (hy : IsClosed {y}) :
    ∃ p : 𝟙_ (SchemeOver K) ⟶ X, (p ≫ q).left (IsLocalRing.closedPoint K) = y := by
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨x₀, hx₀⟩ := q.left.surjective y
  obtain ⟨x, hx, hxc⟩ := nonempty_inter_closedPoints
    (show (q.left ⁻¹' {y}).Nonempty from ⟨x₀, hx₀⟩)
    (hy.preimage q.left.continuous).isLocallyClosed
  let p : 𝟙_ (SchemeOver K) ⟶ X := Over.homMk (pointOfClosedPoint X.hom x hxc)
    (pointOfClosedPoint_comp X.hom x hxc)
  refine ⟨p, ?_⟩
  change (pointOfClosedPoint X.hom x hxc ≫ q.left) (IsLocalRing.closedPoint K) = y
  rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  exact hx

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_after_baseChange {G : GroupScheme k} {X : SchemeOver k}
    [IsAlgClosed K]
    (a : ModObj G.X X) (q : G.X ⟶ X)
    (hq : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul)
    [LocallyOfFinitePresentation ((baseChange k K).obj X).hom]
    [LocallyOfFiniteType ((baseChange k K).obj G.X).hom]
    [IsReduced ((baseChange k K).obj G.X).left]
    [Flat ((baseChange k K).map q).left] [Surjective ((baseChange k K).map q).left] :
    Smooth ((baseChange k K).obj X).hom := by
  let X' := (baseChange k K).obj X
  let q' := (baseChange k K).map q
  let : IsReduced X'.left := reduced_of_flat_surjective q'.left
  let : JacobsonSpace X'.left := LocallyOfFiniteType.jacobsonSpace X'.hom
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H X'.hom.smoothLocus.2.isClosed_compl.isLocallyClosed
  let : Nonempty X'.left := ⟨x⟩
  obtain ⟨y, hy : y ∈ X'.hom.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    X'.hom.dense_smoothLocus_of_perfectField.nonempty X'.hom.smoothLocus.2.isLocallyClosed
  obtain ⟨p, hp⟩ := closedPoint_lift q' hxc
  obtain ⟨r, hr⟩ := closedPoint_lift q' hyc
  obtain ⟨e, he⟩ := translateImages a q hq p r
  have he' : e.hom.left x = y := by
    rw [← hp, ← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, he, hr]
  rw! [← he', ← e.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show e.hom.left ≫ X'.hom = X'.hom from e.hom.w] at hy
  exact hx hy

set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_smooth_equivariant_quotient {G : GroupScheme k} {X : SchemeOver k}
    [Smooth G.X.hom] [LocallyOfFinitePresentation X.hom]
    (a : ModObj G.X X) (q : G.X ⟶ X) [Smooth q.left] [Surjective q.left]
    (hq : μ[G.X] ≫ q = (𝟙 G.X ⊗ₘ q) ≫ a.smul) : Smooth X.hom := by
  let K := AlgebraicClosure k
  let B := baseChange k K
  let f := fieldSpecMap k K
  let : Smooth (B.obj G.X).hom := by
    change Smooth (pullback.snd G.X.hom f)
    infer_instance
  let : IsReduced (B.obj G.X).left := isReduced_of_smooth_over_field (B.obj G.X).hom
  let : LocallyOfFiniteType (B.obj G.X).hom := inferInstance
  let : LocallyOfFinitePresentation (B.obj X).hom := by
    change LocallyOfFinitePresentation (pullback.snd X.hom f)
    infer_instance
  let hp := baseChangeMapIsPullback K q
  let : Flat (B.map q).left := MorphismProperty.of_isPullback (P := @Flat) hp.flip inferInstance
  let : Surjective (B.map q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hp.flip inferInstance
  apply MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := f)
  · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · exact smooth_after_baseChange (K := K) a q hq

set_option backward.isDefEq.respectTransparency false in
/-- The parabolic quotient is smooth and admits a closed equivariant projective
embedding, conditional on the Borel properness results. -/
theorem smoothProjectiveQuotient_conditional :
    Specs.BorelProper.GeometricBorelQuotientProper.{u} →
    Specs.BorelProper.QuotientProperIff.{u} →
    Specs.ProjectiveFlags.SmoothProjectiveQuotient.{u} := by
  intro _ hproper k _ G P hP
  obtain ⟨⟨hG, hGconnected, _⟩, hPsmooth, hBorel⟩ := hP
  let : GeometricallyConnected G.val.X.hom := hGconnected
  have hc : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  obtain ⟨hExists, hTorsor⟩ := HomogeneousQuotient.homogeneousQuotient k G P
  refine ⟨hExists, ?_⟩
  intro Q
  have hQ : IsProper Q.scheme.hom := (hproper G hG hc P hPsmooth Q).2 hBorel
  obtain ⟨V, _, _, _, a, x, O, Q₀, hstab, ⟨e₀, he₀⟩, hlinear⟩ :=
    QuotientEmbedding.smoothQuotientEmbedding k G P hG
  obtain ⟨e₁, he₁, _⟩ := HomogeneousQuotient.quotientUniqueness Q Q₀
  let e := e₁ ≪≫ e₀
  have he : Q.projection ≫ e.hom = O.projection := by
    change Q.projection ≫ (e₁.hom ≫ e₀.hom) = O.projection
    rw [← Category.assoc, he₁, he₀]
  let : ModObj G.val.X O.orbit := O.action
  let : IsMonHom (Iso.refl G.val.X).hom := inferInstanceAs (IsMonHom (𝟙 G.val.X))
  let b : ModObj G.val.X Q.scheme := ModObj.ofIso (Iso.refl G.val.X) e.symm
  have hb : b.smul ≫ e.hom = (𝟙 G.val.X ⊗ₘ e.hom) ≫ O.action.smul := by
    change ((𝟙 G.val.X ⊗ₘ e.hom) ≫ O.action.smul ≫ e.inv) ≫ e.hom = _
    simp
  have hq : μ[G.val.X] ≫ Q.projection = (𝟙 G.val.X ⊗ₘ Q.projection) ≫ b.smul := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, he, hb, O.actionProjection]
    symm
    rw [← Category.assoc, ← id_tensor_comp, he]
  let : Smooth G.val.X.hom := hG
  let : IsProper Q.scheme.hom := hQ
  let : Smooth Q.projection.left := (hTorsor Q).2 hPsmooth
  let : Surjective Q.projection.left := Q.surjective
  refine ⟨smooth_of_smooth_equivariant_quotient b Q.projection hq, hQ, ?_⟩
  let i := O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x
  let j := e.hom ≫ i
  have hj : Q.projection ≫ j = Specs.SmoothOrbit.orbitMap a x := by
    unfold j
    rw [← Category.assoc, he]
    apply Over.OverMorphism.ext
    change O.projection.left ≫
      (O.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap a x).left.imageι) = _
    rw [← Category.assoc, O.factors, Scheme.Hom.toImage_imageι]
  have hbj : b.smul ≫ j = (𝟙 G.val.X ⊗ₘ j) ≫ a.smul := by
    change b.smul ≫ (e.hom ≫ i) = (𝟙 G.val.X ⊗ₘ (e.hom ≫ i)) ≫ a.smul
    have hO : O.action.smul ≫ i = (𝟙 G.val.X ⊗ₘ i) ≫ a.smul := O.actionInclusion
    rw [← Category.assoc, hb, Category.assoc, hO, ← Category.assoc, ← id_tensor_comp]
  let : IsOpenImmersion O.openInClosure.left := O.isOpen
  let : IsImmersion j.left := by
    change IsImmersion (e.hom.left ≫
      (O.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap a x).left.imageι))
    infer_instance
  let : IsProper (projectiveSpace k V).hom := ProjectiveSpaces.projectiveSpaceProper k V
  let : IsProper (j.left ≫ (projectiveSpace k V).hom) := Over.w j ▸ hQ
  let : IsProper j.left := IsProper.of_comp j.left (projectiveSpace k V).hom
  have hclosed : IsClosedImmersion j.left :=
    IsClosedImmersion.of_isPreimmersion j.left j.left.isClosedMap.isClosed_range
  exact ⟨V, inferInstance, inferInstance, inferInstance, a, x, b, j, hclosed,
    hj, hq, hbj, hstab, hlinear⟩

end

end LinearAlgebraicGroups.ProjectiveFlags

universe v8_closure_4936d2b86b7ee184_u0
theorem _root_.«LinearAlgebraicGroups».«ProjectiveFlags».«smoothProjectiveQuotient» : _root_.«LinearAlgebraicGroups».«Specs».«ProjectiveFlags».«SmoothProjectiveQuotient».{v8_closure_4936d2b86b7ee184_u0} :=
  @_root_.«LinearAlgebraicGroups».«ProjectiveFlags».«smoothProjectiveQuotient_conditional».{v8_closure_4936d2b86b7ee184_u0} (@_root_.«LinearAlgebraicGroups».«BorelProper».«geometricBorelQuotientProper».{v8_closure_4936d2b86b7ee184_u0}) (@_root_.«LinearAlgebraicGroups».«BorelProper».«quotientProperIff».{v8_closure_4936d2b86b7ee184_u0})
