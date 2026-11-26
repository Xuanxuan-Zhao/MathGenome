import Specs.LinearAlgebraicGroups.Flag.SchubertClosures
import Specs.LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Flag.SimpleParabolicProduct
import LinearAlgebraicGroups.Flag.GallerySubwords
import LinearAlgebraicGroups.Reductive.BorelProper
import Mathlib.Data.List.Induction
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Flag.BruhatCells
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Pointwise

universe u

namespace LinearAlgebraicGroups.Flag.SchubertClosures

open LinearAlgebraicGroups.Specs
open Specs.SchubertClosures
open Specs.AbstractPairing (Datum Root)
open Specs.BruhatOrbitParametrization (Cell IsRepresentative)
open Specs.DatumAndWeyl (Identification)
open Specs.GallerySubwords (IsReduced)
open Specs.QuotientEmbedding (Presentation)
open Specs.SimpleParabolicProduct (doubleCoset)
open Specs.SimpleRoots (IsBaseFor evaluate wordProduct wordLength)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

private theorem range_closureIdeal {X Y : Scheme.{u}} (i : X ⟶ Y) :
    Set.range (closureIdeal i).subschemeι = closure (Set.range i) := by
  rw [closureIdeal, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

private theorem vanishingSubschemeReduced {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  apply (IsReduced.iff_of_openCover _ I.subschemeCover.openCover).2
  intro U
  change IsReduced (Spec (CommRingCat.of (_ ⧸ I.ideal U)))
  apply (affine_isReduced_iff _).2
  apply (Ideal.isRadical_iff_quotient_reduced _).1
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

attribute [local instance] MvPolynomial.gradedAlgebra in
private theorem projectiveSpaceIrreducible {k J : Type u} [Field k]
    (h : Nonempty (Specs.ProjectiveSpaces.coordinateProjectiveSpace k J).left) :
    IrreducibleSpace (Specs.ProjectiveSpaces.coordinateProjectiveSpace k J).left := by
  let grading := Specs.ProjectiveSpaces.grading k J
  change Nonempty (ProjectiveSpectrum grading) at h
  change IrreducibleSpace (ProjectiveSpectrum grading)
  obtain ⟨x⟩ := h
  let generic : ProjectiveSpectrum grading :=
    ⟨⊥, by simpa only [HomogeneousIdeal.toIdeal_bot] using (Ideal.isPrime_bot : (⊥ : Ideal (MvPolynomial J k)).IsPrime),
      fun hb ↦ x.not_irrelevant_le (hb.trans bot_le)⟩
  have hclosure : closure ({generic} : Set (ProjectiveSpectrum grading)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    apply (ProjectiveSpectrum.le_iff_mem_closure grading generic y).1
    change (⊥ : HomogeneousIdeal grading) ≤ y.asHomogeneousIdeal
    exact bot_le
  exact { isPreirreducible_univ := hclosure ▸ isPreirreducible_singleton.closure
          toNonempty := ⟨generic⟩ }

private theorem snd_isOpen {k : Type u} [Field k] (X Z : SchemeOver k) :
    IsOpenMap (snd X Z).left := by
  have hp : IsPullback (fst X Z) (snd X Z) (toUnit X) (toUnit Z) := by
    refine IsPullback.mk' (Subsingleton.elim _ _) ?_ ?_
    · intro _ _ _ h₁ h₂
      exact CartesianMonoidalCategory.hom_ext _ _ h₁ h₂
    · intro _ f g _
      exact ⟨lift f g, lift_fst _ _, lift_snd _ _⟩
  let : UniversallyOpen X.hom := inferInstance
  let : UniversallyOpen (snd X Z).left :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) (hp.map (Over.forget _))
      (show UniversallyOpen (toUnit X).left from inferInstanceAs (UniversallyOpen X.hom))
  exact (snd X Z).left.isOpenMap

private def saturation {X Z : Type*} (p : X → Z) (S : Set X) : Set X :=
  p ⁻¹' (p '' S)

private theorem closure_saturation {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {p : X → Z} (hcont : Continuous p) (hopen : IsOpenMap p) (hclosed : IsClosedMap p)
    (S : Set X) : closure (saturation p S) = saturation p (closure S) := by
  unfold saturation
  rw [← hopen.preimage_closure_eq_closure_preimage hcont,
    hclosed.closure_image_eq_of_continuous hcont]

private theorem saturation_iUnion {X Z : Type*} {Idx : Type*} (p : X → Z) (F : Idx → Set X)
    (J : Set Idx) : saturation p (⋃ v ∈ J, F v) = ⋃ v ∈ J, saturation p (F v) := by
  simp only [saturation, Set.image_iUnion, Set.preimage_iUnion]

private theorem closure_support_of_partition {Idx X : Type*} [TopologicalSpace X]
    (F : Idx → Set X) (hne : ∀ v, (F v).Nonempty) (hdis : ∀ v w, v ≠ w → Disjoint (F v) (F w))
    {J : Set Idx} {w : Idx} (hJ : closure (F w) = ⋃ v ∈ J, F v) (v : Idx) :
    v ∈ J ↔ F v ⊆ closure (F w) := by
  rw [hJ]
  refine ⟨fun hv _ hx ↦ Set.mem_iUnion₂.mpr ⟨v, hv, hx⟩, ?_⟩
  intro hv
  obtain ⟨x, hx⟩ := hne v
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (hv hx)
  by_contra hn
  exact (Set.disjoint_left.mp (hdis v z (fun he ↦ hn (he ▸ hz)))) hx hxz


section Induction

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing Idx ℤ X Y) (b : P.Base)

private theorem subwordProducts_nil :
    subwordProducts P b [] = {1} := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain rfl := List.sublist_nil.mp hr
    rfl
  · intro hx
    exact ⟨[], List.Sublist.refl _, (Set.mem_singleton_iff.mp hx).symm⟩

private theorem subwordProducts_snoc (l : List b.support) (s : b.support) :
    subwordProducts P b (l ++ [s]) = subwordProducts P b l ∪
      (fun v ↦ v * RootPairing.weylGroup.ofIdx P s.val) '' subwordProducts P b l := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨a, c, rfl, ha, hc⟩ := List.sublist_append_iff.mp hr
    have hcases : c = [] ∨ c = [s] := by
      cases c with
      | nil => exact Or.inl rfl
      | cons t q =>
        have hlen := hc.length_le
        have hq : q = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
        subst q
        have ht : t = s := by simpa using hc.subset (List.mem_singleton_self t)
        exact Or.inr (congrArg (fun z ↦ [z]) ht)
    rcases hcases with rfl | rfl
    · exact Or.inl ⟨a, ha, by simp⟩
    · exact Or.inr ⟨wordProduct P b a, ⟨a, ha, rfl⟩, by simp [wordProduct]⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨_, ⟨r, hr, rfl⟩, rfl⟩)
    · exact ⟨r, hr.trans (List.sublist_append_left _ _), rfl⟩
    · exact ⟨r ++ [s], hr.append (List.Sublist.refl _), by simp [wordProduct]⟩

open private exchange_of_negative from LinearAlgebraicGroups.Flag.GallerySubwords

private theorem reduced_snoc [Finite Idx] [P.IsReduced]
    {l : List b.support} {s : b.support} (h : IsReduced P b (l ++ [s])) :
    IsReduced P b l ∧ b.IsPos (P.weylGroupToPerm (wordProduct P b l) s.val) := by
  have hle (r : List b.support) : wordLength P b (wordProduct P b r) ≤ r.length :=
    Nat.sInf_le ⟨r, rfl, rfl⟩
  obtain ⟨r, hr, hprod⟩ :=
    Nat.sInf_mem (s := {n | ∃ r : List b.support, r.length = n ∧
      wordProduct P b r = wordProduct P b l}) ⟨l.length, l, rfl, rfl⟩
  have heq : wordProduct P b (r ++ [s]) = wordProduct P b (l ++ [s]) := by
    simpa [wordProduct] using congrArg (fun w ↦ w * RootPairing.weylGroup.ofIdx P s.val) hprod
  have hmin := hle (r ++ [s])
  change r.length = wordLength P b (wordProduct P b l) at hr
  rw [heq, h] at hmin
  simp only [List.length_append, List.length_singleton, hr] at hmin
  refine ⟨Nat.le_antisymm (hle l) (by omega), ?_⟩
  by_contra hneg
  obtain ⟨pre, post, i, hsplit, _, hdel⟩ := exchange_of_negative P b l s hneg
  have hmin' := hle (pre ++ post)
  rw [hdel, h, hsplit] at hmin'
  simp only [List.length_append, List.length_cons] at hmin'
  omega

variable {Z : Type*} [TopologicalSpace Z]

private theorem closure_subword_union (F : P.weylGroup → Set Z) (hbase : IsClosed (F 1))
    [Finite Idx] [P.IsReduced]
    (hstep : ∀ (s : b.support), ∃ (S : Set Z → Set Z),
      (∀ v, S (F v) = F v ∪ F (v * RootPairing.weylGroup.ofIdx P s.val)) ∧
      (∀ v, b.IsPos (P.weylGroupToPerm v s.val) →
        closure (F (v * RootPairing.weylGroup.ofIdx P s.val)) = S (closure (F v))) ∧
      (∀ J : Set P.weylGroup, S (⋃ v ∈ J, F v) = ⋃ v ∈ J, S (F v)))
    (l : List b.support) (hl : IsReduced P b l) :
    closure (F (wordProduct P b l)) = ⋃ v ∈ subwordProducts P b l, F v := by
  induction l using List.reverseRecOn with
  | nil =>
    rw [subwordProducts_nil]
    simp [wordProduct]
  | append_singleton l s ih =>
    obtain ⟨hr, hp⟩ := reduced_snoc P b hl
    obtain ⟨S, hS, hinc, hUnion⟩ := hstep s
    rw [show wordProduct P b (l ++ [s]) =
      wordProduct P b l * RootPairing.weylGroup.ofIdx P s.val by simp [wordProduct],
      hinc _ hp, ih hr, hUnion, subwordProducts_snoc]
    simp only [hS, Set.biUnion_union, Set.biUnion_image, Set.iUnion_union_distrib]

end Induction

section Schemes

variable {k : Type u} [Field k]

open private exists_field_point from LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus
open private quotientMapExists quotientSeparatedFiniteType
  from LinearAlgebraicGroups.Reductive.BorelProper
open private projection_eq_iff basePoint_closed from LinearAlgebraicGroups.Flag.QuotientEmbedding

/-- Every underlying point of a scheme admits a lift from an algebraically closed field. -/
private theorem geometric_point_at (X : SchemeOver k) (x : X.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsAlgClosed K)
      (p : Over.mk (fieldSpecMap k K) ⟶ X), p.left (IsLocalRing.closedPoint K) = x := by
  obtain ⟨L, _, _, r, hr⟩ := exists_field_point X x
  let K := AlgebraicClosure L
  let φ := (algebraMap L K).comp (algebraMap k L)
  let : Algebra k K := φ.toAlgebra
  let e : Over.mk (fieldSpecMap k K) ⟶ (testSpec k).obj (.op (CommAlgCat.of k L)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap L K))) (by
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap k L))
        (CommRingCat.ofHom (algebraMap L K))).symm)
  exact ⟨K, inferInstance, inferInstance, inferInstance, e ≫ r,
    (congrArg r.left (Subsingleton.elim _ (IsLocalRing.closedPoint L))).trans hr⟩

private theorem quotient_isOpen {M : GroupScheme k} {B : ClosedSubgroup M} (Q : Presentation B) :
    IsOpenMap Q.projection.left := by
  letI := Q.flat
  letI := Q.finitePresentation
  exact Q.projection.left.isOpenMap

private theorem quotient_map_geometry {M : GroupScheme k} {B P : ClosedSubgroup M}
    (Q : Presentation B) (R : Presentation P)
    (hBP : Specs.SchemeDerivedGroup.IsSubgroupOf B P) (hQ : IsProper Q.scheme.hom) :
    ∃ p : Q.scheme ⟶ R.scheme, Q.projection ≫ p = R.projection ∧
      IsOpenMap p.left ∧ IsClosedMap p.left := by
  obtain ⟨p, hp⟩ := quotientMapExists Q R hBP
  have hcomp : (R.projection.left : M.X.left → R.scheme.left) =
      p.left ∘ Q.projection.left := by rw [← hp]; rfl
  haveI := (quotientSeparatedFiniteType R).1
  haveI : IsProper (p.left ≫ R.scheme.hom) := by rw [Over.w]; exact hQ
  haveI : IsProper p.left := IsProper.of_comp p.left R.scheme.hom
  refine ⟨p, hp, ?_, p.left.isClosedMap⟩
  intro V hV
  have he : R.projection.left '' (Q.projection.left ⁻¹' V) = p.left '' V := by
    calc
      _ = p.left '' (Q.projection.left '' (Q.projection.left ⁻¹' V)) := by
        rw [Set.image_image, hcomp]
        rfl
      _ = _ := congrArg (fun S ↦ p.left '' S) (Q.surjective.1.image_preimage V)
  exact he ▸ quotient_isOpen R _ (hV.preimage Q.projection.left.continuous)

private theorem range_inverseImage {X Y Z W : SchemeOver k}
    {i : X ⟶ Y} {j : X ⟶ Z} {q : Y ⟶ W} {f : Z ⟶ W}
    (h : IsPullback i j q f) :
    Set.range i.left = q.left ⁻¹' Set.range f.left := by
  have hp : IsPullback j.left i.left f.left q.left := h.flip.map (Over.forget _)
  have he := Scheme.image_preimage_eq_of_isPullback hp Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at he
  exact he

private theorem comp_apply_eq {X Y Z : SchemeOver k} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Z} (h : a ≫ b = c) (x : X.left) : b.left (a.left x) = c.left x :=
  congrArg (fun f : X ⟶ Z ↦ f.left x) h

private def sectionsIn {X Z : SchemeOver k} (Y : SchemeOver k) (i : X ⟶ Z) : Set (Y ⟶ Z) :=
  Set.range (fun a : Y ⟶ X ↦ a ≫ i)

private def multiplyInto {M : GroupScheme k} (P : ClosedSubgroup M) {X : SchemeOver k}
    (i : X ⟶ M.X) : X ⊗ P.group.X ⟶ M.X :=
  (fst X P.group.X ≫ i) * (snd X P.group.X ≫ P.inclusion.hom.hom)

private theorem comp_multiplyInto {M : GroupScheme k} (P : ClosedSubgroup M)
    {X Y : SchemeOver k} (i : X ⟶ M.X) (p : Y ⟶ X ⊗ P.group.X) :
    p ≫ multiplyInto P i =
      (p ≫ fst X P.group.X ≫ i) * (p ≫ snd X P.group.X ≫ P.inclusion.hom.hom) := by
  simp only [multiplyInto, MonObj.comp_mul]

/-- Right multiplication by the subgroup has the same support as saturation by the quotient. -/
private theorem range_multiplyInto {M : GroupScheme k} (P : ClosedSubgroup M) {X : SchemeOver k}
    (i : X ⟶ M.X) (R : Presentation P) :
    Set.range (multiplyInto P i).left = R.projection.left ⁻¹' (R.projection.left '' Set.range i.left) := by
  let m := multiplyInto P i
  have hm : m ≫ R.projection = fst X P.group.X ≫ i ≫ R.projection := by
    apply ((projection_eq_iff R (fst X P.group.X ≫ i) m).2 _).symm
    rw [show m = (fst X P.group.X ≫ i) *
        (snd X P.group.X ≫ P.inclusion.hom.hom) from rfl, inv_mul_cancel_left]
    exact ⟨snd X P.group.X, rfl⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨i.left ((fst X P.group.X).left y), ⟨_, rfl⟩,
      (congrArg (fun f : X ⊗ P.group.X ⟶ R.scheme ↦ f.left y) hm).symm⟩
  · rintro x ⟨_, ⟨y, rfl⟩, hy⟩
    let H := pullback (i ≫ R.projection) R.projection
    have hp := (IsPullback.of_hasPullback (i ≫ R.projection) R.projection).map (Over.forget _)
    obtain ⟨t, _, ht⟩ := Scheme.exists_preimage_of_isPullback hp y x hy
    let a : H ⟶ M.X := pullback.fst _ _ ≫ i
    let b : H ⟶ M.X := pullback.snd _ _
    have hab : a ≫ R.projection = b ≫ R.projection := by
      simpa only [a, b, Category.assoc] using (pullback.condition (f := i ≫ R.projection) (g := R.projection))
    have hmem := (projection_eq_iff R a b).1 hab
    change ∃ d : H ⟶ P.group.X, d ≫ P.inclusion.hom.hom = a⁻¹ * b at hmem
    obtain ⟨d, hd⟩ := hmem
    have hmul : lift (pullback.fst (i ≫ R.projection) R.projection) d ≫ m = b := by
      change lift (pullback.fst (i ≫ R.projection) R.projection) d ≫ multiplyInto P i = b
      simp only [comp_multiplyInto, ← Category.assoc, lift_fst, lift_snd]
      rw [show pullback.fst (i ≫ R.projection) R.projection ≫ i = a from rfl, hd, mul_inv_cancel_left]
    exact ⟨(lift (pullback.fst (i ≫ R.projection) R.projection) d).left t,
      (congrArg (fun f : H ⟶ M.X ↦ f.left t) hmul).trans ht⟩

private theorem range_mul_bruhat {M : GroupScheme k} (P : ClosedSubgroup M)
    {X X₀ X₁ : SchemeOver k} (i : X ⟶ M.X) (i₀ : X₀ ⟶ M.X) (i₁ : X₁ ⟶ M.X)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      let Y := Over.mk (fieldSpecMap k K)
      sectionsIn Y i * (SubgroupSections P Y : Set (Y ⟶ M.X)) = sectionsIn Y i₀ ∪ sectionsIn Y i₁) :
    Set.range (multiplyInto P i).left = Set.range i₀.left ∪ Set.range i₁.left := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨K, _, _, _, p, hp⟩ := geometric_point_at (X ⊗ P.group.X) y
    let Y := Over.mk (fieldSpecMap k K)
    have hz : p ≫ multiplyInto P i ∈ sectionsIn Y i * (SubgroupSections P Y : Set (Y ⟶ M.X)) := by
      rw [comp_multiplyInto]
      exact Set.mem_mul.mpr ⟨_, ⟨p ≫ fst X P.group.X, rfl⟩, _, ⟨p ≫ snd X P.group.X, rfl⟩, rfl⟩
    rw [h K] at hz
    have hx := congrArg (multiplyInto P i).left hp
    rcases hz with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a.left _, (comp_apply_eq ha (IsLocalRing.closedPoint K)).trans hx⟩
    · exact Or.inr ⟨a.left _, (comp_apply_eq ha (IsLocalRing.closedPoint K)).trans hx⟩
  · have fromCell {Z : SchemeOver k} (j : Z ⟶ M.X)
        (hj : ∀ Y : SchemeOver k, sectionsIn Y j ⊆ sectionsIn Y i₀ ∪ sectionsIn Y i₁) :
        Set.range j.left ⊆ Set.range (multiplyInto P i).left := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨K, _, _, _, p, hp⟩ := geometric_point_at Z y
      have hmem := hj _ ⟨p, rfl⟩
      rw [← h K] at hmem
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Set.mem_mul.mp hmem
      change (a ≫ i) * (b ≫ P.inclusion.hom.hom) = p ≫ j at hab
      have heq : lift a b ≫ multiplyInto P i = p ≫ j := by
        simpa only [comp_multiplyInto, ← Category.assoc, lift_fst, lift_snd] using hab
      exact ⟨(lift a b).left (IsLocalRing.closedPoint K),
        (comp_apply_eq heq (IsLocalRing.closedPoint K)).trans (congrArg j.left hp)⟩
    exact Set.union_subset (fromCell i₀ (fun _ _ hx ↦ Or.inl hx)) (fromCell i₁ (fun _ _ hx ↦ Or.inr hx))

end Schemes

section Representatives

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D D' : Datum T}

open private some_representative_label normalizer_ratio_mem_torus
  from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

private theorem quotient_eq_iff_torus (I : Identification D) {Y : SchemeOver k}
    (p q : Y ⟶ I.normalizer.group.X) :
    p ≫ I.quotient.hom.hom = q ≫ I.quotient.hom.hom ↔
      (p ≫ I.normalizer.inclusion.hom.hom)⁻¹ * (q ≫ I.normalizer.inclusion.hom.hom) ∈
        SubgroupSections T Y := by
  constructor
  · exact normalizer_ratio_mem_torus I
  · rintro ⟨t, ht⟩
    haveI : IsClosedImmersion I.normalizer.inclusion.hom.hom.left :=
      I.normalizer.isClosedImmersion
    haveI : Mono I.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
    have hi : I.torusInclusion.hom.hom ≫ I.normalizer.inclusion.hom.hom =
        T.inclusion.hom.hom := congrArg (Grp.forget (SchemeOver k)).map I.inclusion_eq
    have h : t ≫ I.torusInclusion.hom.hom = p⁻¹ * q := by
      apply (cancel_mono I.normalizer.inclusion.hom.hom).mp
      rwa [Category.assoc, hi, MonObj.mul_comp, GrpObj.inv_comp]
    have hh : (p⁻¹ * q) ≫ I.quotient.hom.hom = 1 := by
      rw [← h, Category.assoc, I.isQuotient.1.w, ← Category.assoc]
      congr 1
      exact Subsingleton.elim _ _
    rw [MonObj.mul_comp, GrpObj.inv_comp] at hh
    exact inv_mul_eq_one.mp hh

private theorem labels_eq_iff_quotient_eq (I : Identification D)
    {v w : D.rootDatum.weylGroup} {n m : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X}
    (hn : IsRepresentative I v n) (hm : IsRepresentative I w m) :
    n ≫ I.quotient.hom.hom = m ≫ I.quotient.hom.hom ↔ v = w := by
  let Y := 𝟙_ (SchemeOver k)
  let F := I.image.constantGroup
  have hinj : Function.Injective F.sectionPoint := by
    intro a b h
    have hh := congrArg (fun f ↦ F.families Y (toUnit Y ≫ f)) h
    rw [F.constant, F.constant] at hh
    exact congrArg (fun f : LocallyConstant Y.left _ ↦ f (IsLocalRing.closedPoint k)) hh
  rw [hn, hm, hinj.eq_iff, I.labelEquiv.injective.eq_iff]

/-- Match the representatives for two normalizer presentations of the same torus. -/
private theorem align_representatives (I : Identification D) (J : Identification D')
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X))
    (hn : ∀ w, IsRepresentative I w (n w))
    (hJ : ∀ w, ∃ m, IsRepresentative J w m) :
    ∃ (e : D.rootDatum.weylGroup ≃ D'.rootDatum.weylGroup)
      (m : D'.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ J.normalizer.group.X)),
      (∀ w, IsRepresentative J w (m w)) ∧
      ∀ w, m (e w) ≫ J.normalizer.inclusion.hom.hom = n w ≫ I.normalizer.inclusion.hom.hom := by
  classical
  let pt := 𝟙_ (SchemeOver k)
  have hLift (w : D.rootDatum.weylGroup) :
      ∃ q : pt ⟶ J.normalizer.group.X,
        q ≫ J.normalizer.inclusion.hom.hom = n w ≫ I.normalizer.inclusion.hom.hom :=
    (J.representsNormalizer _ _).mp ((I.representsNormalizer _ _).mpr ⟨n w, rfl⟩)
  choose q hq using hLift
  choose e he using fun w ↦ some_representative_label J (q w)
  have hcompare (p p' : pt ⟶ I.normalizer.group.X) (r r' : pt ⟶ J.normalizer.group.X)
      (h : r ≫ J.normalizer.inclusion.hom.hom = p ≫ I.normalizer.inclusion.hom.hom)
      (h' : r' ≫ J.normalizer.inclusion.hom.hom = p' ≫ I.normalizer.inclusion.hom.hom) :
      p ≫ I.quotient.hom.hom = p' ≫ I.quotient.hom.hom ↔
        r ≫ J.quotient.hom.hom = r' ≫ J.quotient.hom.hom := by
    rw [quotient_eq_iff_torus I, quotient_eq_iff_torus J, h, h']
  have hinj : Function.Injective e := by
    intro v w hvw
    exact (labels_eq_iff_quotient_eq I (hn v) (hn w)).mp
      ((hcompare _ _ _ _ (hq v) (hq w)).mpr
        ((labels_eq_iff_quotient_eq J (he v) (he w)).mpr hvw))
  have hsurj : Function.Surjective e := by
    intro w
    obtain ⟨r, hr⟩ := hJ w
    obtain ⟨p, hp⟩ :=
      (I.representsNormalizer _ (r ≫ J.normalizer.inclusion.hom.hom)).mp
        ((J.representsNormalizer _ _).mpr ⟨r, rfl⟩)
    obtain ⟨v, hv⟩ := some_representative_label I p
    refine ⟨v, (labels_eq_iff_quotient_eq J (he v) hr).mp ?_⟩
    exact (hcompare _ _ _ _ (hq v) hp.symm).mp
      ((labels_eq_iff_quotient_eq I (hn v) hv).mpr rfl)
  let E := Equiv.ofBijective e ⟨hinj, hsurj⟩
  refine ⟨E, fun w ↦ q (E.symm w), ?_, ?_⟩
  · intro w
    have hh : e (E.symm w) = w := E.apply_symm_apply w
    exact (congrArg (fun v ↦ IsRepresentative J v (q (E.symm w))) hh) ▸ he (E.symm w)
  · intro w
    change q (E.symm (E w)) ≫ J.normalizer.inclusion.hom.hom = n w ≫ I.normalizer.inclusion.hom.hom
    rw [E.symm_apply_apply]
    exact hq w

private theorem identityRepresentative {B : ClosedSubgroup G.val}
    (I : Identification D) (hTB : Specs.SchemeDerivedGroup.IsSubgroupOf T B)
    {n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X} (hn : IsRepresentative I 1 n) :
    n ≫ I.normalizer.inclusion.hom.hom ∈ SubgroupSections B (𝟙_ (SchemeOver k)) := by
  have h : (1 : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) ≫ I.quotient.hom.hom =
      n ≫ I.quotient.hom.hom := by
    rw [hn, map_one, map_one, MonObj.one_comp]
  have ht := normalizer_ratio_mem_torus I h
  rw [MonObj.one_comp, inv_one, one_mul] at ht
  change ∃ t : 𝟙_ (SchemeOver k) ⟶ T.group.X,
    t ≫ T.inclusion.hom.hom = n ≫ I.normalizer.inclusion.hom.hom at ht
  obtain ⟨t, ht⟩ := ht
  obtain ⟨j, hj⟩ := hTB
  refine ⟨t ≫ j.hom.hom, ?_⟩
  change (t ≫ j.hom.hom) ≫ B.inclusion.hom.hom = n ≫ I.normalizer.inclusion.hom.hom
  rw [Category.assoc, show j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom from
    congrArg (Grp.forget (SchemeOver k)).map hj, ht]

private def relabelCell {B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {n n' : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (h : n = n') (C : Cell (T := T) Q a n A) : Cell (T := T) Q a n' A :=
  h ▸ C

omit [IsCommMonObj T.group.X] in
private theorem relabelCell_range {B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {n n' : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (h : n = n') (C : Cell (T := T) Q a n A) :
    Set.range (relabelCell h C).orbitInclusion.left = Set.range C.orbitInclusion.left := by
  subst n'
  rfl

end Representatives

section RankOne

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open private closed_factor_of_range from LinearAlgebraicGroups.Flag.SimpleParabolicProduct
open private projection_eq_iff basePoint_closed from LinearAlgebraicGroups.Flag.QuotientEmbedding

/-- A section that lies in the closed subgroup on underlying points factors through it. -/
private theorem point_mem_closed_range_iff {K : Type u} [Field K] [Algebra k K]
    {Y Z : SchemeOver k} (p : Over.mk (fieldSpecMap k K) ⟶ Y) (i : Z ⟶ Y)
    (hi : IsClosedImmersion i.left) :
    p.left (IsLocalRing.closedPoint K) ∈ Set.range i.left ↔ ∃ t, t ≫ i = p := by
  constructor
  · intro hp
    let : IsReduced (Over.mk (fieldSpecMap k K)).left :=
      inferInstanceAs (IsReduced (Spec (CommRingCat.of K)))
    exact closed_factor_of_range p i hi (by
      rintro _ ⟨x, rfl⟩
      change PrimeSpectrum K at x
      rwa [Subsingleton.elim x (IsLocalRing.closedPoint K)])
  · rintro ⟨t, ht⟩
    exact ⟨t.left (IsLocalRing.closedPoint K),
      comp_apply_eq ht (IsLocalRing.closedPoint K)⟩

/-- The subgroup is the fiber of the quotient over the identity coset. -/
private theorem range_subgroup {M : GroupScheme k} (H : ClosedSubgroup M) (Q : Presentation H) :
    Set.range H.inclusion.hom.hom.left = Q.projection.left ⁻¹'
      Set.range (((1 : 𝟙_ (SchemeOver k) ⟶ M.X) ≫ Q.projection).left) := by
  let x := (1 : 𝟙_ (SchemeOver k) ⟶ M.X) ≫ Q.projection
  have identify {Y : SchemeOver k} (a : Y ⟶ M.X) :
      a ≫ Q.projection = toUnit Y ≫ x ↔ a ∈ SubgroupSections H Y := by
    rw [show toUnit Y ≫ x = (1 : Y ⟶ M.X) ≫ Q.projection by
      dsimp only [x]
      rw [← Category.assoc, MonObj.comp_one], eq_comm, projection_eq_iff Q, inv_one, one_mul]
  let : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  let : Mono H.inclusion.hom.hom := Over.mono_of_mono_left _
  apply range_inverseImage (j := toUnit H.group.X)
  refine IsPullback.mk' ((identify _).2 ?_) ?_ ?_
  · exact ⟨𝟙 _, by change 𝟙 _ ≫ H.inclusion.hom.hom = _; simp⟩
  · intro _ _ _ he _
    exact (cancel_mono H.inclusion.hom.hom).1 he
  · intro Y a b h
    have hmem := (identify a).1 (h.trans (congrArg (· ≫ x) (Subsingleton.elim b _)))
    change ∃ t : Y ⟶ H.group.X, t ≫ H.inclusion.hom.hom = a at hmem
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht, Subsingleton.elim _ _⟩

private theorem mem_subgroup_iff {B P : ClosedSubgroup G.val}
    (j : B.group ⟶ P.group) (hj : j ≫ P.inclusion = B.inclusion)
    {Y : SchemeOver k} (p : Y ⟶ P.group.X) :
    p ≫ P.inclusion.hom.hom ∈ SubgroupSections B Y ↔ ∃ t, t ≫ j.hom.hom = p := by
  let : IsClosedImmersion P.inclusion.hom.hom.left := P.isClosedImmersion
  let : Mono P.inclusion.hom.hom := Over.mono_of_mono_left _
  have hj' : j.hom.hom ≫ P.inclusion.hom.hom = B.inclusion.hom.hom :=
    congrArg (fun f : B.group ⟶ G.val ↦ f.hom.hom) hj
  change (∃ t : Y ⟶ B.group.X, t ≫ B.inclusion.hom.hom = p ≫ P.inclusion.hom.hom) ↔ _
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, (cancel_mono P.inclusion.hom.hom).1 ?_⟩
    rwa [Category.assoc, hj']
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [Category.assoc, hj']⟩

private theorem sectionsIn_cell {T B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) (Y : SchemeOver k) :
    sectionsIn Y C.doubleOrbitInclusion = doubleCoset B Y n := by
  ext x
  change (∃ c, c ≫ C.doubleOrbitInclusion = x) ↔ x ∈ doubleCoset B Y n
  rw [C.doubleOrbitSections]
  constructor
  · rintro ⟨b₁, b₂, rfl⟩
    exact Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr ⟨_, ⟨b₁, rfl⟩, _, rfl, rfl⟩,
      _, ⟨b₂, rfl⟩, rfl⟩
  · intro hx
    obtain ⟨_, hy, _, ⟨b₂, rfl⟩, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨_, ⟨b₁, rfl⟩, _, hn, rfl⟩ := Set.mem_mul.mp hy
    obtain rfl := Set.mem_singleton_iff.mp hn
    exact ⟨b₁, b₂, rfl⟩

private theorem simplified_doubleCoset {B : ClosedSubgroup G.val}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (hn : n ∈ SubgroupSections B (𝟙_ (SchemeOver k))) (Y : SchemeOver k) :
    doubleCoset B Y n = SubgroupSections B Y := by
  have hu : toUnit Y ≫ n ∈ SubgroupSections B Y := by
    change ∃ t : 𝟙_ (SchemeOver k) ⟶ B.group.X, t ≫ B.inclusion.hom.hom = n at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨toUnit Y ≫ t, ?_⟩
    change (toUnit Y ≫ t) ≫ B.inclusion.hom.hom = toUnit Y ≫ n
    rw [Category.assoc, ht]
  unfold doubleCoset
  ext x
  constructor
  · intro h
    obtain ⟨_, hy, z, hz, rfl⟩ := Set.mem_mul.mp h
    obtain ⟨w, hw, _, hu', rfl⟩ := Set.mem_mul.mp hy
    obtain rfl := Set.mem_singleton_iff.mp hu'
    exact (SubgroupSections B Y).mul_mem ((SubgroupSections B Y).mul_mem hw hu) hz
  · intro hx
    exact Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr
      ⟨_, (SubgroupSections B Y).one_mem, _, rfl, rfl⟩,
      (toUnit Y ≫ n)⁻¹ * x, (SubgroupSections B Y).mul_mem ((SubgroupSections B Y).inv_mem hu) hx,
      by rw [one_mul, mul_inv_cancel_left]⟩

private theorem identity_cell_closed {T B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) (hn : n ∈ SubgroupSections B (𝟙_ (SchemeOver k))) :
    IsClosed (Set.range C.orbitInclusion.left) := by
  have hs (Y : SchemeOver k) : sectionsIn Y C.doubleOrbitInclusion =
      sectionsIn Y B.inclusion.hom.hom :=
    (sectionsIn_cell C Y).trans (simplified_doubleCoset hn Y)
  have eq : Set.range C.doubleOrbitInclusion.left = Set.range B.inclusion.hom.hom.left := by
    obtain ⟨t, ht⟩ : C.doubleOrbitInclusion ∈ sectionsIn C.doubleOrbit B.inclusion.hom.hom := by
      rw [← hs]
      exact ⟨𝟙 _, Category.id_comp _⟩
    obtain ⟨z, hz⟩ : B.inclusion.hom.hom ∈ sectionsIn B.group.X C.doubleOrbitInclusion := by
      rw [hs]
      exact ⟨𝟙 _, Category.id_comp _⟩
    exact Set.Subset.antisymm
      (fun _ ⟨x, hx⟩ ↦ ⟨t.left x, (comp_apply_eq ht x).trans hx⟩)
      (fun _ ⟨x, hx⟩ ↦ ⟨z.left x, (comp_apply_eq hz x).trans hx⟩)
  have h := (range_inverseImage C.isInverseImage).symm.trans (eq.trans (range_subgroup B Q))
  have he := (Set.preimage_injective.mpr Q.surjective.1) h
  rw [he]
  let : IsClosedImmersion (((1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ Q.projection).left) :=
    basePoint_closed Q.quasiProjective _
  exact (((1 : 𝟙_ (SchemeOver k) ⟶ G.val.X) ≫ Q.projection).left).isClosedEmbedding.isClosed_range

/-- The complement of the closed identity fiber is dense in the rank-one parabolic. -/
private theorem dense_rankOne_bigCell {B P : ClosedSubgroup G.val}
    (j : B.group ⟶ P.group) (hj : IsClosedImmersion j.hom.hom.left)
    (S : Presentation (⟨B.group, j, hj⟩ : ClosedSubgroup P.group))
    (e : S.scheme ≅ Specs.RankOneFlag.projectiveLine k)
    (hne : (Set.range j.hom.hom.left)ᶜ.Nonempty) : Dense (Set.range j.hom.hom.left)ᶜ := by
  let x := (1 : 𝟙_ (SchemeOver k) ⟶ P.group.X) ≫ S.projection
  let e' : S.scheme.left ≅ (Specs.RankOneFlag.projectiveLine k).left := (Over.forget _).mapIso e
  let f := e'.hom.homeomorph
  have hnonempty : Nonempty (Specs.RankOneFlag.projectiveLine k).left :=
    ⟨f (x.left (IsLocalRing.closedPoint k))⟩
  let : IrreducibleSpace S.scheme.left := f.irreducibleSpace_iff.mpr
    (projectiveSpaceIrreducible hnonempty)
  have heq : Set.range j.hom.hom.left = S.projection.left ⁻¹' Set.range x.left :=
    range_subgroup (⟨B.group, j, hj⟩ : ClosedSubgroup P.group) S
  have hne' : (Set.range x.left)ᶜ.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    rw [heq] at hy
    exact ⟨S.projection.left y, hy⟩
  let : IsClosedImmersion x.left := basePoint_closed S.quasiProjective x
  have hd := x.left.isClosedEmbedding.isClosed_range.isOpen_compl.dense hne'
  rw [dense_iff_closure_eq, heq, ← Set.preimage_compl, ← (quotient_isOpen S).preimage_closure_eq_closure_preimage
    S.projection.left.continuous, hd.closure_eq, Set.preimage_univ]

private theorem nonempty_rankOne_bigCell {B P : ClosedSubgroup G.val}
    (j : B.group ⟶ P.group) (hj : IsClosedImmersion j.hom.hom.left)
    (hj' : j ≫ P.inclusion = B.inclusion)
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      let Y := Over.mk (fieldSpecMap k K)
      (SubgroupSections P Y : Set (Y ⟶ G.val.X)) =
        (SubgroupSections B Y : Set (Y ⟶ G.val.X)) ∪ doubleCoset B Y n ∧
        Disjoint (SubgroupSections B Y : Set (Y ⟶ G.val.X)) (doubleCoset B Y n)) :
    (Set.range j.hom.hom.left)ᶜ.Nonempty := by
  let K := AlgebraicClosure k
  let Y := Over.mk (fieldSpecMap k K)
  obtain ⟨hP, hdis⟩ := h K
  have hx : toUnit Y ≫ n ∈ doubleCoset B Y n := by
    unfold doubleCoset
    have h₁ : (1 : Y ⟶ G.val.X) ∈ SubgroupSections B Y := (SubgroupSections B Y).one_mem
    exact Set.mem_mul.mpr ⟨_, Set.mem_mul.mpr ⟨_, h₁, _, rfl, rfl⟩, _, h₁, by simp⟩
  have hy : toUnit Y ≫ n ∈ SubgroupSections P Y := by
    change toUnit Y ≫ n ∈ (SubgroupSections P Y : Set (Y ⟶ G.val.X))
    rw [hP]
    exact Or.inr hx
  change ∃ p : Y ⟶ P.group.X, p ≫ P.inclusion.hom.hom = toUnit Y ≫ n at hy
  obtain ⟨p, hp⟩ := hy
  refine ⟨p.left (IsLocalRing.closedPoint K), fun hmem ↦ ?_⟩
  have hz := (mem_subgroup_iff j hj' p).2 ((point_mem_closed_range_iff p j.hom.hom hj).1 hmem)
  rw [hp] at hz
  exact Set.disjoint_left.mp hdis hz hx

private theorem closure_mul_rankOne {B P : ClosedSubgroup G.val} {X Z : SchemeOver k}
    (i : X ⟶ G.val.X) (i' : Z ⟶ G.val.X)
    (j : B.group ⟶ P.group) (hj : IsClosedImmersion j.hom.hom.left)
    (hj' : j ≫ P.inclusion = B.inclusion)
    (hd : Dense (Set.range j.hom.hom.left)ᶜ)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      let Y := Over.mk (fieldSpecMap k K)
      ∀ p : Y ⟶ P.group.X, p ≫ P.inclusion.hom.hom ∉ SubgroupSections B Y →
        sectionsIn Y i * {p ≫ P.inclusion.hom.hom} ⊆ sectionsIn Y i')
    (hr : Set.range i'.left ⊆ Set.range (multiplyInto P i).left) :
    closure (Set.range (multiplyInto P i).left) = closure (Set.range i'.left) := by
  let V := (snd X P.group.X).left ⁻¹' (Set.range j.hom.hom.left)ᶜ
  have hV : closure V = Set.univ := by
    dsimp only [V]
    rw [← (snd_isOpen X P.group.X).preimage_closure_eq_closure_preimage
      (snd X P.group.X).left.continuous, hd.closure_eq, Set.preimage_univ]
  have hsub : (multiplyInto P i).left '' V ⊆ Set.range i'.left := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨K, _, _, _, p, hp⟩ := geometric_point_at (X ⊗ P.group.X) y
    let t := p ≫ snd X P.group.X
    have ht : t ≫ P.inclusion.hom.hom ∉ SubgroupSections B _ := by
      intro ht
      have hy' : t.left (IsLocalRing.closedPoint K) ∈ Set.range j.hom.hom.left :=
        (point_mem_closed_range_iff t j.hom.hom hj).2 ((mem_subgroup_iff j hj' t).1 ht)
      change (snd X P.group.X).left (p.left (IsLocalRing.closedPoint K)) ∈ _ at hy'
      exact hy (hp ▸ hy')
    have hmul : p ≫ multiplyInto P i ∈ sectionsIn _ i * {t ≫ P.inclusion.hom.hom} := by
      rw [comp_multiplyInto]
      exact Set.mem_mul.mpr ⟨_, ⟨p ≫ fst X P.group.X, rfl⟩, _, rfl, rfl⟩
    obtain ⟨f, hf⟩ := h K t ht hmul
    refine ⟨f.left (IsLocalRing.closedPoint K), ?_⟩
    exact (comp_apply_eq hf (IsLocalRing.closedPoint K)).trans
      (congrArg (multiplyInto P i).left hp)
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono hr)
  rw [← Set.image_univ, ← hV]
  exact (image_closure_subset_closure_image (multiplyInto P i).left.continuous).trans
    (closure_mono hsub)

end RankOne

section Closures

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive)
open Specs.SchemeDerivedGroup (IsSubgroupOf)

open private kBorel_smooth_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private exists_shortest_word from LinearAlgebraicGroups.RootData.SimpleRoots
open private hasGallerySubwords from LinearAlgebraicGroups.Flag.GallerySubwords

private theorem flagQuotientProper (hG : IsReductive G) {B : ClosedSubgroup G.val}
    (hB : IsKBorel B) (Q : Presentation B) : IsProper Q.scheme.hom := by
  let : GeometricallyConnected G.val.X.hom := hG.2.1
  have hGc : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.val.X.hom)
  have hBs := (kBorel_smooth_connected G B hB).1
  apply (LinearAlgebraicGroups.BorelProper.quotientProperIff G hG.1 hGc B hBs Q).2
  obtain ⟨h, hB'⟩ := hB
  exact ⟨h, _, hB', 𝟙 _, Category.id_comp _⟩

private theorem preimage_saturation {M : GroupScheme k} {B P : ClosedSubgroup M}
    (Q : Presentation B) (R : Presentation P) (p : Q.scheme ⟶ R.scheme)
    (hp : Q.projection ≫ p = R.projection) {X : SchemeOver k} (i : X ⟶ M.X)
    (F : Set Q.scheme.left) (hF : Set.range i.left = Q.projection.left ⁻¹' F) :
    Q.projection.left ⁻¹' saturation p.left F = Set.range (multiplyInto P i).left := by
  have hcomp : (R.projection.left : M.X.left → R.scheme.left) = p.left ∘ Q.projection.left :=
    (congrArg (fun f : M.X ⟶ R.scheme ↦ (f.left : M.X.left → R.scheme.left)) hp).symm
  have himage := Q.surjective.1.image_preimage F
  rw [← hF] at himage
  have he : p.left '' F = R.projection.left '' Set.range i.left := by
    rw [← himage, Set.image_image, hcomp]
    rfl
  unfold saturation
  rw [he, ← Set.preimage_comp, ← hcomp, range_multiplyInto]

/-- Transfer the rank-one saturation calculation through the full flag projection. -/
private theorem cell_closure_step {M : GroupScheme k} {B P : ClosedSubgroup M}
    (Q : Presentation B) (R : Presentation P) (p : Q.scheme ⟶ R.scheme)
    (hp : Q.projection ≫ p = R.projection) (hopen : IsOpenMap p.left) (hclosed : IsClosedMap p.left)
    {X X' : SchemeOver k} (i : X ⟶ M.X) (i' : X' ⟶ M.X)
    (F F' : Set Q.scheme.left) (hF : Set.range i.left = Q.projection.left ⁻¹' F)
    (hF' : Set.range i'.left = Q.projection.left ⁻¹' F')
    (hprod : Set.range (multiplyInto P i).left = Set.range i.left ∪ Set.range i'.left) :
    saturation p.left F = F ∪ F' ∧
    (closure (Set.range (multiplyInto P i).left) = closure (Set.range i'.left) →
      closure F' = saturation p.left (closure F)) := by
  have hsat := preimage_saturation Q R p hp i F hF
  have hq := (quotient_isOpen Q).preimage_closure_eq_closure_preimage Q.projection.left.continuous
  have hinj := Set.preimage_injective.mpr Q.surjective.1
  constructor
  · apply hinj
    rw [hsat, hprod, Set.preimage_union, ← hF, ← hF']
  · intro h
    apply hinj
    rw [← closure_saturation p.left.continuous hopen hclosed, hq F', hq (saturation p.left F),
      hsat, ← hF', h]

/-- Schubert closure formulas conditional on the split Bruhat stratification. -/
theorem schubertClosures_conditional (bruhatCells : Specs.BruhatCells.Statement.{u}) :
    Specs.SchubertClosures.Statement.{u} := by
  classical
  intro k _ G hG T B hT hTm hB hTB
  obtain ⟨hcomm, D, I, _, c, b, hc, hpos, hb, hrep, hpar⟩ :=
    SimpleParabolicProduct.simpleParabolicProduct G hG T B hT hTm hB hTB
  let : IsCommMonObj T.group.X := hcomm
  let : Finite (Root T) := D.finiteRoots
  let : D.rootDatum.IsReduced := D.reduced
  obtain ⟨_, D', I', _, _, _, _, _, _, hBruhat⟩ := bruhatCells G hG T B hT hTm hB hTB
  obtain ⟨_, _, _, _, _, _, _, _, hrep', hQ, hBruhat⟩ := hBruhat
  refine ⟨hcomm, D, I, c, b, hc, hpos, hb, hrep, hQ, ?_⟩
  intro Q
  obtain ⟨a, ha, hall⟩ := hBruhat Q
  refine ⟨a, ha, ?_⟩
  intro n hn
  dsimp only
  obtain ⟨e, n', hn', he⟩ := align_representatives I I' n hn hrep'
  obtain ⟨A', C', _, hdis', _, _⟩ := hall n' hn'
  let g := fun w ↦ n w ≫ I.normalizer.inclusion.hom.hom
  let A := fun w ↦ A' (e w)
  let C : ∀ w, Cell (T := T) Q a (g w) (A w) := fun w ↦ relabelCell (he w) (C' (e w))
  let F := fun w ↦ Set.range (C w).orbitInclusion.left
  let E := fun w ↦ Set.range (C w).doubleOrbitInclusion.left
  have hdis (v w) (hvw : v ≠ w) : Disjoint (F v) (F w) := by
    dsimp only [F, C]
    rw [relabelCell_range, relabelCell_range]
    exact (hdis' _ _ (fun h ↦ hvw (e.injective h))).1
  have hne (w) : (F w).Nonempty := by
    let b₀ := (1 : 𝟙_ (SchemeOver k) ⟶ B.group.X).left (IsLocalRing.closedPoint k)
    exact ⟨(C w).orbitInclusion.left ((C w).projection.left b₀), ⟨_, rfl⟩⟩
  have hE (w) : E w = Q.projection.left ⁻¹' F w :=
    range_inverseImage (C w).isInverseImage
  have hbase : IsClosed (F 1) := identity_cell_closed (C 1) (identityRepresentative I hTB (hn 1))
  have heval (i : Root T) : evaluate D c (D.rootDatum.root i) =
      Specs.CharacterPairing.pairing T.group i.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  have hpositive (i : Root T) : b.IsPos i → i ∈ subgroupRoots T B := by
    intro hi
    rw [← hpos]
    change 0 < Specs.CharacterPairing.pairing T.group i.val c
    rw [← heval]
    exact (hb.positive_iff i).1 hi
  have hQproper := flagQuotientProper hG hB Q
  have hstep (s : b.support) : ∃ S : Set Q.scheme.left → Set Q.scheme.left,
      (∀ v, S (F v) = F v ∪ F (v * RootPairing.weylGroup.ofIdx D.rootDatum s.val)) ∧
      (∀ v, b.IsPos (D.rootDatum.weylGroupToPerm v s.val) →
        closure (F (v * RootPairing.weylGroup.ofIdx D.rootDatum s.val)) = S (closure (F v))) ∧
      (∀ J : Set D.rootDatum.weylGroup, S (⋃ v ∈ J, F v) = ⋃ v ∈ J, S (F v)) := by
    let σ := RootPairing.weylGroup.ofIdx D.rootDatum s.val
    obtain ⟨_, L, _, _, _, _, _, j, _, _, hj, _, hj', _, _, ⟨S⟩, ⟨S'⟩, heS, products⟩ :=
      hpar s.val s.property
    let P := L.parabolic
    obtain ⟨f, _, ⟨f'⟩⟩ := heS S S'
    obtain ⟨R⟩ := (HomogeneousQuotient.homogeneousQuotient k G P).1
    obtain ⟨p, hp, hopen, hclosed⟩ := quotient_map_geometry Q R ⟨j, hj'⟩ hQproper
    have hRank := products n hn
    have hnonempty : (Set.range j.hom.hom.left)ᶜ.Nonempty :=
      nonempty_rankOne_bigCell j hj hj' (n := g σ) (fun K ↦ ⟨(hRank K).1, (hRank K).2.1⟩)
    have hd := dense_rankOne_bigCell j hj S (f ≪≫ f') hnonempty
    have hm (v : D.rootDatum.weylGroup) :
        Set.range (multiplyInto P (C v).doubleOrbitInclusion).left = E v ∪ E (v * σ) := by
      apply range_mul_bruhat
      intro K _ _ _
      dsimp only
      simp only [sectionsIn_cell]
      exact ((hRank K).2.2.2 v).1
    have hgeom (v : D.rootDatum.weylGroup) (hposv : b.IsPos (D.rootDatum.weylGroupToPerm v s.val)) :
        closure (Set.range (multiplyInto P (C v).doubleOrbitInclusion).left) =
          closure (E (v * σ)) := by
      apply closure_mul_rankOne (B := B) _ _ j hj hj' hd
      · intro K _ _ _
        dsimp only
        intro t ht
        simp only [sectionsIn_cell]
        let Y := Over.mk (fieldSpecMap k K)
        have htP : t ≫ L.parabolic.inclusion.hom.hom ∈
            (SubgroupSections L.parabolic Y : Set (Y ⟶ G.val.X)) := ⟨t, rfl⟩
        rw [(hRank K).1] at htP
        have hc := htP.resolve_left ht
        calc
          _ ⊆ doubleCoset B Y (g v) * doubleCoset B Y (g σ) :=
            Set.mul_subset_mul_left (Set.singleton_subset_iff.mpr hc)
          _ = _ := ((hRank K).2.2.2 v).2 (hpositive _ hposv)
      · rw [hm]
        exact Set.subset_union_right
    have step (v : D.rootDatum.weylGroup) :=
      cell_closure_step Q R p hp hopen hclosed _ _ (F v) (F (v * σ)) (hE _) (hE _) (hm v)
    exact ⟨saturation p.left, fun v ↦ (step v).1, fun v hv ↦ (step v).2 (hgeom v hv),
      saturation_iUnion p.left F⟩
  have hclosure (l : List b.support) (hl : IsReduced D.rootDatum b l) :
      closure (F (wordProduct D.rootDatum b l)) = ⋃ v ∈ subwordProducts D.rootDatum b l, F v :=
    closure_subword_union D.rootDatum b F hbase hstep l hl
  have hmem (l : List b.support) (hl : IsReduced D.rootDatum b l) (v : D.rootDatum.weylGroup) :=
    closure_support_of_partition F hne hdis (hclosure l hl) v
  have horder (v w : D.rootDatum.weylGroup) : SubwordLE D.rootDatum b v w ↔ F v ⊆ closure (F w) := by
    constructor
    · rintro ⟨l, hl, rfl, hv⟩
      exact (hmem l hl v).1 hv
    · intro hv
      obtain ⟨l, hw, hmin, _⟩ := exists_shortest_word D.rootDatum b hb.generates w
      have hl : IsReduced D.rootDatum b l := by
        change wordLength D.rootDatum b (wordProduct D.rootDatum b l) = l.length
        rw [hw, hmin]
      exact ⟨l, hl, hw, (hmem l hl v).2 (hw.symm ▸ hv)⟩
  have hregular (i : Root T) : evaluate D c (D.rootDatum.root i) ≠ 0 := by
    rw [heval]
    exact hc i
  have hgallery := hasGallerySubwords D.rootDatum b hb hregular
  refine ⟨A, C, (fun w ↦ ⟨vanishingSubschemeReduced _, vanishingSubschemeReduced _⟩), horder, ?_⟩
  intro l hl
  refine ⟨fun v ↦ ⟨(hmem l hl v).trans (horder v _).symm, hgallery.subword_iff l v⟩, ?_, ?_⟩
  · exact (range_closureIdeal _).trans (hclosure l hl)
  · rw [range_closureIdeal]
    change closure (E (wordProduct D.rootDatum b l)) = ⋃ v ∈ subwordProducts D.rootDatum b l, E v
    rw [hE, ← (quotient_isOpen Q).preimage_closure_eq_closure_preimage Q.projection.left.continuous,
      hclosure l hl]
    simp only [hE, Set.preimage_iUnion]

end Closures

end

end LinearAlgebraicGroups.Flag.SchubertClosures

universe v8_closure_80674f2e85506d92_u0
theorem _root_.«LinearAlgebraicGroups».«Flag».«SchubertClosures».«schubertClosures» : _root_.«LinearAlgebraicGroups».«Specs».«SchubertClosures».«Statement».{v8_closure_80674f2e85506d92_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«SchubertClosures».«schubertClosures_conditional».{v8_closure_80674f2e85506d92_u0} (@_root_.«LinearAlgebraicGroups».«Flag».«BruhatCells».«bruhatCells».{v8_closure_80674f2e85506d92_u0})
