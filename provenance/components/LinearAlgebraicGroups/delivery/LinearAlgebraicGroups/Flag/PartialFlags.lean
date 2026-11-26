import Specs.LinearAlgebraicGroups.Flag.PartialFlags
import LinearAlgebraicGroups.Flag.ProjectiveFlags
import LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Flag.ParabolicCosetLength
import LinearAlgebraicGroups.Flag.SchubertClosures
import Batteries.Tactic.OpenPrivate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise

universe u

namespace LinearAlgebraicGroups.Flag.PartialFlags

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.BruhatOrbitParametrization (Cell IsRepresentative OrderedParametrization conjugatePoint)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.ParabolicCosetLength (IsShortestInCoset)
open Specs.PartialFlags (IsMinimal)
open Specs.QuotientEmbedding (Presentation)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.SchubertClosures (SubwordLE subwordProducts closureIdeal)
open Specs.SimpleRoots (IsBaseFor evaluate wordLength wordProduct)
open Specs.StandardParabolicLevi (StandardParabolic parabolicWeylGroup leviRoots)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open Specs.GallerySubwords (IsReduced)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

open private normalizerLabel normalizer_isRepresentative evaluate_root
  from LinearAlgebraicGroups.Flag.BruhatCells
open private representativeConjugation monoSubgroup from
  LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

private theorem transferRepresentative {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (W : Identification D) (V : Identification E)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hn : IsRepresentative W w n) :
    ∃ (v : E.rootDatum.weylGroup) (m : 𝟙_ (SchemeOver k) ⟶ V.normalizer.group.X),
      IsRepresentative V v m ∧
      m ≫ V.normalizer.inclusion.hom.hom = n ≫ W.normalizer.inclusion.hom.hom ∧
      v.val.weightEquiv = w.val.weightEquiv := by
  have hN := (W.representsNormalizer _ _).mpr ⟨n, rfl⟩
  obtain ⟨m, hm⟩ := (V.representsNormalizer _ _).mp hN
  let v := normalizerLabel V m
  have hv : IsRepresentative V v m := normalizer_isRepresentative V m
  refine ⟨v, m, hv, hm, ?_⟩
  let e := V.image.conjugation (V.labelEquiv v)
  let f := W.image.conjugation (W.labelEquiv w)
  have hef : e = f := by
    apply Iso.ext
    apply Grp.hom_ext
    letI := monoSubgroup T
    apply (cancel_mono T.inclusion.hom.hom).mp
    change (e.hom ≫ T.inclusion).hom.hom = (f.hom ≫ T.inclusion).hom.hom
    rw [representativeConjugation V hv, representativeConjugation W hn, hm]
  apply LinearEquiv.ext
  intro x
  change v.val.weightEquiv (Additive.ofMul (Additive.toMul x)) =
    w.val.weightEquiv (Additive.ofMul (Additive.toMul x))
  rw [V.characterAction, W.characterAction, V.image.characterAction, W.image.characterAction]
  exact congrArg (fun j : T.group ≅ T.group ↦ Additive.ofMul (j.inv ≫ Additive.toMul x)) hef

private theorem transferRepresentative_sameDatum {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (W V : Identification D)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hn : IsRepresentative W w n) :
    ∃ m : 𝟙_ (SchemeOver k) ⟶ V.normalizer.group.X,
      IsRepresentative V w m ∧
      m ≫ V.normalizer.inclusion.hom.hom = n ≫ W.normalizer.inclusion.hom.hom := by
  obtain ⟨v, m, hv, hm, he⟩ := transferRepresentative W V hn
  have h : v = w := Subtype.ext (RootPairing.Equiv.weightHom_injective _ he)
  exact ⟨m, h ▸ hv, hm⟩

private theorem rootPairing_ext {Idx X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    {P Q : RootDatum Idx X Y}
    (hPair : P.toLinearMap = Q.toLinearMap) (hRoot : P.root = Q.root)
    (hCoroot : P.coroot = Q.coroot) (hPerm : P.reflectionPerm = Q.reflectionPerm) : P = Q := by
  cases P
  cases Q
  congr

private theorem datum_ext {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (h : D.rootDatum = E.rootDatum) : D = E := by
  cases D
  cases E
  congr

/-- The product of two candidate reflections at the same root is a shear along
that root. It belongs to the finite normalizer action on the character lattice,
so the shear is trivial. Perfectness then gives equality of the coroots. -/
private theorem rootDatum_eq_of_identifications {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D E : Datum T} (W : Identification D) (V : Identification E)
    (hV : ∀ w, ∃ n, IsRepresentative V w n) :
    D = E := by
  letI := D.freeCharacters
  letI := W.image.finite
  letI : Finite D.rootDatum.weylGroup := Finite.of_injective W.labelEquiv W.labelEquiv.injective
  let P := D.rootDatum
  let Q := E.rootDatum
  have hRoot (i : Root T) : P.root i = Q.root i := (D.root_eq i).trans (E.root_eq i).symm
  have hPair : P.toLinearMap = Q.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact (D.pairing_eq (Additive.toMul x) (Additive.toMul y)).trans
      (E.pairing_eq (Additive.toMul x) (Additive.toMul y)).symm
  have hRefl (i : Root T) : P.reflection i = Q.reflection i := by
    obtain ⟨m, hm⟩ := hV (RootPairing.weylGroup.ofIdx Q i)
    obtain ⟨v, n, hn, he, hv⟩ := transferRepresentative V W hm
    change v.val.weightEquiv = (RootPairing.Equiv.reflection Q i).weightEquiv at hv
    rw [RootPairing.Equiv.reflection_weightEquiv] at hv
    let f := (RootPairing.Equiv.weightHom P).domRestrict P.weylGroup
    let s := RootPairing.weylGroup.ofIdx P i * v
    have hsf : f s = P.reflection i * Q.reflection i := by
      change f (RootPairing.weylGroup.ofIdx P i * v) = _
      rw [map_mul]
      change (RootPairing.Equiv.reflection P i).weightEquiv * v.val.weightEquiv = _
      rw [RootPairing.Equiv.reflection_weightEquiv, hv]
    let a := P.root i
    let d := P.coroot' i - Q.coroot' i
    have ha : d a = 0 := by
      change P.coroot' i (P.root i) - Q.coroot' i (P.root i) = 0
      rw [show Q.coroot' i (P.root i) = 2 by rw [hRoot i, RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same],
        RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same, sub_self]
    have hstep (x : Additive (Character T.group)) : f s x = x - d x • a := by
      rw [hsf]
      change P.reflection i (Q.reflection i x) = _
      rw [P.reflection_apply, Q.reflection_apply, ← hRoot i,
        map_sub, map_smul, RootPairing.root_coroot'_eq_pairing, RootPairing.pairing_same]
      change x - Q.coroot' i x • a - (P.coroot' i x - Q.coroot' i x • (2 : ℤ)) • a = _
      simp only [d, LinearMap.sub_apply, smul_eq_mul, mul_two, sub_smul, add_smul]
      abel
    obtain ⟨N, hN, hsN⟩ := (isOfFinOrder_of_finite s).exists_pow_eq_one
    have hp (x : Additive (Character T.group)) (r : ℕ) :
        f (s ^ r) x = x - (r : ℤ) • (d x • a) := by
      induction r with
      | zero => simp [f]
      | succ r ih =>
        rw [pow_succ', map_mul]
        change f s (f (s ^ r) x) = _
        rw [hstep, ih, map_sub, map_smul, map_smul, ha]
        simp only [smul_zero, sub_zero, Nat.cast_succ, add_smul, one_smul, sub_add_eq_sub_sub]
    have hzero (x : Additive (Character T.group)) : d x • a = 0 := by
      have hh := hp x N
      rw [hsN, map_one] at hh
      change x = x - (N : ℤ) • (d x • a) at hh
      have hh' : (N : ℤ) • (d x • a) = 0 := by
        exact sub_eq_self.mp hh.symm
      exact (smul_eq_zero.mp hh').resolve_left (by exact_mod_cast hN.ne')
    apply LinearEquiv.ext
    intro x
    rw [P.reflection_apply, Q.reflection_apply, ← hRoot i]
    have hd := hzero x
    change (P.coroot' i x - Q.coroot' i x) • a = 0 at hd
    rw [sub_smul, sub_eq_zero] at hd
    rw [hd]
  apply datum_ext
  apply rootPairing_ext hPair (Function.Embedding.ext hRoot)
  · apply Function.Embedding.ext
    intro i
    apply (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective
    apply LinearMap.ext
    intro x
    change P.toLinearMap x (P.coroot i) = P.toLinearMap x (Q.coroot i)
    have hh := LinearEquiv.congr_fun (hRefl i) x
    rw [P.reflection_apply, Q.reflection_apply, ← hRoot i, sub_right_inj] at hh
    have hzero : (P.coroot' i x - Q.coroot' i x) • P.root i = 0 := by rw [sub_smul, hh, sub_self]
    have h := sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right (P.ne_zero i))
    simpa only [RootPairing.coroot', LinearMap.flip_apply, ← hPair] using h
  · funext i
    apply Equiv.ext
    intro j
    apply P.root.injective
    rw [P.root_reflectionPerm, hRefl, hRoot (Q.reflectionPerm i j), Q.root_reflectionPerm, hRoot j]

private theorem base_eq {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}
    {c c' : Cocharacter T.group} {b b' : D.rootDatum.Base}
    (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    (hb' : IsBaseFor D.rootDatum (evaluate D c') b')
    (h : positiveRoots T c = positiveRoots T c') : b = b' := by
  have hp : SimpleRoots.positive D.rootDatum (evaluate D c) =
      SimpleRoots.positive D.rootDatum (evaluate D c') := by
    ext i
    change (0 < evaluate D c (D.rootDatum.root i)) ↔
      (0 < evaluate D c' (D.rootDatum.root i))
    rw [evaluate_root, evaluate_root]
    exact Set.ext_iff.mp h i
  have hs : b.support = b'.support := by
    ext i
    rw [hb.simple_iff, hb'.simple_iff, hp]
  cases b
  cases b'
  congr

open private exists_shortest_word word_append from LinearAlgebraicGroups.RootData.SimpleRoots

private theorem minimal_of_shortest {M : Type*} [Group M] {H : Subgroup M}
    {length : M → ℕ} {v m : M} (hm : IsShortestInCoset length H v m) :
    IsShortestInCoset length H m m := by
  refine ⟨by simp, fun x ↦ ?_⟩
  have hh := hm.2 (⟨v⁻¹ * m, hm.1⟩ * x)
  simpa only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left] using hh

private theorem subword_of_shortest {Idx X Y : Type*}
    [AddCommGroup X] [AddCommGroup Y] (P : RootDatum Idx X Y)
    (b : P.Base) {f : X →ₗ[ℤ] ℤ} (hb : IsBaseFor P f b)
    {H : Subgroup P.weylGroup} {v m : P.weylGroup}
    (hm : IsShortestInCoset (wordLength P b) H v m)
    (hadd : ∀ x : H, wordLength P b (m * x.val) = wordLength P b m + wordLength P b x.val) :
    SubwordLE P b m v := by
  let x : H := ⟨m⁻¹ * v, by
    have h := H.inv_mem hm.1
    simpa only [mul_inv_rev, inv_inv] using h⟩
  have hmx : m * x.val = v := mul_inv_cancel_left _ _
  obtain ⟨p, hp, hpLen, _⟩ := exists_shortest_word P b hb.generates m
  obtain ⟨q, hq, hqLen, _⟩ := exists_shortest_word P b hb.generates x.val
  have hprod : wordProduct P b (p ++ q) = v := by rw [word_append, hp, hq, hmx]
  refine ⟨p ++ q, ?_, hprod, p, List.sublist_append_left _ _, hp⟩
  change wordLength P b (wordProduct P b (p ++ q)) = (p ++ q).length
  rw [hprod, List.length_append, hpLen, hqLen, ← hadd, hmx]

private theorem projectedClosure {X Y W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hc : Continuous p) (hp : IsClosedMap p)
    (F : W → Set X) (le : W → W → Prop) (shortest : W → Prop) (w : W)
    (hclosure : closure (F w) = ⋃ (v : W) (_ : le v w), F v)
    (hshort : ∀ v, ∃ m, shortest m ∧ p '' F m = p '' F v ∧ le m v)
    (htrans : ∀ a b c, le a b → le b c → le a c) :
    closure (p '' F w) = ⋃ (v : {v // shortest v}) (_ : le v.val w), p '' F v.val := by
  rw [hp.closure_image_eq_of_continuous hc, hclosure]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨v, hv, hx⟩ := hx
    obtain ⟨m, hm, hmv, hle⟩ := hshort v
    exact ⟨⟨m, hm⟩, htrans m v w hle hv, hmv.symm ▸ ⟨x, hx, rfl⟩⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨v, hv, x, hx, rfl⟩
    exact ⟨x, Set.mem_iUnion.mpr ⟨v.val, Set.mem_iUnion.mpr ⟨hv, hx⟩⟩, rfl⟩

open private range_closureIdeal vanishingSubschemeReduced range_inverseImage
  from LinearAlgebraicGroups.Flag.SchubertClosures
open private quotientMapExists from LinearAlgebraicGroups.Reductive.BorelProper
open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding
open private actionOnQuotient quotientAction_mul orbitProjection_eq
  from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private quotientAction from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction

private theorem range_comp_left {X Y Z : SchemeOver k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g).left = g.left '' Set.range f.left := by
  change Set.range (g.left ∘ f.left) = _
  exact Set.range_comp g.left f.left

private theorem range_comp_surjective {X Y Z : SchemeOver k} {f : X ⟶ Y}
    (hf : Surjective f.left) (g : Y ⟶ Z) :
    Set.range (f ≫ g).left = Set.range g.left := by
  rw [range_comp_left, Set.range_eq_univ.mpr hf.1, Set.image_univ]

private theorem fullOrbitRange {T B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme}
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (C : Cell (T := T) Q a n A) :
    Set.range C.orbitInclusion.left =
      Set.range ((B.inclusion.hom.hom * (toUnit B.group.X ≫ n)) ≫ Q.projection).left := by
  rw [← range_comp_surjective C.orbitSurjective C.orbitInclusion, C.projection_eq]
  rw [← Category.assoc (toUnit _) n Q.projection, actionOnQuotient Q a ha]

private theorem doubleOrbitRange {T B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} (C : Cell (T := T) Q a n A) :
    Set.range C.doubleOrbitInclusion.left = Q.projection.left ⁻¹' Set.range C.orbitInclusion.left :=
  range_inverseImage C.isInverseImage

private theorem saturation_range {H : ClosedSubgroup G.val} (R : Presentation H)
    {Y : SchemeOver k} (i : Y ⟶ G.val.X) :
    Set.range (((fst Y H.group.X ≫ i) *
      (snd Y H.group.X ≫ H.inclusion.hom.hom))).left =
        R.projection.left ⁻¹' Set.range (i ≫ R.projection).left := by
  let m : Y ⊗ H.group.X ⟶ G.val.X :=
    (fst Y H.group.X ≫ i) * (snd Y H.group.X ≫ H.inclusion.hom.hom)
  have he : m ≫ R.projection = fst Y H.group.X ≫ (i ≫ R.projection) := by
    symm
    rw [← Category.assoc]
    apply (projection_eq_iff R _ _).mpr
    refine ⟨snd _ _, ?_⟩
    change snd _ _ ≫ H.inclusion.hom.hom = (fst _ _ ≫ i)⁻¹ * m
    simp only [m, inv_mul_cancel_left]
  have h (c : PullbackCone R.projection (i ≫ R.projection)) :
      ∃ a : c.pt ⟶ H.group.X, a ≫ H.inclusion.hom.hom = (c.snd ≫ i)⁻¹ * c.fst := by
    apply (projection_eq_iff R _ _).mp
    rw [Category.assoc, c.condition]
  choose a ha using h
  letI := monoSubgroup H
  have hp : IsPullback m (fst Y H.group.X) R.projection (i ≫ R.projection) :=
    IsPullback.of_isLimit' ⟨he⟩ (PullbackCone.IsLimit.mk he
      (fun c ↦ lift c.snd (a c)) (fun c ↦ by
        simp only [m, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, ha, mul_inv_cancel_left])
      (fun c ↦ lift_fst _ _) (fun c z hz hs ↦ by
        apply CartesianMonoidalCategory.hom_ext
        · rw [hs, lift_fst]
        · apply (cancel_mono H.inclusion.hom.hom).mp
          rw [lift_snd, ha, Category.assoc]
          have hz' : (c.snd ≫ i) * (z ≫ snd _ _ ≫ H.inclusion.hom.hom) = c.fst := by
            simpa only [m, MonObj.comp_mul, ← Category.assoc z (fst _ _) i, hs,
              Category.assoc] using hz
          rw [← hz', inv_mul_cancel_left]))
  exact range_inverseImage hp

open LinearAlgebraicGroups.CocharacterDynamics (oppositeCocharacter LimitDecomposition oppositeLimitIntersection)
open Specs.RankOneFlag (SameSubgroup)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.StandardParabolicLevi (HasFace)
open private positiveRoots_conjugate oppositeCocharacter_eq_inv translatingCocharacter
  conjugateContractingSections conjugatePoint_mul conjugatePoint_inv conjugatePoint_cancel
  existsEnumeration rootProductSubset section_mem_of_le subgroupFactorThrough memSubgroup_comp
  from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization

private theorem negative_face_pairing {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} {c faceChar : Cocharacter T.group} {b : D.rootDatum.Base} {I : Set (Root T)}
    (hc : IsRegular T c) (hpos : positiveRoots T c = subgroupRoots T B)
    (hb : IsBaseFor D.rootDatum (evaluate D c) b) (hface : HasFace b I faceChar)
    (α : Root T) (hα : α ∉ subgroupRoots T B) (hI : α ∉ leviRoots D I) :
    pairing T.group α.val faceChar < 0 := by
  let P := D.rootDatum
  let f := evaluate D c
  let g := evaluate D faceChar
  have hf (i : Root T) : f (P.root i) = pairing T.group i.val c := evaluate_root D c i
  have hg (i : Root T) : g (P.root i) = pairing T.group i.val faceChar := evaluate_root D faceChar i
  have hneg : f (P.root α) < 0 := by
    rw [hf]
    apply lt_of_le_of_ne _ (hc α)
    rw [← hpos] at hα
    exact le_of_not_gt hα
  obtain ⟨d, _, hd, hsum⟩ := hb.integral_coordinates α
  have hnonpos : ∀ j, d j ≤ 0 := by
    refine hd.resolve_left (fun hnonneg ↦ (not_le_of_gt hneg) ?_)
    rw [hsum, map_sum]
    apply Finset.sum_nonneg
    intro j hj
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg (hnonneg j) ((hb.positive_iff j).mp (b.isPos_of_mem_support hj)).le
  have hnonneg (j : Root T) (hj : j ∈ b.support) : 0 ≤ g (P.root j) := by
    rw [hg]
    by_cases h : j ∈ I
    · rw [hface.1 j h]
    · exact (hface.2 j ⟨hj, h⟩).le
  rw [← hg, hsum, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hterm (j : Root T) (hj : j ∈ b.support) : d j * g (P.root j) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hnonpos j) (hnonneg j hj)
  apply lt_of_le_of_ne (Finset.sum_nonpos hterm)
  intro hz
  apply hI
  change P.root α ∈ Submodule.span ℤ (P.root '' I)
  rw [hsum]
  apply Submodule.sum_mem
  intro j hj
  by_cases hi : j ∈ I
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hi, rfl⟩)
  · have hprod := (Finset.sum_eq_zero_iff_of_nonpos hterm).mp hz j hj
    have hgj : 0 < g (P.root j) := (hg j).symm ▸ hface.2 j ⟨hj, hi⟩
    rw [(mul_eq_zero.mp hprod).resolve_right hgj.ne', zero_smul]
    exact Submodule.zero_mem _

private theorem inversion_not_levi {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} {c : Cocharacter T.group} {b : D.rootDatum.Base} {I : Set (Root T)}
    (hpos : positiveRoots T c = subgroupRoots T B) (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    (w : D.rootDatum.weylGroup)
    (hw : Set.MapsTo (D.rootDatum.weylGroupToPerm w)
      {α | b.IsPos α ∧ α ∈ leviRoots D I} {α | b.IsPos α})
    (α : Root T) (hα : α ∉ subgroupRoots T B)
    (hβ : D.rootDatum.weylGroupToPerm w α ∈ subgroupRoots T B) :
    α ∉ leviRoots D I := by
  let P := D.rootDatum
  letI := P.indexNeg
  have hB (i : Root T) : b.IsPos i ↔ i ∈ subgroupRoots T B := by
    rw [← hpos, hb.positive_iff]
    change (0 < evaluate D c (P.root i)) ↔ (0 < pairing T.group i.val c)
    rw [evaluate_root]
  intro hI
  have hneg : b.IsPos (-α) := (RootPairing.Base.IsPos.neg_iff_not b α).mpr
    (fun hp ↦ hα ((hB α).mp hp))
  have hrootNeg (i : Root T) : P.root (-i) = -P.root i := by
    change P.root (P.reflectionPerm i i) = -P.root i
    rw [P.root_reflectionPerm, P.reflection_apply_self]
  have hspan : -α ∈ leviRoots D I := by
    change P.root (-α) ∈ Submodule.span ℤ (P.root '' I)
    rw [hrootNeg]
    exact Submodule.neg_mem _ hI
  have hwa : b.IsPos (P.weylGroupToPerm w (-α)) := hw ⟨hneg, hspan⟩
  have he : P.weylGroupToPerm w (-α) = -(P.weylGroupToPerm w α) := by
    apply P.root.injective
    change P.root (w.val.indexEquiv (-α)) = P.root (-(w.val.indexEquiv α))
    rw [← w.val.root_weightMap_apply, hrootNeg, map_neg,
      hrootNeg, ← w.val.root_weightMap_apply]
  rw [he, RootPairing.Base.IsPos.neg_iff_not] at hwa
  exact hwa ((hB _).mpr hβ)

/-- Inversions occurring at a shortest representative are strictly negative on
the conjugated parabolic face. Their ordered product lies in the opposite
contracting group as a scheme. -/
private theorem cell_in_opposite_contraction {T B A : ClosedSubgroup G.val}
    [IsCommMonObj T.group.X] {D : Datum T} (W : Identification D) {U U₀ : RootSubgroupFamily T}
    {c : Cocharacter T.group} {b : D.rootDatum.Base} {I : Set (Root T)}
    (P : StandardParabolic B D b U₀ I)
    (hG : IsReductive G) (hT : IsSplitTorus T.group) (hmax : RankOneFlag.IsGeometricallyMaximal T)
    (hc : IsRegular T c) (hpos : positiveRoots T c = subgroupRoots T B)
    (hb : IsBaseFor D.rootDatum (evaluate D c) b)
    {w : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hn : IsRepresentative W w n)
    (hw : Set.MapsTo (D.rootDatum.weylGroupToPerm w)
      {α | b.IsPos α ∧ α ∈ leviRoots D I} {α | b.IsPos α})
    (hA : OrderedParametrization U
      (subgroupRoots T B ∩ (D.rootDatum.weylGroupToPerm w '' (subgroupRoots T B)ᶜ)) A) :
    ∃ E : LimitDecomposition (oppositeCocharacter (P.cocharacter ≫ T.inclusion)),
      ∀ (Y : SchemeOver k) (a : Y ⟶ A.group.X),
        conjugatePoint (n ≫ W.normalizer.inclusion.hom.hom)⁻¹ (a ≫ A.inclusion.hom.hom) ∈
          SubgroupSections E.contracting Y := by
  letI := D.finiteRoots
  let faceChar := P.cocharacter
  let cocharNeg := oppositeCocharacter faceChar
  let cocharW := cocharNeg ≫ (W.image.conjugation (W.labelEquiv w)).hom
  have hcocharNeg : cocharNeg ≫ T.inclusion = oppositeCocharacter (faceChar ≫ T.inclusion) := by
    unfold cocharNeg oppositeCocharacter
    rw [Category.assoc]
  obtain ⟨⟨E⟩, _⟩ := (LinearAlgebraicGroups.RootData.OrderedRootProducts.contractingProduct
    G hG T hT hmax).2.2 cocharNeg
  obtain ⟨⟨Ew⟩, hEw⟩ := (LinearAlgebraicGroups.RootData.OrderedRootProducts.contractingProduct
    G hG T hT hmax).2.2 cocharW
  let S := subgroupRoots T B ∩ (D.rootDatum.weylGroupToPerm w '' (subgroupRoots T B)ᶜ)
  have hS : S ⊆ positiveRoots T cocharW := by
    rw [positiveRoots_conjugate W w cocharNeg]
    rintro β ⟨hβ, α, hα, rfl⟩
    refine ⟨α, ?_, rfl⟩
    have hI := inversion_not_levi hpos hb w hw α hα hβ
    have hneg := negative_face_pairing hc hpos hb P.face α hα hI
    change 0 < pairing T.group α.val cocharNeg
    rw [← D.pairing_eq, show cocharNeg = faceChar⁻¹ from oppositeCocharacter_eq_inv faceChar]
    change 0 < D.rootDatum.toLinearMap (Additive.ofMul α.val) (-Additive.ofMul faceChar)
    rw [map_neg, D.pairing_eq, neg_pos]
    exact hneg
  obtain ⟨l, hl⟩ := existsEnumeration S
  have hle : IsSubgroupOf A Ew.contracting := by
    obtain ⟨e, he⟩ := hA l hl
    apply subgroupFactorThrough
    have hr := rootProductSubset hl hS (fun l h ↦ hEw Ew U l h)
    rw [← he] at hr
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using memSubgroup_comp e.inv hr
  have hsame : SameSubgroup E.contracting E.contracting :=
    ⟨⟨𝟙 _, Category.id_comp _⟩, ⟨𝟙 _, Category.id_comp _⟩⟩
  have hcont := conjugateContractingSections E Ew _ (translatingCocharacter W hn cocharNeg)
    E.contracting hsame
  have hE (Y : SchemeOver k) (a : Y ⟶ A.group.X) :
      conjugatePoint (n ≫ W.normalizer.inclusion.hom.hom)⁻¹ (a ≫ A.inclusion.hom.hom) ∈
        SubgroupSections E.contracting Y :=
    (hcont Y _).mp (section_mem_of_le hle ⟨a, rfl⟩)
  rw [← hcocharNeg]
  exact ⟨E, hE⟩

private theorem opposite_intersection {c : Cocharacter G.val}
    (L : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    {Y : SchemeOver k} {g : Y ⟶ G.val.X} (hL : g ∈ SubgroupSections L.parabolic Y)
    (hE : g ∈ SubgroupSections E.contracting Y) : g = 1 := by
  obtain ⟨x, hx⟩ := hE
  obtain ⟨y, hy⟩ := hL
  change x ≫ E.contracting.inclusion.hom.hom = g at hx
  change y ≫ L.parabolic.inclusion.hom.hom = g at hy
  have hp := oppositeLimitIntersection G c L E
  have h := hp.lift_fst x y (hx.trans hy.symm)
  rw [← hx, ← h, Category.assoc, IsMonHom.one_hom]
  exact congrArg (· ≫ η[G.val.X]) (toUnit_unique _ _)

private theorem fixes_in_quotient {H : ClosedSubgroup G.val} (Q : Presentation H)
    (a : ModObj G.val.X Q.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    {Y : SchemeOver k} (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (g : Y ⟶ G.val.X) :
    (lift g (toUnit Y ≫ n ≫ Q.projection) ≫ a.smul = toUnit Y ≫ n ≫ Q.projection) ↔
      conjugatePoint n⁻¹ g ∈ SubgroupSections H Y := by
  rw [← Category.assoc (toUnit _) n Q.projection, actionOnQuotient Q a ha, eq_comm,
    projection_eq_iff Q]
  rw [conjugatePoint, GrpObj.comp_inv, inv_inv, mul_assoc]

/-- A full cell coordinate of an element fixing the partial flag is in both the
parabolic and its opposite contracting group after conjugation. The coordinate
is the identity, so the element already fixes the full flag. -/
private theorem partialStabilizer {T B A : ClosedSubgroup G.val} {c : Cocharacter G.val}
    (L : LimitDecomposition c) (E : LimitDecomposition (oppositeCocharacter c))
    (hB : IsSubgroupOf B L.parabolic)
    (Q : Presentation B) (R : Presentation L.parabolic)
    (a : ModObj G.val.X Q.scheme) (a' : ModObj G.val.X R.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (ha' : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ R.projection) ≫ a'.smul =
      μ[G.val.X] ≫ R.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (C : Cell (T := T) Q a n A)
    (hA : ∀ (Y : SchemeOver k) (x : Y ⟶ A.group.X),
      conjugatePoint n⁻¹ (x ≫ A.inclusion.hom.hom) ∈ SubgroupSections E.contracting Y) :
    RepresentsSubgroup C.stabilizer (fun Y t ↦
      lift (t ≫ B.inclusion.hom.hom) (toUnit Y ≫ n ≫ R.projection) ≫ a'.smul =
        toUnit Y ≫ n ≫ R.projection) := by
  intro Y t
  rw [← C.representsStabilizer Y t]
  dsimp only
  rw [fixes_in_quotient R a' ha', fixes_in_quotient Q a ha]
  refine ⟨?_, section_mem_of_le hB⟩
  intro ht
  let p := toUnit Y ≫ n
  let tG := t ≫ B.inclusion.hom.hom
  let x := (t ≫ C.projection) ≫ C.orbitIso.inv
  let xG := x ≫ A.inclusion.hom.hom
  have hfull : (xG * p) ≫ Q.projection = (tG * p) ≫ Q.projection := by
    have h₁ : x ≫ C.orbitIso.hom ≫ C.orbitInclusion =
        (xG * p) ≫ Q.projection := by
      rw [C.orbitIso_eq, MonObj.comp_mul_assoc, comp_toUnit_assoc]
    have h₂ : t ≫ C.projection ≫ C.orbitInclusion = (tG * p) ≫ Q.projection := by
      rw [C.projection_eq, comp_lift_assoc, comp_toUnit_assoc,
        ← Category.assoc (toUnit Y) n Q.projection, actionOnQuotient Q a ha]
    rw [← h₁, ← h₂]
    simp [x]
  have hr := (projection_eq_iff Q _ _).mp hfull
  have hc : conjugatePoint n⁻¹ (xG⁻¹ * tG) = (xG * p)⁻¹ * (tG * p) := by
    rw [conjugatePoint, GrpObj.comp_inv, inv_inv, mul_inv_rev]
    change p⁻¹ * (xG⁻¹ * tG) * p = _
    group
  have hsub := section_mem_of_le hB (hc.symm ▸ hr)
  have hprod := (SubgroupSections L.parabolic Y).mul_mem ht
    ((SubgroupSections L.parabolic Y).inv_mem hsub)
  have hxp : conjugatePoint n⁻¹ xG ∈ SubgroupSections L.parabolic Y := by
    rw [conjugatePoint_mul, conjugatePoint_inv, mul_inv_rev, inv_inv,
      ← mul_assoc, mul_inv_cancel, one_mul] at hprod
    exact hprod
  have hxG : xG = 1 := by
    have h := opposite_intersection L E hxp (hA Y x)
    have h' := congrArg (conjugatePoint n) h
    rw [conjugatePoint_cancel] at h'
    simpa [conjugatePoint] using h'
  simp only [hxG, inv_one, one_mul] at hc hr
  exact hc.symm ▸ hr

open private restrictGroupAction restrictGroupAction_smul from LinearAlgebraicGroups.Flag.SmoothOrbit

private theorem cellProjection_epi {T B A : ClosedSubgroup G.val} {Q : Presentation B}
    {a : ModObj G.val.X Q.scheme} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) : Epi C.projection := by
  letI : Sheaf.IsLocallySurjective (Specs.rightQuotientProjection C.stabilizer) :=
    LinearAlgebraicGroups.rightQuotientLocalLifts C.stabilizer
  refine ⟨fun f g h ↦ ?_⟩
  apply (fppfOver k).uliftYoneda.map_injective
  apply (cancel_epi (Specs.rightQuotientProjection C.stabilizer ≫ C.quotientIso.hom)).mp
  rw [C.quotientProjection, ← Functor.map_comp, ← Functor.map_comp, h]

private theorem partialOrbitImmersion {T B H A : ClosedSubgroup G.val}
    (Q : Presentation B) (R : Presentation H)
    (π : Q.scheme ⟶ R.scheme) (hπ : Q.projection ≫ π = R.projection)
    (a : ModObj G.val.X Q.scheme) (a' : ModObj G.val.X R.scheme)
    (ha : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
      μ[G.val.X] ≫ Q.projection)
    (ha' : lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ R.projection) ≫ a'.smul =
      μ[G.val.X] ≫ R.projection)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) (C : Cell (T := T) Q a n A)
    (hB : Smooth B.group.X.hom) (hR : IsProper R.scheme.hom)
    (hS : RepresentsSubgroup C.stabilizer (fun Y t ↦
      lift (t ≫ B.inclusion.hom.hom) (toUnit Y ≫ n ≫ R.projection) ≫ a'.smul =
        toUnit Y ≫ n ≫ R.projection)) :
    IsImmersion (C.orbitInclusion ≫ π).left := by
  let b := restrictGroupAction B.inclusion a'
  let x := n ≫ R.projection
  have hstab : RepresentsSubgroup C.stabilizer (fun _ t ↦ Stabilizes b.smul x t) := by
    intro Y t
    simpa only [b, x, Stabilizes, Category.assoc, restrictGroupAction_smul,
      lift_map_assoc, Category.comp_id] using hS Y t
  letI := hR
  obtain ⟨O⟩ := LinearAlgebraicGroups.SmoothOrbit.schemeOrbit k (closedSubgroupAlgebraicGroup B)
    R.scheme b x hB inferInstance inferInstance inferInstance
  let i := O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion b x
  have hi : O.projection ≫ i = Specs.SmoothOrbit.orbitMap b x := orbitProjection_eq O
  letI := O.isOpen
  have hImm : IsImmersion i.left := by
    change IsImmersion (O.openInClosure.left ≫ (Specs.SmoothOrbit.orbitMap b x).left.imageι)
    infer_instance
  letI : Mono i := Over.mono_of_mono_left i
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.SmoothOrbit.orbitQuotient k _ _ _ b x i O.projection
    C.stabilizer inferInstance hi O.flat O.surjective O.finitePresentation hstab
  let F := (fppfOver k).uliftYoneda
  let f := (fppfOver k).fullyFaithfulUliftYoneda.preimageIso (C.quotientIso.symm ≪≫ e)
  have hproj : C.projection ≫ f.hom = O.projection := by
    apply F.map_injective
    change F.map (C.projection ≫ f.hom) = F.map O.projection
    rw [Functor.map_comp, ← C.quotientProjection]
    change (Specs.rightQuotientProjection C.stabilizer ≫ C.quotientIso.hom) ≫
      F.map ((fppfOver k).fullyFaithfulUliftYoneda.preimage (C.quotientIso.inv ≫ e.hom)) = _
    rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, he]
  have hfac : C.projection ≫ C.orbitInclusion ≫ π = Specs.SmoothOrbit.orbitMap b x := by
    rw [← Category.assoc, C.projection_eq, ← Category.assoc (toUnit _) n Q.projection,
      actionOnQuotient Q a ha, Category.assoc, hπ]
    unfold Specs.SmoothOrbit.orbitMap
    change _ = lift (𝟙 B.group.X) ((toUnit B.group.X ≫ n) ≫ R.projection) ≫
      (restrictGroupAction B.inclusion a').smul
    rw [restrictGroupAction_smul, lift_map_assoc, Category.id_comp, Category.comp_id,
      actionOnQuotient R a' ha']
  have heq : C.orbitInclusion ≫ π = f.hom ≫ i := by
    letI := cellProjection_epi C
    apply (cancel_epi C.projection).mp
    rw [hfac, ← Category.assoc, hproj, hi]
  rw [heq, Over.comp_left]
  letI := hImm
  infer_instance

private theorem partialRangeOfDouble {T B H A : ClosedSubgroup G.val}
    {Q : Presentation B} {R : Presentation H}
    {π : Q.scheme ⟶ R.scheme} (hπ : Q.projection ≫ π = R.projection)
    {a : ModObj G.val.X Q.scheme} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (C : Cell (T := T) Q a n A) :
    Set.range (C.doubleOrbitInclusion ≫ R.projection).left =
      Set.range (C.orbitInclusion ≫ π).left := by
  rw [← hπ, ← Category.assoc, range_comp_left _ π, range_comp_left _ π,
    range_comp_left _ Q.projection, doubleOrbitRange,
    Set.image_preimage_eq _ Q.surjective.1]

private theorem disjointCosetUnions {M X : Type*} [Group M] (H : Subgroup M)
    (E : M → Set X) (hE : ∀ w v, w ≠ v → Disjoint (E w) (E v)) {w v : M}
    (h : w⁻¹ * v ∉ H) :
    Disjoint (⋃ u : H, E (w * u.val)) (⋃ u : H, E (v * u.val)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hy
  have he : w * a.val = v * b.val := by
    by_contra hne
    exact Set.disjoint_left.mp (hE _ _ hne) ha hb
  apply h
  have hm : w⁻¹ * v = a.val * b.val⁻¹ := by rw [← mul_inv_cancel_right v b.val, ← he]; group
  rw [hm]
  exact H.mul_mem a.property (H.inv_mem b.property)

private theorem equalCosetUnions {M X : Type*} [Group M] (H : Subgroup M) (E : M → Set X)
    {w v : M} (h : w⁻¹ * v ∈ H) :
    (⋃ u : H, E (w * u.val)) = ⋃ u : H, E (v * u.val) := by
  have inc (w v : M) (h : w⁻¹ * v ∈ H) :
      (⋃ u : H, E (v * u.val)) ⊆ ⋃ u : H, E (w * u.val) := by
    intro x hx
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
    let b : H := ⟨w⁻¹ * v, h⟩ * a
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    simpa only [b, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left] using ha
  exact (inc v w (by simpa only [mul_inv_rev, inv_inv] using H.inv_mem h)).antisymm (inc w v h)

private theorem subword_closure {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum Idx X Y) (b : P.Base) {f : X →ₗ[ℤ] ℤ} (hb : IsBaseFor P f b)
    {Z : Type*} [TopologicalSpace Z] (F : P.weylGroup → Set Z)
    (h : ∀ l : List b.support, IsReduced P b l →
      let w := wordProduct P b l
      (∀ v, (v ∈ subwordProducts P b l ↔ SubwordLE P b v w) ∧
        (v ∈ subwordProducts P b l ↔ ∃ r : List b.support, r.Sublist l ∧
          IsReduced P b r ∧ wordProduct P b r = v)) ∧
      closure (F w) = ⋃ v ∈ subwordProducts P b l, F v) (w : P.weylGroup) :
    closure (F w) = ⋃ (v : P.weylGroup) (_ : SubwordLE P b v w), F v := by
  obtain ⟨l, hl, hlen, _⟩ := exists_shortest_word P b hb.generates w
  have hr : IsReduced P b l := by
    unfold GallerySubwords.IsReduced
    rw [hl, hlen]
  obtain ⟨hle, hc⟩ := h l hr
  rw [hl] at hle hc
  exact hc.trans (by simp_rw [fun v ↦ (hle v).1])

private theorem subword_trans {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum Idx X Y) (b : P.Base) {Z : Type*} [TopologicalSpace Z]
    (F : P.weylGroup → Set Z)
    (h : ∀ v w, SubwordLE P b v w ↔ F v ⊆ closure (F w)) :
    ∀ x y z, SubwordLE P b x y → SubwordLE P b y z → SubwordLE P b x z := by
  intro x y z hxy hyz
  exact (h _ _).mpr ((h _ _).mp hxy |>.trans (closure_minimal ((h _ _).mp hyz) isClosed_closure))

open private kBorel_smooth_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers

private theorem splitCells
    (hParabolic : Specs.ParabolicCosetLength.Statement.{u,u,u,u})
    (hSchubert : Specs.SchubertClosures.Statement.{u}) :
    Specs.PartialFlags.SplitCells.{u} := by
  classical
  intro k _ G hG T B hT hmax hB hTB
  obtain ⟨hcomm, D, W, U, c, b, hc, hpos, hb, hpar⟩ := hParabolic.1 G hG T B hT hmax hB hTB
  letI := hcomm
  obtain ⟨hcommS, DS, WS, cS, bS, _, hposS, hbS, hrepS, hQS, hSch⟩ :=
    hSchubert G hG T B hT hmax hB hTB
  have hDS := rootDatum_eq_of_identifications W WS hrepS
  subst DS
  have hbS_eq := base_eq hb hbS (hpos.trans hposS.symm)
  subst bS
  obtain ⟨hcommC, DC, WC, UC, Bneg, Rpos, Rneg, cC, bC,
    _, _, hneg, _, _, _, hposC, hbC, hrepC, _, hCells⟩ :=
    _root_.LinearAlgebraicGroups.Flag.BruhatCells.bruhatCells G hG T B hT hmax hB hTB
  have hDC := rootDatum_eq_of_identifications W WC hrepC
  subst DC
  have hbC_eq := base_eq hb hbC (hpos.trans hposC.symm)
  subst bC
  refine ⟨hcomm, D, W, U, c, b, hc, hpos, hb, ?_, hQS, ?_⟩
  · intro w
    obtain ⟨n, hn⟩ := hrepS w
    obtain ⟨n', hn', _⟩ := transferRepresentative_sameDatum WS W hn
    exact ⟨n', hn'⟩
  intro I hI
  obtain ⟨P, _, _, hSat⟩ := hpar I hI
  let H := P.limitGroups.parabolic
  let WI := parabolicWeylGroup D I
  letI := D.finiteRoots
  letI := D.freeCharacters
  letI := D.finiteCharacters
  letI := D.freeCocharacters
  letI := D.finiteCocharacters
  letI := D.reduced
  letI := D.reducedCoroots
  have hlength := hParabolic.2 D.rootDatum b I hI
  have hproj := _root_.LinearAlgebraicGroups.ProjectiveFlags.smoothProjectiveQuotient k G H P.parabolic
  have hBs := (kBorel_smooth_connected G B hB).1
  have hBpar : Specs.BorelProper.IsParabolic G B := by
    refine ⟨hG, hBs, ?_⟩
    obtain ⟨h, hgeom⟩ := hB
    exact ⟨h, _, hgeom, 𝟙 _, Category.id_comp _⟩
  have hfull := _root_.LinearAlgebraicGroups.ProjectiveFlags.smoothProjectiveQuotient k G B hBpar
  refine ⟨P, hproj.1, fun w ↦ (hlength w).1, ?_⟩
  intro Q R n hn
  dsimp only
  let g := fun w ↦ n w ≫ W.normalizer.inclusion.hom.hom
  choose nS hnS hgS using fun w ↦ transferRepresentative_sameDatum W WS (hn w)
  choose nC hnC hgC using fun w ↦ transferRepresentative_sameDatum W WC (hn w)
  obtain ⟨a, ha, hCellQ⟩ := hCells Q
  have hCelln := hCellQ nC hnC
  have hgC_eq : (fun w ↦ nC w ≫ WC.normalizer.inclusion.hom.hom) = g := funext hgC
  rw [hgC_eq] at hCelln
  dsimp only at hCelln
  obtain ⟨A, C, hC, hdisj, hCover, _⟩ := hCelln
  obtain ⟨aS, haS, hSchQ⟩ := hSch Q
  have hSchn := hSchQ nS hnS
  have hgS_eq : (fun w ↦ nS w ≫ WS.normalizer.inclusion.hom.hom) = g := funext hgS
  rw [hgS_eq] at hSchn
  dsimp only at hSchn
  obtain ⟨AS, CS, _, hOrder, hClosure⟩ := hSchn
  have hSatn := hSat Q n hn
  dsimp only at hSatn
  obtain ⟨aSat, ASat, CSat, haSat, _, hSatRange⟩ := hSatn
  obtain ⟨π, hπ⟩ := quotientMapExists Q R P.containsBorel
  let a' := quotientAction R
  have ha' := quotientAction_mul R
  have hProperR := (hproj.2 R).2.1
  have hProper : IsProper π.left := by
    letI := hProperR
    letI : IsProper (π.left ≫ R.scheme.hom) := Over.w π ▸ (hfull.2 Q).2.1
    exact IsProper.of_comp π.left R.scheme.hom
  let j := fun w ↦ (C w).orbitInclusion ≫ π
  let F := fun w ↦ Set.range (j w).left
  let Ffull := fun w ↦ Set.range (C w).orbitInclusion.left
  let E := fun w ↦ Set.range (C w).doubleOrbitInclusion.left
  have hF (w) : F w = π.left '' Ffull w := range_comp_left _ _
  have hSc (w) : Set.range (CS w).orbitInclusion.left = Ffull w :=
    (fullOrbitRange haS (CS w)).trans (fullOrbitRange ha (C w)).symm
  have hSatFull (w) : Set.range (CSat w).orbitInclusion.left = Ffull w :=
    (fullOrbitRange haSat (CSat w)).trans (fullOrbitRange ha (C w)).symm
  have hSatDouble (w) : Set.range (CSat w).doubleOrbitInclusion.left = E w := by
    rw [doubleOrbitRange, hSatFull, show E w = _ from doubleOrbitRange (C w)]
  have horbit (w) : F w = Set.range
      (lift B.inclusion.hom.hom (toUnit B.group.X ≫ g w ≫ R.projection) ≫ a'.smul).left := by
    rw [hF, show Ffull w = _ from fullOrbitRange ha (C w),
      ← range_comp_left, Category.assoc, hπ,
      ← Category.assoc (toUnit _) (g w) R.projection, actionOnQuotient R a' ha']
  have hPreimage (w) : R.projection.left ⁻¹' F w = ⋃ v : WI, E (w * v.val) := by
    have h := hSatRange w
    rw [saturation_range, partialRangeOfDouble hπ, range_comp_left, hSatFull, ← hF] at h
    simpa only [hSatDouble] using h
  have hdis (w v) (h : w⁻¹ * v ∉ WI) : Disjoint (F w) (F v) := by
    have hh := disjointCosetUnions WI E (fun w v h ↦ (hdisj w v h).2) h
    rw [← hPreimage, ← hPreimage] at hh
    apply Set.disjoint_left.mpr
    intro y hy hy'
    obtain ⟨x, rfl⟩ := R.surjective.1 y
    exact Set.disjoint_left.mp hh hy hy'
  have hFs (w v) : F w = F v ↔ w⁻¹ * v ∈ WI := by
    refine ⟨?_, fun h ↦ (Set.preimage_injective.mpr R.surjective.1) ?_⟩
    · intro he
      by_contra! h
      have hd := hdis w v h
      rw [← he] at hd
      obtain ⟨x, hx⟩ : (F w).Nonempty := by
        rw [horbit]
        exact ⟨_, ⟨(η[B.group.X]).left (IsLocalRing.closedPoint k), rfl⟩⟩
      exact Set.disjoint_left.mp hd hx hx
    · rw [hPreimage, hPreimage]
      exact equalCosetUnions WI E h
  have hcover : (⋃ w, F w) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := R.surjective.1 y
    have hx : x ∈ ⋃ w, E w := hCover ▸ Set.mem_univ x
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨w, ?_⟩
    change x ∈ R.projection.left ⁻¹' F w
    rw [hPreimage]
    exact Set.mem_iUnion.mpr ⟨1, by simpa using hw⟩
  refine ⟨π, a, a', A, C, hπ, hProper, ha, ha', horbit, hFs, hdis, hcover, ?_⟩
  intro w hw
  have hwpos : Set.MapsTo (D.rootDatum.weylGroupToPerm w)
      {α | b.IsPos α ∧ α ∈ leviRoots D I} {α | b.IsPos α} :=
    ((hlength w).2.1 w |>.mp hw).2
  have hA := (hC w).2.1
  rw [hneg] at hA
  obtain ⟨Lneg, hLneg⟩ := cell_in_opposite_contraction W P hG hT hmax hc hpos hb (hn w) hwpos hA
  have hStab := partialStabilizer P.limitGroups Lneg P.containsBorel Q R a a' ha ha' (g w) (C w) hLneg
  have hImm := partialOrbitImmersion Q R π hπ a a' ha ha' (g w) (C w) hBs hProperR hStab
  refine ⟨hImm, (hC w).2.2, hStab, vanishingSubschemeReduced _, ?_⟩
  have hClosureFull : closure (Ffull w) = ⋃ (v : D.rootDatum.weylGroup) (_ : SubwordLE D.rootDatum b v w), Ffull v := by
    refine subword_closure D.rootDatum b hb Ffull (fun l hl ↦ ?_) w
    obtain ⟨hwords, he, _⟩ := hClosure l hl
    rw [range_closureIdeal] at he
    refine ⟨hwords, ?_⟩
    simpa only [hSc] using he
  rw [range_closureIdeal]
  change closure (F w) = ⋃ (v : {v // IsMinimal D b I v}) (_ : SubwordLE D.rootDatum b v.val w), F v.val
  simp only [hF]
  letI := hProper
  refine projectedClosure π.left π.left.continuous π.left.isClosedMap Ffull
    (SubwordLE D.rootDatum b) (IsMinimal D b I) w hClosureFull (fun v ↦ ?_)
    (subword_trans D.rootDatum b Ffull (fun v w ↦ by simpa only [hSc] using hOrder v w))
  obtain ⟨m, hm, _⟩ := (hlength v).1
  refine ⟨m, minimal_of_shortest hm, ?_, subword_of_shortest D.rootDatum b hb hm ((hlength v).2.2 m hm)⟩
  rw [← hF, ← hF]
  exact ((hFs v m).mpr hm.1).symm

/-- The partial flag theorem follows from parabolic coset length and saturation,
and the full flag Schubert closure theorem. -/
theorem partialFlags_conditional.{v} :
    Specs.ParabolicCosetLength.Statement.{v,v,v,v} →
    Specs.SchubertClosures.Statement.{v} →
    Specs.PartialFlags.Statement.{v} := by
  intro hParabolic hSchubert
  exact ⟨_root_.LinearAlgebraicGroups.ProjectiveFlags.smoothProjectiveQuotient,
    splitCells hParabolic hSchubert⟩

/-- Parabolic quotients are smooth and projective, and their split Bruhat cells
and reduced closures are indexed by the shortest Weyl coset representatives. -/
theorem partialFlags : Specs.PartialFlags.Statement.{u} :=
  partialFlags_conditional
    _root_.LinearAlgebraicGroups.Flag.ParabolicCosetLength.parabolicCosetLength
    _root_.LinearAlgebraicGroups.Flag.SchubertClosures.schubertClosures

end

end LinearAlgebraicGroups.Flag.PartialFlags
