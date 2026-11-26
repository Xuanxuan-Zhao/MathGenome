import Specs.LinearAlgebraicGroups.Unipotent.CanonicalSplitSubgroup
import LinearAlgebraicGroups.Unipotent.CentralAdditiveSubgroup
import LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
import LinearAlgebraicGroups.Unipotent.WoundExample
import LinearAlgebraicGroups.Affine.Components
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Whiskering
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Unipotent

open _root_.LinearAlgebraicGroups.Specs.Unipotent
open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel AffineAlgebraicGroup GroupScheme
  ClosedSubgroup IsNormalSubgroup)

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]

/-- A group is wound if every morphism from the affine line is constant. -/
abbrev IsWound : IsWoundType.{u} := @Specs.Unipotent.IsWound

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.PerfectFieldVectorGroups
open private origin_constant from LinearAlgebraicGroups.Unipotent.CentralKilledByPCurves
open private factor_through_closed from LinearAlgebraicGroups.Unipotent.CentralSeries
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private IsCentralIn central_comp central_normal
  trivial_map_eq_one sections_eq_one_of_trivial additive_point_specialization
  trivialAffine trivial_inclusion_closed exists_central_additive_charZero
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness

private abbrev schemeForget (k : Type u) [Field k] : GroupScheme k ⥤ Scheme.{u} :=
  Grp.forget _ ⋙ Over.forget _

private theorem additiveCurve_nonconstant (k : Type u) [Field k] :
    IsNonconstantCurve (G := (StandardGroups.additiveGroup k).val) (𝟙 _) := by
  intro h
  obtain ⟨x, hx, _⟩ := additive_point_specialization (k := k)
  let y := groupIdentityPoint (StandardGroups.additiveGroup k).val
  have he : ∀ a : (StandardGroups.additiveGroup k).val.X.left,
      a = (constantCurve (curveAtZero (G := (StandardGroups.additiveGroup k).val) (𝟙 _))).left a :=
    fun a => congrArg (fun f : AffineLineCurve (StandardGroups.additiveGroup k).val => f.left a) h
  let : Subsingleton ((testSpec k).obj (op (CommAlgCat.of k k))).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  apply hx
  exact (he x).trans ((congrArg (curveAtZero (G := (StandardGroups.additiveGroup k).val)
    (𝟙 _)).left (Subsingleton.elim _ _)).trans (he y).symm)

private theorem nonconstant_comp_mono {G H : GroupScheme k} (f : G.X ⟶ H.X)
    [Mono f] {a : AffineLineCurve G} (ha : IsNonconstantCurve a) :
    IsNonconstantCurve (G := H) (a ≫ f) := by
  intro h
  apply ha
  apply (cancel_mono f).mp
  simpa only [constantCurve, curveAtZero, mapPoints, Category.assoc] using h

private theorem no_additive_of_wound {U : AffineAlgebraicGroup k} (h : IsWound U.val)
    (N : ClosedSubgroup U.val)
    (e : (groupPointsFunctor k).obj N.group ≅ Specs.StandardGroups.additivePoints k) : False := by
  let A := StandardGroups.additiveGroup k
  let N' := closedSubgroupAlgebraicGroup N
  let j := groupIsoOfPoints A.property.1 N'.property.1 (StandardGroups.additiveGroupPointsIso k ≪≫ e.symm)
  let := N.isClosedImmersion
  let : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  let f : A.val.X ⟶ N.group.X := j.hom.hom.hom
  let : IsIso f := inferInstanceAs (IsIso j.hom.hom.hom)
  have hj := nonconstant_comp_mono (G := A.val) (H := N.group) f (additiveCurve_nonconstant k)
  exact h _ (nonconstant_comp_mono (G := N.group) (H := U.val) N.inclusion.hom.hom hj)

private theorem fieldSpecSelf (k : Type u) [Field k] : fieldSpecMap k k = 𝟙 _ := by
  rw [← Spec.map_id]
  congr 1

private theorem wound_map_from_additive {G : GroupScheme k} (hw : IsWound G)
    (x : (StandardGroups.additiveGroup k).val.X ⟶ G.X)
    (hx : η[(StandardGroups.additiveGroup k).val.X] ≫ x = 1) : x = 1 := by
  classical
  let A := (StandardGroups.additiveGroup k).val.X
  let K := (testSpec k).obj (op (CommAlgCat.of k k))
  have he : x = constantCurve (curveAtZero x) := not_not.mp (hw x)
  let b : A ⟶ K := (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k (Polynomial k))).op
  have hK : K.hom = 𝟙 _ := fieldSpecSelf k
  let e : (𝟙_ (SchemeOver k)) ⟶ K := by
    refine Over.homMk (𝟙 (Spec (CommRingCat.of k))) ?_
    change 𝟙 (Spec (CommRingCat.of k)) ≫ fieldSpecMap k k = 𝟙 (Spec (CommRingCat.of k))
    rw [Category.id_comp, fieldSpecSelf]
  have he' : b = toUnit A ≫ e := by
    apply Over.OverMorphism.ext
    let : IsIso K.hom := hK ▸ inferInstanceAs (IsIso (𝟙 (Spec (CommRingCat.of k))))
    apply (cancel_mono K.hom).mp
    rw [Over.w, Over.w]
  change x = b ≫ curveAtZero x at he
  have hx' : x = toUnit A ≫ e ≫ curveAtZero x :=
    he.trans (by rw [he', Category.assoc])
  have hunit : η[(StandardGroups.additiveGroup k).val.X] ≫ toUnit A = 𝟙 _ :=
    (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  have h₀ : e ≫ curveAtZero x = 1 := calc
    _ = η[(StandardGroups.additiveGroup k).val.X] ≫
        (toUnit A ≫ e ≫ curveAtZero x) := by rw [← Category.assoc, hunit, Category.id_comp]
    _ = η[(StandardGroups.additiveGroup k).val.X] ≫ x := congrArg _ hx'.symm
    _ = 1 := hx
  exact hx'.trans (by rw [h₀, MonObj.comp_one])

private theorem wound_map_of_quotient {S Q U : AffineAlgebraicGroup k}
    (N : ClosedSubgroup S.val) (q : S.val ⟶ Q.val) (hq : IsFppfGroupQuotient N q)
    (f : S.val ⟶ U.val) (hf : N.inclusion.hom.hom ≫ f.hom.hom = 1)
    (hQ : Nonempty (Q.val ≅ Grp.trivial (SchemeOver k)) ∨
      Nonempty ((groupPointsFunctor k).obj Q.val ≅ Specs.StandardGroups.additivePoints k))
    (hU : IsWound U.val) : f.hom.hom = 1 := by
  let p := q.hom.hom.left
  let g := f.hom.hom.left
  let := hq.2.1
  let := hq.2.2.1
  let := S.property.1
  let := Q.property.1
  have : Flat p := ‹Flat q.hom.hom.left›
  have : Surjective p := ‹Surjective q.hom.hom.left›
  have : IsRegularEpi p := isRegularEpi_of_flat_of_surjective_of_isAffine p
  have eq_pair {T : Scheme.{u}} (x y : T ⟶ S.val.X.left) (he : x ≫ p = y ≫ p) :
      x ≫ g = y ≫ g := by
    let V := Over.mk (x ≫ S.val.X.hom)
    let a : V ⟶ S.val.X := Over.homMk x rfl
    let b : V ⟶ S.val.X := Over.homMk y (by
      change y ≫ S.val.X.hom = x ≫ S.val.X.hom
      rw [← q.hom.hom.w, ← Category.assoc, ← Category.assoc, he])
    let φ := IsMonHom.monoidHom q.hom.hom V
    have hab : φ a = φ b := Over.OverMorphism.ext he
    have hker : (a⁻¹ * b) ≫ q.hom.hom = 1 := by
      change φ (a⁻¹ * b) = 1
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    obtain ⟨n, hn⟩ := (schemeKernel_sections hq.1 (a⁻¹ * b)).mpr hker
    change n ≫ N.inclusion.hom.hom = a⁻¹ * b at hn
    let ψ := IsMonHom.monoidHom f.hom.hom V
    have hψ : ψ (a⁻¹ * b) = 1 := by
      change (a⁻¹ * b) ≫ f.hom.hom = 1
      rw [← hn, Category.assoc, hf, MonObj.comp_one]
    rw [map_mul, map_inv, inv_mul_eq_one] at hψ
    exact congrArg Over.Hom.left hψ
  obtain ⟨v, hv⟩ := IsRegularEpi.exists_of_isKernelPair p (IsKernelPair.of_hasPullback p)
    g (eq_pair _ _ pullback.condition)
  let v' : Q.val.X ⟶ U.val.X := Over.homMk v (by
    apply (cancel_epi p).mp
    rw [← Category.assoc, hv, f.hom.hom.w, q.hom.hom.w])
  have hv' : q.hom.hom ≫ v' = f.hom.hom := Over.OverMorphism.ext hv
  have hvone : η[Q.val.X] ≫ v' = 1 := by
    rw [← IsMonHom.one_hom q.hom.hom, Category.assoc, hv', IsMonHom.one_hom]
    rfl
  have hc : v' = 1 := by
    rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · calc
        v' = 𝟙 Q.val.X ≫ v' := (Category.id_comp v').symm
        _ = (toUnit Q.val.X ≫ η[Q.val.X]) ≫ v' :=
          congrArg (· ≫ v') (sections_eq_one_of_trivial ⟨e⟩ (𝟙 _))
        _ = 1 := by rw [Category.assoc, hvone, MonObj.comp_one]
    · let A := StandardGroups.additiveGroup k
      let j := groupIsoOfPoints A.property.1 Q.property.1 (StandardGroups.additiveGroupPointsIso k ≪≫ e.symm)
      have : IsIso ((Grp.forget _).map j.hom) := inferInstance
      apply (cancel_epi j.hom.hom.hom).mp
      rw [MonObj.comp_one]
      apply wound_map_from_additive hU
      rw [← Category.assoc, IsMonHom.one_hom, hvone]
  rw [← hv', hc, MonObj.comp_one]

theorem splitToWoundTrivial : SplitToWoundTrivial.{u} := by
  intro k _ S U hS hU f
  obtain ⟨_, n, C, hC⟩ := hS
  have hterm : ∀ i ≤ n, (C.inclusion i ≫ f).hom.hom = 1 := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | of_succ i hi ih =>
      obtain ⟨Q, q, hq, hA⟩ := hC i hi
      apply wound_map_of_quotient _ q hq _ ?_ hA hU
      exact ih
    | self =>
      simpa only [Category.id_comp] using
        (trivial_map_eq_one ⟨C.bottom⟩ (C.inclusion n ≫ f) (𝟙 _))
  have he := hterm 0 (Nat.zero_le _)
  have : IsIso ((Grp.forget _).map C.top.hom) := inferInstance
  exact (cancel_epi C.top.hom.hom.hom).mp (he.trans (MonObj.comp_one _).symm)

private theorem wound_of_trivial {G : GroupScheme k}
    (h : Nonempty (G ≅ Grp.trivial (SchemeOver k))) : IsWound G := by
  intro a ha
  exact ha ((sections_eq_one_of_trivial h a).trans
    (sections_eq_one_of_trivial h (constantCurve (curveAtZero a))).symm)

private theorem wound_of_structural_iso {G : GroupScheme k} [IsIso G.X.hom] : IsWound G := by
  intro a ha
  apply ha
  apply Over.OverMorphism.ext
  rw [← cancel_mono G.X.hom, a.w, (constantCurve (curveAtZero a)).w]

private theorem trivial_structural_iso {G : GroupScheme k}
    (e : G ≅ Grp.trivial (SchemeOver k)) : IsIso G.X.hom := by
  have h : (schemeForget k).map e.hom = G.X.hom := by
    change (_ : G.X.left ⟶ Spec (CommRingCat.of k)) = G.X.hom
    exact (Category.comp_id _).symm.trans e.hom.hom.hom.w
  exact h ▸ (schemeForget k).map_isIso e.hom

private def baseChangeSelfIso (X : SchemeOver k) : (baseChange k k).obj X ≅ X := by
  exact (eqToIso (congrArg (fun f => (Over.pullback f).obj X) (fieldSpecSelf k))) ≪≫
    Over.pullbackId.app X

private theorem isCentralIn_of_centralizes {U : AffineAlgebraicGroup k} (H : ClosedSubgroup U.val)
    (h : Centralizes (𝟙 U.val) H.inclusion.hom.hom) :
    IsCentralIn H.inclusion := by
  intro T a b
  exact ((centralizes_iff (𝟙 U.val) H.inclusion.hom.hom).mp h T b a).symm

private theorem central_additive_of_curve (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : AffineAlgebraicGroup k) (hs : Smooth U.val.X.hom)
    (hc : ConnectedSpace U.val.X.left) (hu : IsUnipotent U)
    (K : Type u) [Field K] [Algebra k K] [Algebra.IsTranscendentalSeparable k K]
    (x : AffineLineCurve ((groupBaseChange k K).obj U.val)) (hx : IsNonconstantCurve x) :
    ∃ j : (StandardGroups.additiveGroup k).val ⟶ U.val,
      IsClosedImmersion j.hom.hom.left ∧ IsCentralIn j := by
  obtain ⟨H, hH, ⟨e⟩⟩ := centralAdditiveSubgroup p U hs hc hu K x hx
  let A := StandardGroups.additiveGroup k
  let B := closedSubgroupAlgebraicGroup H
  let t := groupIsoOfPoints A.property.1 B.property.1
    (StandardGroups.additiveGroupPointsIso k ≪≫ e.symm)
  refine ⟨t.hom ≫ H.inclusion, ?_, central_comp (isCentralIn_of_centralizes H hH) t.hom⟩
  change IsClosedImmersion ((schemeForget k).map t.hom ≫ H.inclusion.hom.hom.left)
  have ht : IsClosedImmersion ((schemeForget k).map t.hom) := by
    let : IsIso ((schemeForget k).map t.hom) := (schemeForget k).map_isIso t.hom
    infer_instance
  exact @IsClosedImmersion.comp _ _ _ _ _ ht H.isClosedImmersion

private theorem central_additive_of_nonwound (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : AffineAlgebraicGroup k) (hs : Smooth U.val.X.hom)
    (hc : ConnectedSpace U.val.X.left) (hu : IsUnipotent U) (hw : ¬ IsWound U.val) :
    ∃ j : (StandardGroups.additiveGroup k).val ⟶ U.val,
      IsClosedImmersion j.hom.hom.left ∧ IsCentralIn j := by
  classical
  change ¬ (∀ x : AffineLineCurve U.val, ¬ IsNonconstantCurve x) at hw
  obtain ⟨a, ha⟩ := not_forall.mp hw
  let V := (groupBaseChange k k).obj U.val
  let e : V.X ≅ U.val.X := baseChangeSelfIso U.val.X
  have ha' : IsNonconstantCurve (G := V) (a ≫ e.inv) :=
    nonconstant_comp_mono (G := U.val) (H := V) e.inv (not_not.mp ha)
  exact central_additive_of_curve p U hs hc hu k _ ha'

theorem woundIffNoAdditiveSubgroup : WoundIffNoAdditiveSubgroup.{u} := by
  intro k _ U hs hc hu
  constructor
  · intro hw N ⟨e⟩
    exact no_additive_of_wound hw N e
  · intro h
    by_contra hw
    obtain ⟨j, hj, _⟩ : ∃ j : (StandardGroups.additiveGroup k).val ⟶ U.val,
        IsClosedImmersion j.hom.hom.left ∧ IsCentralIn j := by
      rcases CharP.exists' k with h₀ | ⟨p, hp, hkp⟩
      · exact exists_central_additive_charZero U hu (fun ht => hw (wound_of_trivial ht))
      · exact central_additive_of_nonwound p U hs hc hu hw
    exact h ⟨_, j, hj⟩ ⟨StandardGroups.additiveGroupPointsIso k⟩

theorem woundSeparableExtension : WoundSeparableExtension.{u} := by
  intro k _ U hs hc hu hw K _ _ _
  rcases CharP.exists' k with h₀ | ⟨p, hp, hkp⟩
  · have ht : Nonempty (U.val ≅ Grp.trivial (SchemeOver k)) := by
      by_contra h
      obtain ⟨j, hj, _⟩ := exists_central_additive_charZero U hu h
      exact no_additive_of_wound hw ⟨_, j, hj⟩ (StandardGroups.additiveGroupPointsIso k)
    let : IsIso U.val.X.hom := trivial_structural_iso ht.some
    let : IsIso ((groupBaseChange k K).obj U.val).X.hom :=
      inferInstanceAs (IsIso (pullback.snd U.val.X.hom (fieldSpecMap k K)))
    exact wound_of_structural_iso
  · intro x hx
    obtain ⟨j, hj, _⟩ := central_additive_of_curve p U hs hc hu K x hx
    exact no_additive_of_wound hw ⟨_, j, hj⟩ (StandardGroups.additiveGroupPointsIso k)

open private identityDimension identityDimension_lt
  represented_quotient_of_kernel liftSeries liftSeries_map liftSeries_factor liftSeries_last_factor
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private baseChangeMapIsPullback from LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open scoped TensorProduct

private theorem smoothConnected_quotient {G Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    (hf : Flat q.hom.hom.left) (hj : Surjective q.hom.hom.left)
    (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left) :
    Smooth Q.val.X.hom ∧ ConnectedSpace Q.val.X.left := by
  refine ⟨(affineGroupSmoothnessCriteria k Q).1.mpr ?_, ?_⟩
  · refine ⟨(geometrically_iff_of_isClosedUnderIsomorphisms (P := fun Z ↦ IsReduced Z)).mpr ?_⟩
    intro K _ b
    let t := pullback.snd Q.val.X.hom b
    let v := pullback.fst q.hom.hom.left (pullback.fst Q.val.X.hom b)
    let r := pullback.snd q.hom.hom.left (pullback.fst Q.val.X.hom b)
    have : IsAffine Q.val.X.left := Q.property.1
    have : IsAffine G.val.X.left := G.property.1
    have : IsAffine (pullback Q.val.X.hom b) := inferInstance
    have : IsAffine (pullback q.hom.hom.left (pullback.fst Q.val.X.hom b)) := inferInstance
    have : Flat q.hom.hom.left := hf
    have : Surjective q.hom.hom.left := hj
    have hff := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine r).mp
      ⟨inferInstance, inferInstance⟩
    have hpb : IsPullback v (r ≫ t) G.val.X.hom b := by
      rw [← q.hom.hom.w]
      exact (IsPullback.of_hasPullback q.hom.hom.left (pullback.fst Q.val.X.hom b)).paste_vert
        (IsPullback.of_hasPullback Q.val.X.hom b)
    have : Smooth (r ≫ t) := MorphismProperty.of_isPullback (P := @Smooth) hpb hs
    have := isReduced_of_smooth_over_field (r ≫ t)
    have : IsReduced Γ(pullback Q.val.X.hom b, ⊤) := isReduced_of_injective _ hff.injective
    exact isReduced_of_isAffine_isReduced _
  · let := hc
    exact (Surjective.surj (f := q.hom.hom.left)).connectedSpace q.hom.hom.left.continuous

private theorem normal_of_schemeKernel {G Q : GroupScheme k} (q : G ⟶ Q)
    (H : ClosedSubgroup G) (h : IsSchemeKernel q H) : IsNormalSubgroup H.inclusion := by
  apply (schemeKernel_sections h (Specs.subgroupConjugation H.inclusion)).mpr
  let T := G.X ⊗ H.group.X
  let φ := IsMonHom.monoidHom q.hom.hom T
  change φ ((fst G.X H.group.X * (snd G.X H.group.X ≫ H.inclusion.hom.hom)) *
    (fst G.X H.group.X)⁻¹) = 1
  have hh : φ (snd G.X H.group.X ≫ H.inclusion.hom.hom) = 1 :=
    (schemeKernel_sections h _).mp ⟨_, rfl⟩
  rw [map_mul, map_mul, map_inv, hh, mul_one, mul_inv_cancel]

private theorem subgroup_mono {G : GroupScheme k} (H : ClosedSubgroup G) :
    Mono H.inclusion.hom.hom := by
  let := H.isClosedImmersion
  exact Over.mono_of_mono_left _

private theorem groupSubgroup_mono {G : GroupScheme k} (H : ClosedSubgroup G) :
    Mono H.inclusion := by
  exact (Grp.forget _).mono_of_mono_map (subgroup_mono H)

private theorem factorsThrough_kernel {G Q A : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val)
    (H : ClosedSubgroup G.val) (hk : IsSchemeKernel q H) (f : A.val ⟶ G.val)
    (hf : (f ≫ q).hom.hom = 1) : ∃ j : A.val ⟶ H.group, j ≫ H.inclusion = f := by
  apply factor_through_closed (B := closedSubgroupAlgebraicGroup H) f H.inclusion H.isClosedImmersion
  intro R x
  apply (schemeKernel_sections hk (x ≫ f.hom.hom)).mpr
  change (x ≫ f.hom.hom) ≫ q.hom.hom = 1
  rw [Category.assoc, show f.hom.hom ≫ q.hom.hom = 1 from hf, MonObj.comp_one]

private theorem largest_of_wound_quotient {G Q : AffineAlgebraicGroup k}
    (q : G.val ⟶ Q.val) (H : ClosedSubgroup G.val) (hk : IsSchemeKernel q H)
    (hs : Smooth H.group.X.hom) (hc : ConnectedSpace H.group.X.left)
    (hH : IsSplitUnipotent (closedSubgroupAlgebraicGroup H)) (hw : IsWound Q.val) :
    IsLargestSplitSubgroup (U := G) H := by
  refine ⟨hs, hc, hH, fun N hN ↦ ?_⟩
  exact factorsThrough_kernel (A := closedSubgroupAlgebraicGroup N) q H hk N.inclusion
    (splitToWoundTrivial (closedSubgroupAlgebraicGroup N) Q hN hw (N.inclusion ≫ q))

theorem canonicalSplitSubgroupUniqueness : CanonicalSplitSubgroupUniqueness.{u} := by
  intro k _ G H N hH hN
  obtain ⟨f, hf⟩ := hN.2.2.2 H hH.2.2.1
  obtain ⟨g, hg⟩ := hH.2.2.2 N hN.2.2.1
  let := groupSubgroup_mono H
  let := groupSubgroup_mono N
  let e : H.group ≅ N.group :=
    ⟨f, g, (cancel_mono H.inclusion).mp (by simp [Category.assoc, hg, hf]),
      (cancel_mono N.inclusion).mp (by simp [Category.assoc, hf, hg])⟩
  refine ⟨e, hf, fun j hj ↦ ?_⟩
  apply Iso.ext
  exact (cancel_mono N.inclusion).mp (hj.trans hf.symm)

private theorem split_of_trivial {G : AffineAlgebraicGroup k} (hu : IsUnipotent G)
    (h : Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) : IsSplitUnipotent G :=
  ⟨hu, 0, ⟨fun _ => G, Iso.refl _, h.some, fun _ => 𝟙 _,
    fun _ => inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩,
    fun i hi => (Nat.not_lt_zero i hi).elim⟩

private theorem split_extension_additive {G Q : AffineAlgebraicGroup k}
    (hu : IsUnipotent G) (q : G.val ⟶ Q.val)
    (i : (StandardGroups.additiveGroup k).val ⟶ G.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hq : IsFppfGroupQuotient ⟨_, i, hi⟩ q)
    (hQ : IsSplitUnipotent Q) : IsSplitUnipotent G := by
  let := hq.2.1
  let := hq.2.2.1
  let := hq.2.2.2.1
  obtain ⟨_, n, S, hS⟩ := hQ
  refine ⟨hu, n + 1, liftSeries q S, ?_⟩
  intro j hj
  by_cases hj' : j < n
  · obtain ⟨A, a, ha, hA⟩ := hS j hj'
    exact ⟨A, liftSeries_map q S j hj'.le ≫ a, liftSeries_factor q S hj' a ha, hA⟩
  · have he : j = n := by omega
    subst j
    obtain ⟨p, hp⟩ := liftSeries_last_factor q S i hi hq.1
    exact ⟨StandardGroups.additiveGroup k, p, hp, Or.inr ⟨StandardGroups.additiveGroupPointsIso k⟩⟩

private def trivialSubgroup (G : AffineAlgebraicGroup k) : ClosedSubgroup G.val :=
  ⟨(trivialAffine k).val, (default : Grp.trivial (SchemeOver k) ⟶ G.val),
    trivial_inclusion_closed G⟩

private theorem wound_case (G : AffineAlgebraicGroup k)
    (hu : IsUnipotent G) (hw : IsWound G.val) :
    IsLargestSplitSubgroup (U := G) (trivialSubgroup G) ∧
    IsFppfGroupQuotient (Q := G) (trivialSubgroup G) (𝟙 G.val) := by
  let H := trivialSubgroup G
  have hk : IsSchemeKernel (𝟙 G.val) H := by
    let := G.property.1
    apply schemeKernel_of_testPoints (𝟙 G.val)
    intro R x
    change (∃ y : Points H.group.X R, y ≫ H.inclusion.hom.hom = x) ↔ x ≫ 𝟙 G.val.X = 1
    rw [Category.comp_id]
    constructor
    · rintro ⟨y, rfl⟩
      exact trivial_map_eq_one (G := Grp.trivial _) ⟨Iso.refl _⟩ H.inclusion y
    · rintro rfl
      exact ⟨1, MonObj.one_comp _⟩
  refine ⟨largest_of_wound_quotient (𝟙 G.val) H hk ?_ ?_ ?_ hw,
    represented_quotient_of_kernel (𝟙 G.val) H hk ?_ ?_ ?_⟩
  · exact inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k))))
  · exact inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of k)))
  · exact split_of_trivial (closedSubgroupsUnipotent G H hu) ⟨Iso.refl _⟩
  · exact inferInstanceAs (Flat (𝟙 G.val.X.left))
  · exact inferInstanceAs (Surjective (𝟙 G.val.X.left))
  · exact inferInstanceAs (LocallyOfFinitePresentation (𝟙 G.val.X.left))

private theorem split_case (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom)
    (hc : ConnectedSpace G.val.X.left) (hu : IsSplitUnipotent G) :
    ∃ (H : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsLargestSplitSubgroup (U := G) H ∧ IsIso H.inclusion ∧
      IsFppfGroupQuotient H q ∧ Smooth Q.val.X.hom ∧ ConnectedSpace Q.val.X.left ∧
      IsUnipotent Q ∧ IsWound Q.val := by
  let H : ClosedSubgroup G.val := ⟨_, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 G.val.X.left))⟩
  let Q := trivialAffine k
  let q : G.val ⟶ Q.val := (default : G.val ⟶ Grp.trivial (SchemeOver k))
  have hq : q.hom.hom.left = G.val.X.hom := by
    change (_ : G.val.X.left ⟶ Spec (CommRingCat.of k)) = G.val.X.hom
    exact (Category.comp_id _).symm.trans q.hom.hom.w
  have hk : IsSchemeKernel q H := by
    let := G.property.1
    let := Q.property.1
    apply schemeKernel_of_testPoints q
    intro R x
    exact ⟨fun _ => sections_eq_one_of_trivial (G := Grp.trivial _) ⟨Iso.refl _⟩ _,
      fun _ => ⟨x, Category.comp_id _⟩⟩
  have hf : Flat q.hom.hom.left := by
    let : Smooth G.val.X.hom := hs
    exact hq.symm ▸ inferInstanceAs (Flat G.val.X.hom)
  have hj : Surjective q.hom.hom.left := by
    change Surjective (_ : G.val.X.left ⟶ Spec (CommRingCat.of k))
    constructor
    intro x
    exact ⟨groupIdentityPoint G.val, Subsingleton.elim _ _⟩
  have hp : LocallyOfFinitePresentation q.hom.hom.left := by
    let : Smooth G.val.X.hom := hs
    exact hq.symm ▸ inferInstanceAs (LocallyOfFinitePresentation G.val.X.hom)
  have hw : IsWound Q.val := wound_of_trivial ⟨Iso.refl _⟩
  exact ⟨H, Q, q, largest_of_wound_quotient q H hk hs hc hu hw, inferInstanceAs (IsIso (𝟙 G.val)),
    represented_quotient_of_kernel q H hk hf hj hp,
    inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of k)))),
    inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of k))),
    faithfullyFlatQuotientsUnipotent G Q q hf hj hu.1, hw⟩

private def baseChangePointsIso (K : Type u) [Field K] [Algebra k K] (G : GroupScheme k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅
      restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G :=
  NatIso.ofComponents
    (fun R => MulEquiv.toGrpIso
      (X := ((groupPointsFunctor K).obj ((groupBaseChange k K).obj G)).obj R)
      (Y := (restrictTestAlgebra k K ⋙ (groupPointsFunctor k).obj G).obj R)
      (baseChangePointGroupEquiv K G R))
    (by
      intro R S a
      apply GrpCat.ext
      intro z
      exact baseChangePointsNaturality k K G.X a z)

private def baseChangeAdditivePoints (K : Type u) [Field K] [Algebra k K]
    {G : GroupScheme k} (e : (groupPointsFunctor k).obj G ≅ Specs.StandardGroups.additivePoints k) :
    (groupPointsFunctor K).obj ((groupBaseChange k K).obj G) ≅ Specs.StandardGroups.additivePoints K :=
  baseChangePointsIso K G ≪≫ Functor.isoWhiskerLeft (restrictTestAlgebra k K) e ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; apply GrpCat.ext; intro z; rfl)

private def baseChangeTrivialIso (K : Type u) [Field K] [Algebra k K] :
    (groupBaseChange k K).obj (Grp.trivial (SchemeOver k)) ≅ Grp.trivial (SchemeOver K) :=
  Grp.mkIso (G := (groupBaseChange k K).obj (Grp.trivial (SchemeOver k)))
    (H := Grp.trivial (SchemeOver K)) (Functor.Monoidal.εIso (baseChange k K)).symm
    ((isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _)
    ((isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _)

private theorem baseChangeKernel (K : Type u) [Field K] [Algebra k K]
    {G Q : GroupScheme k} (q : G ⟶ Q) (N : ClosedSubgroup G) (hk : IsSchemeKernel q N) :
    ∃ h : IsClosedImmersion ((groupBaseChange k K).map N.inclusion).hom.hom.left,
      IsSchemeKernel ((groupBaseChange k K).map q)
        ⟨_, (groupBaseChange k K).map N.inclusion, h⟩ := by
  let F := baseChange k K
  have hc := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (baseChangeMapIsPullback K N.inclusion.hom.hom).flip N.isClosedImmersion
  refine ⟨hc, ?_⟩
  let e := Functor.Monoidal.εIso F
  refine (hk.map F).of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
    (by simp only [Iso.refl_hom]; rfl) ?_
    (by simp only [Iso.refl_hom]; rfl) ?_
  · apply (cancel_mono e.hom).mp
    simp [e, Functor.Monoidal.toUnit_ε]
  · change F.map η[Q.X] ≫ 𝟙 _ = e.inv ≫ e.hom ≫ F.map η[Q.X]
    simp

private theorem baseChangeGroupQuotient (K : Type u) [Field K] [Algebra k K]
    {G Q : AffineAlgebraicGroup k} (q : G.val ⟶ Q.val) (N : ClosedSubgroup G.val)
    (hq : IsFppfGroupQuotient N q)
    (hi : IsClosedImmersion ((groupBaseChange k K).map N.inclusion).hom.hom.left) :
    IsFppfGroupQuotient (G := baseChangedAlgebraicGroup K G) (Q := baseChangedAlgebraicGroup K Q)
      ⟨_, (groupBaseChange k K).map N.inclusion, hi⟩ ((groupBaseChange k K).map q) := by
  have pb := baseChangeMapIsPullback K q.hom.hom
  have hfp : LocallyOfFinitePresentation ((baseChange k K).map q.hom.hom).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) pb.flip hq.2.2.2.1
  exact represented_quotient_of_kernel (G := baseChangedAlgebraicGroup K G)
    (Q := baseChangedAlgebraicGroup K Q) ((groupBaseChange k K).map q) _
    (baseChangeKernel K q N hq.1).choose_spec
    (MorphismProperty.of_isPullback (P := @Flat) pb.flip hq.2.1)
    (MorphismProperty.of_isPullback (P := @Surjective) pb.flip hq.2.2.1) hfp

private theorem split_baseChange (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (hu : IsSplitUnipotent G) :
    IsSplitUnipotent (baseChangedAlgebraicGroup K G) := by
  obtain ⟨hG, n, S, hS⟩ := hu
  let F := groupBaseChange k K
  let C : ClosedSeries (baseChangedAlgebraicGroup K G) n :=
    ⟨fun i => baseChangedAlgebraicGroup K (S.term i),
      F.mapIso S.top, F.mapIso S.bottom ≪≫ baseChangeTrivialIso K,
      fun i => F.map (S.step i), fun i =>
        MorphismProperty.of_isPullback (P := @IsClosedImmersion)
          (baseChangeMapIsPullback K (S.step i).hom.hom).flip (S.closed i)⟩
  refine ⟨(unipotenceFieldExtension G).mpr hG, n, C, ?_⟩
  intro i hi
  obtain ⟨Q, q, hq, hQ⟩ := hS i hi
  refine ⟨baseChangedAlgebraicGroup K Q, F.map q,
    baseChangeGroupQuotient K q ⟨_, S.step i, S.closed i⟩ hq (C.closed i), ?_⟩
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨F.mapIso e ≪≫ baseChangeTrivialIso K⟩
  · exact Or.inr ⟨baseChangeAdditivePoints K e⟩

private theorem group_connected_baseChange (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (hc : ConnectedSpace G.val.X.left) :
    ConnectedSpace ((groupBaseChange k K).obj G.val).X.left := by
  obtain ⟨Q, H, q, i, hi, _, _, hh⟩ := identityComponentAndQuotient k G
  let := hc
  have he : Surjective i.hom.hom.left := by
    rw [surjective_iff, ← Set.range_eq_univ, hi.identityComponent, PreconnectedSpace.connectedComponent_eq_univ]
  let f := groupBaseChange k K
  let := (hh K).geometricallyConnected
  have hconn : ConnectedSpace (f.obj H).X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := (f.obj H).X.hom)
  let := hconn
  have : Surjective (f.map i).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective) (baseChangeMapIsPullback K i.hom.hom).flip he
  exact (Surjective.surj (f := (f.map i).hom.hom.left)).connectedSpace
    (f.map i).hom.hom.left.continuous

theorem canonicalSplitSubgroupBaseChange : CanonicalSplitSubgroupBaseChange.{u} := by
  intro k _ U H Q q hH hq hQs hQc hQu hw K _ _ _
  obtain ⟨hc, hk⟩ := baseChangeKernel K q H hq.1
  refine ⟨hc, largest_of_wound_quotient (G := baseChangedAlgebraicGroup K U)
    (Q := baseChangedAlgebraicGroup K Q) ((groupBaseChange k K).map q) _ hk ?_ ?_ ?_ ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback H.group.X.hom (fieldSpecMap k K)) hH.1
  · exact group_connected_baseChange K (closedSubgroupAlgebraicGroup H) hH.2.1
  · exact split_baseChange K (closedSubgroupAlgebraicGroup H) hH.2.2.1
  · exact woundSeparableExtension Q hQs hQc hQu hw K

private theorem additive_smooth (k : Type u) [Field k] :
    Smooth (StandardGroups.additiveGroup k).val.X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))))
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr
    ⟨inferInstance, (Algebra.FinitePresentation.of_finiteType).mp inferInstance⟩)

private theorem additive_connected (k : Type u) [Field k] :
    ConnectedSpace (StandardGroups.additiveGroup k).val.X.left :=
  inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of (Polynomial k))))

private theorem additive_geometricallyConnected (k : Type u) [Field k] :
    GeometricallyConnected (StandardGroups.additiveGroup k).val.X.hom := by
  refine ⟨(geometrically_iff_of_isClosedUnderIsomorphisms (P := fun Z ↦ ConnectedSpace Z)).mpr ?_⟩
  intro K _ b
  let : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hb : fieldSpecMap k K = b := Spec.map_preimage b
  rw [← hb]
  exact group_connected_baseChange K (StandardGroups.additiveGroup k) (additive_connected k)

private theorem quotient_by_additive (G : AffineAlgebraicGroup k)
    (i : (StandardGroups.additiveGroup k).val ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hc : IsCentralIn i) :
    ∃ (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, i, hi⟩ q ∧ Smooth q.hom.hom.left ∧
      GeometricallyConnected q.hom.hom.left := by
  let A := StandardGroups.additiveGroup k
  let D : ClosedSubgroup G.val := ⟨A.val, i, hi⟩
  obtain ⟨⟨B⟩, hB⟩ := HomogeneousQuotient.homogeneousQuotient k G D
  obtain ⟨_, Q, _, q, _, e, _, hker, hfac, _, he⟩ :=
    HomogeneousQuotient.quotientAffineComparison G D B (central_normal hc)
  have he' : B.projection.left ≫ e.hom.left = q.hom.hom.left := congrArg Over.Hom.left he
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  refine ⟨Q, q, represented_quotient_of_kernel q D hker hfac.2.1 hfac.2.2.1 hfac.2.2.2.1, ?_, ?_⟩
  · rw [← he']
    let : Smooth B.projection.left := (hB B).2 (additive_smooth k)
    infer_instance
  · rw [← he', MorphismProperty.cancel_right_of_respectsIso (P := @GeometricallyConnected)]
    have hp : IsPullback (prod.fst : G.val.X ⨯ D.group.X ⟶ G.val.X).left
        (Specs.HomogeneousQuotient.rightMultiplication D).left B.projection.left B.projection.left :=
      (HomogeneousQuotient.quotientPullback B).map (Over.forget _)
    have hpb : IsPullback (prod.fst : G.val.X ⨯ D.group.X ⟶ G.val.X).left
        (prod.snd : G.val.X ⨯ D.group.X ⟶ D.group.X).left G.val.X.hom D.group.X.hom :=
      Over.isPullback_of_binaryFan_isLimit
        (BinaryFan.mk (prod.fst : G.val.X ⨯ D.group.X ⟶ G.val.X) prod.snd) (prodIsProd _ _)
    have hgeo : GeometricallyConnected (prod.fst : G.val.X ⨯ D.group.X ⟶ G.val.X).left :=
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.flip (additive_geometricallyConnected k)
    let : Surjective B.projection.left := B.surjective
    let : GeometricallyConnected (pullback.snd B.projection.left B.projection.left) := by
      rw [← MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyConnected)
            hp.flip.isoPullback.hom, hp.flip.isoPullback_hom_snd]
      exact hgeo
    exact geometricallyConnectedOfSurjectiveBaseChange B.projection.left B.projection.left

private theorem lift_split_subgroup {G Q R : AffineAlgebraicGroup k}
    (hu : IsUnipotent G)
    (q : G.val ⟶ Q.val)
    (i : (StandardGroups.additiveGroup k).val ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hq : IsFppfGroupQuotient ⟨_, i, hi⟩ q)
    (hs : Smooth q.hom.hom.left) (hc : GeometricallyConnected q.hom.hom.left)
    (B : ClosedSubgroup Q.val) (hB : IsLargestSplitSubgroup (U := Q) B)
    (r : Q.val ⟶ R.val) (hr : IsFppfGroupQuotient B r) (hw : IsWound R.val) :
    ∃ (H : ClosedSubgroup G.val),
      IsLargestSplitSubgroup (U := G) H ∧ IsFppfGroupQuotient H (q ≫ r) := by
  let A := StandardGroups.additiveGroup k
  let X := pullback q B.inclusion
  let j : X ⟶ G.val := pullback.fst _ _
  let s : X ⟶ B.group := pullback.snd _ _
  have hpb : IsPullback j.hom.hom s.hom.hom q.hom.hom B.inclusion.hom.hom :=
    (Grp.forget _).map_isPullback (.of_hasPullback _ _)
  have hpb' := hpb.map (Over.forget _)
  have hj : IsClosedImmersion j.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb'.flip B.isClosedImmersion
  let H : ClosedSubgroup G.val := ⟨X, j, hj⟩
  let P := closedSubgroupAlgebraicGroup H
  have hk : IsSchemeKernel (q ≫ r) H := by
    change IsPullback j.hom.hom (toUnit X.X) (q.hom.hom ≫ r.hom.hom) η[R.val.X]
    simpa only [comp_toUnit] using hpb.paste_vert hr.1
  let Z := closedSubgroupAlgebraicGroup B
  let z : A.val ⟶ B.group := (default : A.val ⟶ Grp.trivial _) ≫ default
  have hz : z.hom.hom = 1 := by
    change _ ≫ _ = _
    rw [trivial_map_eq_one ⟨Iso.refl _⟩]
  have hiq : i.hom.hom ≫ q.hom.hom = 1 :=
    (schemeKernel_sections hq.1 i.hom.hom).mp
      ⟨𝟙 A.val.X, show 𝟙 A.val.X ≫ i.hom.hom = i.hom.hom from Category.id_comp _⟩
  have hiz : i ≫ q = z ≫ B.inclusion := by
    apply Grp.hom_ext
    change i.hom.hom ≫ q.hom.hom = z.hom.hom ≫ B.inclusion.hom.hom
    rw [hiq, hz, MonObj.one_comp]
  let t : A.val ⟶ X := pullback.lift i z hiz
  have htj : t.hom.hom ≫ j.hom.hom = i.hom.hom :=
    congrArg (fun f => f.hom.hom) (pullback.lift_fst i z hiz)
  have ht : IsClosedImmersion t.hom.hom.left := by
    refine @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ _ _ hj ?_
    change IsClosedImmersion (t.hom.hom ≫ j.hom.hom).left
    rwa [htj]
  have hts : t.hom.hom ≫ s.hom.hom = 1 :=
    (congrArg (fun f => f.hom.hom) (pullback.lift_snd i z hiz)).trans hz
  have hk' : IsSchemeKernel s ⟨A.val, t, ht⟩ := by
    -- The two pullbacks describe the preimage of B and the kernel of q.
    have houter : IsPullback (t.hom.hom ≫ j.hom.hom) (toUnit A.val.X) q.hom.hom
        (η[B.group.X] ≫ B.inclusion.hom.hom) := by
      rw [htj, IsMonHom.one_hom]
      exact hq.1
    exact IsPullback.of_right houter hts hpb
  have hsf : Flat s.hom.hom.left := MorphismProperty.of_isPullback (P := @Flat) hpb' hq.2.1
  have hss : Surjective s.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb' hq.2.2.1
  have hsp : LocallyOfFinitePresentation s.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb' hq.2.2.2.1
  let hsm : Smooth s.hom.hom.left := MorphismProperty.of_isPullback (P := @Smooth) hpb' hs
  let hgeo : GeometricallyConnected s.hom.hom.left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb' hc
  let hBs : Smooth B.group.X.hom := hB.1
  let hBc : ConnectedSpace B.group.X.left := hB.2.1
  have hPs : Smooth P.val.X.hom := by
    change Smooth X.X.hom
    exact s.hom.hom.w ▸ MorphismProperty.comp_mem @Smooth _ _ hsm hBs
  have hPc : ConnectedSpace P.val.X.left :=
    @GeometricallyConnected.connectedSpace _ _ s.hom.hom.left hgeo hBc s.hom.hom.left.isOpenMap
  have hq' : IsFppfGroupQuotient (G := P) (Q := Z) ⟨A.val, t, ht⟩ s :=
    represented_quotient_of_kernel (G := P) (Q := Z) s _ hk' hsf hss hsp
  have hsplit : IsSplitUnipotent P :=
    split_extension_additive (closedSubgroupsUnipotent G H hu) (Q := Z) s t ht hq' hB.2.2.1
  exact ⟨H, largest_of_wound_quotient (q ≫ r) H hk hPs hPc hsplit hw,
    represented_quotient_of_kernel (q ≫ r) H hk
      (MorphismProperty.comp_mem @Flat _ _ hq.2.1 hr.2.1)
      (MorphismProperty.comp_mem @Surjective _ _ hq.2.2.1 hr.2.2.1)
      (MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ hq.2.2.2.1 hr.2.2.2.1)⟩

theorem canonicalSplitSubgroup : CanonicalSplitSubgroup.{u} := by
  intro k _ G
  suffices hall : ∀ d : ℕ, ∀ G : AffineAlgebraicGroup k, identityDimension G = d →
      Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G →
      ∃ (H : ClosedSubgroup G.val) (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val),
        IsLargestSplitSubgroup (U := G) H ∧ IsNormalSubgroup H.inclusion ∧
        IsFppfGroupQuotient H q ∧ Smooth Q.val.X.hom ∧ ConnectedSpace Q.val.X.left ∧
        IsUnipotent Q ∧ IsWound Q.val from hall (identityDimension G) G rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro G hdim hs hc hu
    classical
    rcases CharP.exists' k with h₀ | ⟨p, hp, hkp⟩
    · obtain ⟨H, Q, q, hH, _, hq, hQs, hQc, hQu, hw⟩ :=
        split_case G hs hc (perfectFieldIsSplitUnipotent G hs hc hu)
      exact ⟨H, Q, q, hH, normal_of_schemeKernel q H hq.1, hq, hQs, hQc, hQu, hw⟩
    by_cases hw : IsWound G.val
    · obtain ⟨hH, hq⟩ := wound_case G hu hw
      exact ⟨trivialSubgroup G, G, 𝟙 _, hH, normal_of_schemeKernel _ _ hq.1, hq, hs, hc, hu, hw⟩
    obtain ⟨i, hi, hcent⟩ := central_additive_of_nonwound p G hs hc hu hw
    obtain ⟨Q, q, hq, hqS, hqC⟩ := quotient_by_additive G i hi hcent
    let := hq.2.1
    have hlt : identityDimension Q < d := hdim ▸ identityDimension_lt q i hi hq.1
    obtain ⟨hQs, hQc⟩ := smoothConnected_quotient q hq.2.1 hq.2.2.1 hs hc
    have hQu := faithfullyFlatQuotientsUnipotent G Q q hq.2.1 hq.2.2.1 hu
    obtain ⟨B, R, r, hB, _, hr, hRs, hRc, hRu, hRw⟩ :=
      ih _ hlt Q rfl hQs hQc hQu
    obtain ⟨H, hH, hHq⟩ := lift_split_subgroup hu q i hi hq hqS hqC B hB r hr hRw
    exact ⟨H, R, q ≫ r, hH, normal_of_schemeKernel _ _ hHq.1, hHq, hRs, hRc, hRu, hRw⟩

open private operations additiveRepresentation from LinearAlgebraicGroups.Affine.StandardGroups

private def primitivePolynomialGroupIso
    (l : Specs.StandardGroups.HopfOperations k (Polynomial k))
    (h : Specs.WoundExample.Primitive k l Polynomial.X) :
    letI := l.hopf
    (Specs.StandardGroups.spectrum k (Polynomial k)).val ≅ (StandardGroups.additiveGroup k).val := by
  let S := operations (additiveRepresentation k)
  have hSΔ : S.delta Polynomial.X = Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X := by
    exact Polynomial.aeval_X _
  have hSε : S.epsilon Polynomial.X = 0 := Polynomial.aeval_X _
  have hε : l.epsilon = S.epsilon := Polynomial.algHom_ext (h.2.1.trans hSε.symm)
  have hΔ : l.delta = S.delta := Polynomial.algHom_ext (h.1.trans hSΔ.symm)
  let A := @CommHopfAlgCat.of k _ (Polynomial k) _ l.hopf
  let B := @CommHopfAlgCat.of k _ (Polynomial k) _ (StandardGroups.additiveHopf k)
  have e : A ≅ B := by
    refine @CommHopfAlgCat.isoMk k _ (Polynomial k) (Polynomial k) _ _
      l.hopf (StandardGroups.additiveHopf k) ?_
    refine @BialgEquiv.ofAlgEquiv k (Polynomial k) (Polynomial k) _ _ _
      l.hopf.toHopfAlgebraStruct.toBialgebra
      (StandardGroups.additiveHopf k).toHopfAlgebraStruct.toBialgebra (AlgEquiv.refl) ?_ ?_
    · change S.epsilon.comp (AlgHom.id k _) = l.epsilon
      simpa using hε.symm
    · change (Algebra.TensorProduct.map (AlgHom.id k _) (AlgHom.id k _)).comp l.delta =
        S.delta.comp (AlgHom.id k _)
      simpa using hΔ
  exact (hopfSpec (CommRingCat.of k)).mapIso e.symm.op

private theorem split_of_additive_iso {G : AffineAlgebraicGroup k}
    (j : (StandardGroups.additiveGroup k).val ≅ G.val)
    (hu : IsUnipotent G) (hs : Smooth G.val.X.hom) : IsSplitUnipotent G := by
  let Q := trivialAffine k
  let q : G.val ⟶ Q.val := (default : G.val ⟶ Grp.trivial (SchemeOver k))
  let i := j.hom
  let hi : IsClosedImmersion i.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion ((schemeForget k).map j.hom))
  let H : ClosedSubgroup G.val := ⟨_, i, hi⟩
  have hq : q.hom.hom.left = G.val.X.hom := by
    change (_ : G.val.X.left ⟶ Spec (CommRingCat.of k)) = G.val.X.hom
    exact (Category.comp_id _).symm.trans q.hom.hom.w
  have hk : IsSchemeKernel q H := by
    let := G.property.1
    let := Q.property.1
    apply schemeKernel_of_testPoints q
    intro R x
    refine ⟨fun _ => sections_eq_one_of_trivial (G := Grp.trivial _) ⟨Iso.refl _⟩ _, fun _ => ?_⟩
    refine ⟨x ≫ j.inv.hom.hom, ?_⟩
    have he : j.inv.hom.hom ≫ j.hom.hom.hom = 𝟙 G.val.X :=
      congrArg (fun f : G.val ⟶ G.val => f.hom.hom) j.inv_hom_id
    change (x ≫ j.inv.hom.hom) ≫ j.hom.hom.hom = x
    rw [Category.assoc, he, Category.comp_id]
  have hf : Flat q.hom.hom.left := by
    let : Smooth G.val.X.hom := hs
    exact hq.symm ▸ inferInstanceAs (Flat G.val.X.hom)
  have hj : Surjective q.hom.hom.left := by
    change Surjective (_ : G.val.X.left ⟶ Spec (CommRingCat.of k))
    constructor
    intro x
    exact ⟨groupIdentityPoint G.val, Subsingleton.elim _ _⟩
  have hp : LocallyOfFinitePresentation q.hom.hom.left := by
    let : Smooth G.val.X.hom := hs
    exact hq.symm ▸ inferInstanceAs (LocallyOfFinitePresentation G.val.X.hom)
  exact split_extension_additive hu q i hi (represented_quotient_of_kernel q H hk hf hj hp)
    (split_of_trivial (faithfullyFlatQuotientsUnipotent G Q q hf hj hu) ⟨Iso.refl _⟩)

theorem woundExampleSplitEnlargement : WoundExampleSplitEnlargement.{u} := by
  intro k _ p _ _ c hc
  obtain ⟨h, hprim, hI, _, hs, hg, hu, _, ⟨d, hd, d', hd', hb⟩, hw, _⟩ :=
    WoundExample.woundSubgroup k p c hc
  let := h.hopf
  let := hI
  let W := Specs.StandardGroups.spectrum k (Specs.WoundExample.Coordinates k p c)
  let K := IntermediateField.adjoin k ({d} : Set (AlgebraicClosure k))
  let V := baseChangedAlgebraicGroup K W
  have hcW : ConnectedSpace W.val.X.left :=
    @GeometricallyConnected.connectedSpace_of_subsingleton _ _ W.val.X.hom hg _ _
  have hw' : IsWound W.val := by
    intro a ha
    obtain ⟨b, hb₀⟩ := hw a
    have he := congrArg (fun f : AffineLineCurve W.val => curveAtZero f) hb₀
    have hb₁ : curveAtZero (constantCurve b) = b := origin_constant b
    exact ha (hb₀.trans (congrArg constantCurve (he.trans hb₁).symm))
  let H := trivialSubgroup W
  have hH := (wound_case W hu hw').1
  obtain ⟨l, hl, _, _, _, _, ⟨e⟩⟩ := hb
  let j : (StandardGroups.additiveGroup K).val ≅ V.val :=
    (e ≪≫ primitivePolynomialGroupIso l hl).symm
  have hsV : Smooth V.val.X.hom :=
    MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback W.val.X.hom (fieldSpecMap k K)) hs
  have hcV := group_connected_baseChange K W hcW
  have huV : IsUnipotent V := (unipotenceFieldExtension W).mpr hu
  have hx : IsSplitUnipotent V := split_of_additive_iso j huV hsV
  obtain ⟨N, _, _, hN, hni, _⟩ := split_case V hsV hcV hx
  have hnontrivial : ¬ Nonempty (N.group ≅ Grp.trivial (SchemeOver K)) := by
    intro ht
    exact (wound_of_trivial ⟨j ≪≫ (asIso N.inclusion).symm ≪≫ ht.some⟩ _)
      (additiveCurve_nonconstant K)
  refine ⟨h, hprim, hI, H, d, hd, ?_, N, hH, ⟨Iso.refl _⟩, hN, hni, hnontrivial, ?_⟩
  · apply (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem
      k (AlgebraicClosure k) p).mpr
    exact ⟨1, c, by simpa only [pow_one] using hd.symm⟩
  · intro hHi
    let : IsIso ((groupBaseChange k K).map H.inclusion) := hHi
    exact hnontrivial ⟨asIso N.inclusion ≪≫
      (asIso ((groupBaseChange k K).map H.inclusion)).symm ≪≫ baseChangeTrivialIso K⟩

end

end LinearAlgebraicGroups.Unipotent
