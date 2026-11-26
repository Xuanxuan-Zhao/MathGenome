import Specs.LinearAlgebraicGroups.Unipotent.SplitFieldExtensions
import LinearAlgebraicGroups.Unipotent.CanonicalSplitSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Unipotent

open _root_.LinearAlgebraicGroups.Specs _root_.LinearAlgebraicGroups.Specs.Unipotent

noncomputable section

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {k : Type u} [Field k]

open private isReduced_of_smooth_over_field identitySection_comp
  from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private group_connected_baseChange baseChangeTrivialIso central_additive_of_nonwound
  quotient_by_additive smoothConnected_quotient split_extension_additive split_of_trivial
  split_baseChange no_additive_of_wound baseChangeKernel baseChangeGroupQuotient baseChangeAdditivePoints
  from LinearAlgebraicGroups.Unipotent.CanonicalSplitSubgroup
open private identityDimension identityDimension_lt exists_central_additive_charP
  trivial_inclusion_closed represented_quotient_of_kernel
  sections_eq_one_of_trivial
  from LinearAlgebraicGroups.Unipotent.PerfectFieldSplitness
open private curveCoordinates curveCoordinates_isNonconstant finiteType_of_affine_coordinates
  lift_polynomial_coefficients from LinearAlgebraicGroups.Unipotent.CentralKilledByPCurves
open private groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.PerfectFieldVectorGroups
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private closed_surjective_points_iso scheme_kernel_of_iso
  from LinearAlgebraicGroups.Unipotent.CentralSeries

private theorem split_of_groupIso {G H : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) (hG : IsSplitUnipotent G) : IsSplitUnipotent H := by
  have hi : IsClosedImmersion e.inv.hom.hom.left :=
    inferInstanceAs (IsClosedImmersion (((Grp.forget (SchemeOver k)) ⋙
      Over.forget (Spec (CommRingCat.of k))).map e.inv))
  obtain ⟨hu, n, S, hS⟩ := hG
  exact ⟨closedSubgroupsUnipotent G ⟨H.val, e.inv, hi⟩ hu, n,
    ⟨S.term, S.top ≪≫ e, S.bottom, S.step, S.closed⟩, hS⟩

private theorem smooth_baseChanged (K : Type u) [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) :
    Smooth (baseChangedAlgebraicGroup K G).val.X.hom :=
  MorphismProperty.of_isPullback (P := @Smooth)
    (IsPullback.of_hasPullback G.val.X.hom (fieldSpecMap k K)) hs

private theorem closed_iso_of_baseChange_surjective {A G : GroupScheme k}
    (i : A ⟶ G) (hi : IsClosedImmersion i.hom.hom.left) (hr : IsReduced G.X.left)
    (K : Type u) [Field K] [Algebra k K]
    (hs : Surjective ((groupBaseChange k K).map i).hom.hom.left) : IsIso i := by
  let F := groupBaseChange k K
  let p := pullback.fst G.X.hom (fieldSpecMap k K)
  let pA := pullback.fst A.X.hom (fieldSpecMap k K)
  have hp : Surjective p := MorphismProperty.pullback_fst _ _ (by infer_instance)
  have hcomm : (F.map i).hom.hom.left ≫ p = pA ≫ i.hom.hom.left := by
    change ((baseChange k K).map i.hom.hom).left ≫ p = _
    exact pullback.lift_fst _ _ _
  have hsurj : Surjective ((F.map i).hom.hom.left ≫ p) := ⟨hp.surj.comp hs.surj⟩
  have : Surjective (pA ≫ i.hom.hom.left) := hcomm ▸ hsurj
  let : Surjective i.hom.hom.left := Surjective.of_comp pA _
  let : IsIso ((Over.forget _).map i.hom.hom) :=
    isIso_of_isClosedImmersion_of_surjective i.hom.hom.left
  let : IsIso i.hom.hom := isIso_of_reflects_iso i.hom.hom (Over.forget _)
  let e : A ≅ G := Grp.mkIso' (asIso i.hom.hom)
  have he : e.hom = i := by apply Grp.hom_ext; rfl
  rw [← he]
  infer_instance

/-- Over a perfect field the smooth connected unipotent groups are split. -/
theorem splitUnipotentOverPerfectField : PerfectFieldIsSplitUnipotent.{u} :=
  perfectFieldIsSplitUnipotent

theorem separableSplitnessDescent : SeparableSplitnessDescent.{u} := by
  intro k _ G hs hc hu K _ _ _ hGK
  obtain ⟨H, Q, q, hH, _, hq, hQs, hQc, hQu, hQw⟩ := canonicalSplitSubgroup G hs hc hu
  obtain ⟨hi, hHK⟩ := canonicalSplitSubgroupBaseChange G H Q q hH hq hQs hQc hQu hQw K
  let GK := baseChangedAlgebraicGroup K G
  let I : ClosedSubgroup GK.val := ⟨_, 𝟙 _, inferInstanceAs (IsClosedImmersion (𝟙 GK.val.X.left))⟩
  obtain ⟨j, hj⟩ := hHK.2.2.2 I hGK
  have hsurj : Surjective ((groupBaseChange k K).map H.inclusion).hom.hom.left := by
    constructor
    intro x
    exact ⟨j.hom.hom.left x, congrArg (fun f : GK.val ⟶ GK.val => f.hom.hom.left x) hj⟩
  let := hs
  have hiso : IsIso H.inclusion := closed_iso_of_baseChange_surjective H.inclusion H.isClosedImmersion
    (isReduced_of_smooth_over_field G.val.X.hom) K hsurj
  exact split_of_groupIso (G := closedSubgroupAlgebraicGroup H)
    (@asIso _ _ _ _ H.inclusion hiso) hH.2.2.1

private theorem exists_finite_curve (L : Type u) [Field L] [Algebra k L]
    [IsPurelyInseparable k L] (G : AffineAlgebraicGroup k)
    (x : AffineLineCurve ((groupBaseChange k L).obj G.val)) (hx : IsNonconstantCurve x) :
    ∃ (K : IntermediateField k L) (_ : FiniteDimensional k K),
      ∃ y : AffineLineCurve ((groupBaseChange k K).obj G.val), IsNonconstantCurve y := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr G.property.1
  have : Algebra.FiniteType k A.unop := finiteType_of_affine_coordinates e G.property.2.1
  obtain ⟨a, n, hn, hc⟩ := (curveCoordinates_isNonconstant L e x).mp hx
  obtain ⟨s, g, hg⟩ := lift_polynomial_coefficients (curveCoordinates L e x)
  let K := IntermediateField.adjoin k (s : Set L)
  have hK : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  let B := Algebra.adjoin k (s : Set L)
  let i : B →ₐ[k] K := Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin k _)
  let f : A.unop →ₐ[k] Polynomial K := (Polynomial.mapAlgHom i).comp g
  have hfi : (Polynomial.mapAlgHom K.val).comp f = curveCoordinates L e x := by
    have hcomp : (Polynomial.mapAlgHom K.val).comp (Polynomial.mapAlgHom i) =
        Polynomial.mapAlgHom B.val := Polynomial.mapAlgHom_comp _ _ _
    rw [show f = (Polynomial.mapAlgHom i).comp g from rfl, ← AlgHom.comp_assoc, hcomp, hg]
  let y : AffineLineCurve ((groupBaseChange k K).obj G.val) := (curveCoordinates K e).symm f
  refine ⟨K, hK, y, (curveCoordinates_isNonconstant K e y).mpr ⟨a, n, hn, ?_⟩⟩
  rw [show curveCoordinates K e y = f from Equiv.apply_symm_apply _ _]
  rw [← hfi, AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply] at hc
  exact fun h => hc (by rw [h, map_zero])

private def groupBaseChangeTower (K L : Type u) [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L] :
    groupBaseChange k L ≅ groupBaseChange k K ⋙ groupBaseChange K L := by
  have he : fieldSpecMap k L = fieldSpecMap K L ≫ fieldSpecMap k K := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq k K L))
  let e : baseChange k L ≅ baseChange k K ⋙ baseChange K L :=
    eqToIso (congrArg (fun f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k) =>
      Over.pullback f) he) ≪≫ Over.pullbackComp _ _
  exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpCompIso


private theorem fieldSpecMap_universallyInjective (K : Type u) [Field K] [Algebra k K]
    [IsPurelyInseparable k K] : UniversallyInjective (fieldSpecMap k K) := by
  apply ((tfae_universallyInjective (fieldSpecMap k K)).out 1 2).mpr
  intro L _ f g hfg
  apply Spec.preimage_injective
  apply CommRingCat.hom_ext
  apply IsPurelyInseparable.injective_comp_algebraMap k K L
  have h := congrArg Spec.preimage hfg
  rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at h
  exact congrArg CommRingCat.Hom.hom h

private theorem baseChange_identityPoint (K : Type u) [Field K] [Algebra k K] (G : GroupScheme k) :
    pullback.fst G.X.hom (fieldSpecMap k K) (groupIdentityPoint ((groupBaseChange k K).obj G)) =
      groupIdentityPoint G := by
  have h := congrArg (fun f : Spec (CommRingCat.of K) ⟶ G.X.left =>
    f (IsLocalRing.closedPoint K)) (identitySection_comp (K := K) G)
  change pullback.fst G.X.hom (fieldSpecMap k K) (groupIdentityPoint ((groupBaseChange k K).obj G)) =
    groupIdentitySection G (fieldSpecMap k K (IsLocalRing.closedPoint K)) at h
  rw [Subsingleton.elim (fieldSpecMap k K (IsLocalRing.closedPoint K))
    (IsLocalRing.closedPoint k)] at h
  exact h

attribute [local instance] specializationOrder

private theorem identityDimension_baseChange (K : Type u) [Field K] [Algebra k K]
    [IsPurelyInseparable k K] (G : AffineAlgebraicGroup k) :
    identityDimension (baseChangedAlgebraicGroup K G) = identityDimension G := by
  let f := fieldSpecMap k K
  let p := pullback.fst G.val.X.hom f
  have hfi : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr inferInstance)
  have hfr : UniversallyInjective f := fieldSpecMap_universallyInjective K
  let : IsIntegralHom p := MorphismProperty.pullback_fst _ _ hfi
  let : UniversallyInjective p := MorphismProperty.pullback_fst _ _ hfr
  let : Surjective p := MorphismProperty.pullback_fst _ _ (by infer_instance)
  let e := (Equiv.ofBijective p ⟨p.injective, p.surjective⟩).toHomeomorphOfContinuousClosed
    p.continuous p.isClosedMap
  let o : (baseChangedAlgebraicGroup K G).val.X.left ≃o G.val.X.left :=
    { e.toEquiv with map_rel_iff' := fun {a b} => e.isEmbedding.isInducing.specializes_iff }
  unfold identityDimension
  rw [← Order.coheight_orderIso o (groupIdentityPoint (baseChangedAlgebraicGroup K G).val)]
  change (Order.coheight (p (groupIdentityPoint ((groupBaseChange k K).obj G.val)))).toNat = _
  rw [baseChange_identityPoint]

private theorem nonwound_over_perfectClosure (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hu : IsUnipotent G) (ht : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) :
    ¬ IsWound (baseChangedAlgebraicGroup (perfectClosure k (AlgebraicClosure k)) G).val := by
  let L := perfectClosure k (AlgebraicClosure k)
  let V := baseChangedAlgebraicGroup L G
  let : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  let := hs
  have hVt : ¬ Nonempty (V.val ≅ Grp.trivial (SchemeOver L)) := by
    rintro ⟨e⟩
    let j : Grp.trivial (SchemeOver k) ⟶ G.val := default
    let F := groupBaseChange k L
    have he : IsIso (F.map j) := by
      let i := baseChangeTrivialIso (k := k) L ≪≫ e.symm
      have eq : F.map j = i.hom := (cancel_mono e.hom).mp (Subsingleton.elim _ _)
      rw [eq]
      infer_instance
    have hj := closed_iso_of_baseChange_surjective j (trivial_inclusion_closed G)
      (isReduced_of_smooth_over_field G.val.X.hom) L
      (inferInstanceAs (Surjective (((Grp.forget _) ⋙ Over.forget _).map (F.map j))))
    exact ht ⟨(@asIso _ _ _ _ j hj).symm⟩
  obtain ⟨i, hi, _⟩ := exists_central_additive_charP (p := p) V
    ((unipotenceFieldExtension G).mpr hu) (smooth_baseChanged L G hs)
    (group_connected_baseChange L G hc) hVt
  intro hw
  exact no_additive_of_wound hw ⟨_, i, hi⟩ (StandardGroups.additiveGroupPointsIso L)

private theorem exists_finite_nonwound (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : AffineAlgebraicGroup k) (hs : Smooth G.val.X.hom) (hc : ConnectedSpace G.val.X.left)
    (hu : IsUnipotent G) (ht : ¬ Nonempty (G.val ≅ Grp.trivial (SchemeOver k))) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧
      IsPurelyInseparable k K ∧ ¬ IsWound (baseChangedAlgebraicGroup K G).val := by
  classical
  let L := perfectClosure k (AlgebraicClosure k)
  have hw := nonwound_over_perfectClosure p G hs hc hu ht
  change ¬ (∀ x : AffineLineCurve ((groupBaseChange k L).obj G.val), ¬ IsNonconstantCurve x) at hw
  obtain ⟨x, hx⟩ := not_forall.mp hw
  obtain ⟨K, hK, y, hy⟩ := exists_finite_curve L G x (not_not.mp hx)
  exact ⟨K, inferInstance, inferInstance, hK, inferInstance, fun h => h y hy⟩

private theorem split_baseChange_of_additive_extension (L : Type u) [Field L] [Algebra k L]
    {V Q : AffineAlgebraicGroup k} (hVu : IsUnipotent V)
    (q : V.val ⟶ Q.val) (i : (StandardGroups.additiveGroup k).val ⟶ V.val)
    (hi : IsClosedImmersion i.hom.hom.left) (hq : IsFppfGroupQuotient ⟨_, i, hi⟩ q)
    (hsplit : IsSplitUnipotent (baseChangedAlgebraicGroup L Q)) :
    IsSplitUnipotent (baseChangedAlgebraicGroup L V) := by
  let F := groupBaseChange k L
  let W := baseChangedAlgebraicGroup L V
  let A := StandardGroups.additiveGroup k
  let e : (StandardGroups.additiveGroup L).val ≅ F.obj A.val :=
    groupIsoOfPoints (StandardGroups.additiveGroup L).property.1
      (baseChangedAlgebraicGroup L A).property.1
      (StandardGroups.additiveGroupPointsIso L ≪≫
        (baseChangeAdditivePoints L (StandardGroups.additiveGroupPointsIso k)).symm)
  obtain ⟨hic, hik⟩ := baseChangeKernel L q ⟨_, i, hi⟩ hq.1
  have hclosed : IsClosedImmersion (e.hom ≫ F.map i).hom.hom.left := by
    let T := Grp.forget (SchemeOver L) ⋙ Over.forget (Spec (CommRingCat.of L))
    let : IsClosedImmersion (T.map (F.map i)) := hic
    change IsClosedImmersion (T.map e.hom ≫ T.map (F.map i))
    infer_instance
  have hQbc := baseChangeGroupQuotient (G := V) (Q := Q) L q ⟨_, i, hi⟩ hq hic
  have hker := scheme_kernel_of_iso (A := W) (B := StandardGroups.additiveGroup L)
    (C := baseChangedAlgebraicGroup L Q) (F.map q) (e.hom ≫ F.map i) hclosed
    ⟨_, F.map i, hic⟩ hik e rfl
  have hquot := represented_quotient_of_kernel (G := W) (Q := baseChangedAlgebraicGroup L Q)
    (F.map q) ⟨_, e.hom ≫ F.map i, hclosed⟩ hker hQbc.2.1 hQbc.2.2.1 hQbc.2.2.2.1
  exact split_extension_additive (G := W) (Q := baseChangedAlgebraicGroup L Q)
    ((unipotenceFieldExtension V).mpr hVu) (F.map q) _ hclosed hquot hsplit

theorem finitePurelyInseparableSplitness : FinitePurelyInseparableSplitness.{u} := by
  suffices h : ∀ d : ℕ, ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
      identityDimension G = d → Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsUnipotent G →
        ∃ (K : Type u) (_ : Field K) (_ : Algebra k K), FiniteDimensional k K ∧
          IsPurelyInseparable k K ∧ IsSplitUnipotent (baseChangedAlgebraicGroup K G) by
    intro k _ G hs hc hu
    exact h _ G rfl hs hc hu
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k _ G hd hs hc hu
    classical
    rcases CharP.exists' k with h₀ | ⟨p, hp, hkp⟩
    · exact ⟨k, inferInstance, inferInstance, inferInstance, inferInstance,
        split_baseChange k G (perfectFieldIsSplitUnipotent G hs hc hu)⟩
    by_cases ht : Nonempty (G.val ≅ Grp.trivial (SchemeOver k))
    · exact ⟨k, inferInstance, inferInstance, inferInstance, inferInstance,
        split_baseChange k G (split_of_trivial hu ht)⟩
    -- Descend a curve from the perfect closure and take a central additive subgroup.
    obtain ⟨K, hKF, hKA, hKf, hKp, hw⟩ := exists_finite_nonwound p G hs hc hu ht
    let := hKF
    let := hKA
    let := hKf
    let := hKp
    let V := baseChangedAlgebraicGroup K G
    let : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
    have hVs := smooth_baseChanged K G hs
    have hVc := group_connected_baseChange K G hc
    have hVu : IsUnipotent V := (unipotenceFieldExtension G).mpr hu
    obtain ⟨i, hi, hcent⟩ := central_additive_of_nonwound p V hVs hVc hVu hw
    obtain ⟨Q, q, hq, _, _⟩ := quotient_by_additive V i hi hcent
    let := hq.2.1
    have hdim := identityDimension_lt q i hi hq.1
    rw [identityDimension_baseChange K G, hd] at hdim
    obtain ⟨hQs, hQc⟩ := smoothConnected_quotient q hq.2.1 hq.2.2.1 hVs hVc
    have hQu := faithfullyFlatQuotientsUnipotent V Q q hq.2.1 hq.2.2.1 hVu
    -- A field that splits the quotient splits the extension by the additive group.
    obtain ⟨L, hLF, hLA, hLf, hLp, hsplit⟩ := ih _ hdim Q rfl hQs hQc hQu
    let := hLF
    let := hLA
    let := hLf
    let := hLp
    let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
    let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hW := split_baseChange_of_additive_extension L hVu q i hi hq hsplit
    exact ⟨L, inferInstance, inferInstance, FiniteDimensional.trans k K L,
      IsPurelyInseparable.trans k K L,
      split_of_groupIso ((groupBaseChangeTower K L).app G.val).symm hW⟩

private theorem additiveSeries_of_groupIso {G H : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) (h : HasAdditiveSeries G) : HasAdditiveSeries H := by
  obtain ⟨n, S, hS⟩ := h
  exact ⟨n, ⟨S.term, S.top ≪≫ e, S.bottom, S.step, S.closed⟩, hS⟩

private theorem additiveSeries_prepend {N G Q : AffineAlgebraicGroup k}
    (i : N.val ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left) (q : G.val ⟶ Q.val)
    (hq : IsFppfGroupQuotient ⟨_, i, hi⟩ q)
    (hQ : Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k))
    (hN : HasAdditiveSeries N) : HasAdditiveSeries G := by
  obtain ⟨n, S, hS⟩ := hN
  let term : ℕ → AffineAlgebraicGroup k
    | 0 => G
    | j + 1 => S.term j
  let step : (j : ℕ) → (term (j + 1)).val ⟶ (term j).val
    | 0 => S.top.hom ≫ i
    | j + 1 => S.step j
  have h0 : IsClosedImmersion (step 0).hom.hom.left := by
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    let : IsClosedImmersion (F.map i) := hi
    change IsClosedImmersion (F.map S.top.hom ≫ F.map i)
    infer_instance
  let C : ClosedSeries G (n + 1) :=
    ⟨term, Iso.refl _, S.bottom, step, fun
      | 0 => h0
      | j + 1 => S.closed j⟩
  refine ⟨n + 1, C, ?_⟩
  intro j hj
  cases j with
  | zero =>
    have hker := scheme_kernel_of_iso q (step 0) h0 ⟨_, i, hi⟩ hq.1 S.top rfl
    exact ⟨Q, q, represented_quotient_of_kernel q ⟨_, step 0, h0⟩ hker
      hq.2.1 hq.2.2.1 hq.2.2.2.1, hQ⟩
  | succ j =>
    exact hS j (Nat.lt_of_succ_lt_succ hj)

private theorem additiveSeries_of_closedSeries {G : AffineAlgebraicGroup k} {n : ℕ}
    (S : ClosedSeries G n)
    (hS : ∀ i < n, ∃ (Q : AffineAlgebraicGroup k) (q : (S.term i).val ⟶ Q.val),
      IsFppfGroupQuotient ⟨_, S.step i, S.closed i⟩ q ∧
      (Nonempty (Q.val ≅ Grp.trivial (SchemeOver k)) ∨
        Nonempty ((groupPointsFunctor k).obj Q.val ≅ StandardGroups.additivePoints k))) :
    HasAdditiveSeries G := by
  induction n generalizing G with
  | zero => exact ⟨0, S, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    let T : ClosedSeries (S.term 1) n :=
      ⟨fun i => S.term (i + 1), Iso.refl _, S.bottom, fun i => S.step (i + 1),
        fun i => S.closed (i + 1)⟩
    have hT : HasAdditiveSeries (S.term 1) :=
      ih T (fun i hi => hS (i + 1) (Nat.succ_lt_succ hi))
    obtain ⟨Q, q, hq, hQ | hQ⟩ := hS 0 (Nat.zero_lt_succ n)
    · have hI : IsIso (S.step 0) := by
        apply closed_surjective_points_iso (S.step 0) (S.closed 0)
        intro R x
        exact (schemeKernel_sections hq.1 x).mpr (sections_eq_one_of_trivial hQ _)
      exact additiveSeries_of_groupIso ((@asIso _ _ _ _ (S.step 0) hI) ≪≫ S.top) hT
    · exact additiveSeries_of_groupIso S.top (additiveSeries_prepend (S.step 0) (S.closed 0) q hq hQ hT)

theorem additiveSeriesCharacterization : AdditiveSeriesCharacterization.{u} := by
  intro k _ G
  constructor
  · rintro ⟨hu, n, S, hS⟩
    exact ⟨hu, additiveSeries_of_closedSeries (G := G) S hS⟩
  · rintro ⟨hu, n, S, hS⟩
    refine ⟨hu, n, S, fun i hi => ?_⟩
    obtain ⟨Q, q, hq, hQ⟩ := hS i hi
    exact ⟨Q, q, hq, Or.inr hQ⟩

end

end LinearAlgebraicGroups.Unipotent
