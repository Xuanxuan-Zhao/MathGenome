import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.FppfTorsors
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.HomogeneousQuotient

open _root_.LinearAlgebraicGroups.Specs
open Specs.QuotientEmbedding (Presentation)
open Specs.HomogeneousQuotient

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private projection_eq_iff represent_of_fppf from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding

variable {k : Type u} [Field k] {G : Specs.GroupScheme k} {H : Specs.ClosedSubgroup G}

private lemma comp_rightMultiplication {T : SchemeOver k} (g : T ⟶ G.X)
    (h : T ⟶ H.group.X) :
    prod.lift g h ≫ rightMultiplication H = g * (h ≫ H.inclusion.hom.hom) := by
  simp [rightMultiplication, MonObj.comp_mul]

/-- Right translation gives the kernel pair of the quotient projection. -/
theorem quotientPullback : QuotientPullback.{u} := by
  intro k _ G H Q
  let i := H.inclusion.hom.hom
  have hi : IsClosedImmersion i.left := H.isClosedImmersion
  haveI : Mono i := Over.mono_of_mono_left i
  have he : (prod.fst : G.X ⨯ H.group.X ⟶ G.X) ≫ Q.projection =
      rightMultiplication H ≫ Q.projection := by
    apply (projection_eq_iff Q _ _).2
    refine ⟨prod.snd, ?_⟩
    change prod.snd ≫ i = prod.fst⁻¹ * (prod.fst * (prod.snd ≫ i))
    simp
  have h (s : PullbackCone Q.projection Q.projection) :
      ∃ a : s.pt ⟶ H.group.X, a ≫ i = s.fst⁻¹ * s.snd :=
    (projection_eq_iff Q _ _).1 s.condition
  choose a ha using h
  refine IsPullback.of_isLimit' ⟨he⟩ (PullbackCone.IsLimit.mk he
    (fun s ↦ prod.lift s.fst (a s)) (fun s ↦ prod.lift_fst _ _) (fun s ↦ ?_)
    (fun s m hm₁ hm₂ ↦ ?_))
  · rw [comp_rightMultiplication, ha, mul_inv_cancel_left]
  · have hh : m ≫ prod.snd ≫ i = s.fst⁻¹ * s.snd := by
      have hm₂' : (m ≫ prod.fst) * (m ≫ prod.snd ≫ i) = s.snd := by
        simpa only [rightMultiplication, MonObj.comp_mul, Category.assoc] using hm₂
      rw [hm₁] at hm₂'
      rw [← hm₂', inv_mul_cancel_left]
    apply prod.hom_ext
    · simpa only [prod.lift_fst] using hm₁
    · rw [prod.lift_snd, ← cancel_mono i, ha]
      exact hh

private def quotientAction (Q : Presentation H) :
    Fppf.SchemeRightAction (Over.mk Q.projection) H.group where
  action := Over.homMk (rightMultiplication H) (quotientPullback Q).w.symm
  one x := by
    apply Over.OverMorphism.ext
    change prod.lift x.left (1 : _ ⟶ H.group.X) ≫ rightMultiplication H = x.left
    rw [comp_rightMultiplication]
    simp
  mul {T} x g h := by
    apply Over.OverMorphism.ext
    let x' : T.left ⟶ G.X := x.left
    let g' : T.left ⟶ H.group.X := g.down
    let h' : T.left ⟶ H.group.X := h.down
    change prod.lift (prod.lift x' g' ≫ rightMultiplication H) h' ≫
        rightMultiplication H = prod.lift x' (g' * h') ≫ rightMultiplication H
    rw [comp_rightMultiplication (prod.lift x' g' ≫ rightMultiplication H) h',
      comp_rightMultiplication x' g', comp_rightMultiplication x' (g' * h'),
      MonObj.mul_comp, mul_assoc]

private theorem quotientComparisonIso (Q : Presentation H) :
    IsIso (Fppf.comparison (quotientAction Q)) := by
  have he : Fppf.comparison (quotientAction Q) = (quotientPullback Q).isoPullback.hom := by
    apply pullback.hom_ext
    · change pullback.lift prod.fst (rightMultiplication H) _ ≫
          pullback.fst Q.projection Q.projection =
        (quotientPullback Q).isoPullback.hom ≫ pullback.fst Q.projection Q.projection
      rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · change pullback.lift prod.fst (rightMultiplication H) _ ≫
          pullback.snd Q.projection Q.projection =
        (quotientPullback Q).isoPullback.hom ≫ pullback.snd Q.projection Q.projection
      rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  rw [he]
  infer_instance

private theorem quotientSmooth (A : Specs.AffineAlgebraicGroup k)
    {H : Specs.ClosedSubgroup A.val} (Q : Presentation H) (hH : Smooth H.group.X.hom) :
    Smooth Q.projection.left := by
  letI : LocallyOfFiniteType A.val.X.hom := A.property.2.1
  letI : IsAffine A.val.X.left := A.property.1
  letI : IsLocallyNoetherian A.val.X.left := LocallyOfFiniteType.isLocallyNoetherian A.val.X.hom
  letI : IsNoetherian A.val.X.left := ⟨⟩
  have hc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      Q.projection.left := ⟨⟨Q.surjective, Q.flat⟩, inferInstance⟩
  have hp := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A.val.X H.group.X)
  have hf : Smooth (prod.fst : A.val.X ⨯ H.group.X ⟶ A.val.X).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hp.flip hH
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
    ((quotientPullback Q).map (Over.forget _)) hc hf

theorem homogeneousQuotient : Specs.HomogeneousQuotient.RepresentabilityAndTorsor.{u} := by
  intro k _ G H
  refine ⟨QuotientEmbedding.quotientEmbedding k G H, fun Q ↦ ⟨?_, quotientSmooth G Q⟩⟩
  letI : IsClosedImmersion H.inclusion.hom.hom.left := H.isClosedImmersion
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : QuasiCompact G.val.X.hom := G.property.2.2
  haveI : LocallyOfFiniteType H.group.X.hom := by
    rw [← Over.w H.inclusion.hom.hom]
    infer_instance
  haveI : QuasiCompact H.group.X.hom := by
    rw [← Over.w H.inclusion.hom.hom]
    infer_instance
  have ha := quotientComparisonIso Q
  refine ⟨quotientAction Q, rfl, ha, ?_⟩
  exact (Fppf.representedTorsorCriterion ⟨inferInstance, inferInstance⟩
    (quotientAction Q)).2 ⟨⟨Q.flat, Q.surjective, Q.finitePresentation⟩, ha⟩

private def compareRepresentatives (Q : Presentation H) {Y : SchemeOver k}
    (e : rightQuotientSheaf H ≅ schemeFppfSheaf Y) : Q.scheme ≅ Y :=
  (fppfOver k).fullyFaithfulUliftYoneda.preimageIso (Q.quotientIso.symm ≪≫ e)

private theorem compareRepresentatives_projection (Q : Presentation H) {Y : SchemeOver k}
    (q : G.X ⟶ Y) (e : rightQuotientSheaf H ≅ schemeFppfSheaf Y)
    (he : rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q) :
    Q.projection ≫ (compareRepresentatives Q e).hom = q := by
  apply (fppfOver k).uliftYoneda.map_injective
  rw [Functor.map_comp, compareRepresentatives, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    ← Q.quotientProjection]
  simpa using he

theorem quotientUniqueness : QuotientUniqueness.{u} := by
  intro k _ G H Q Q'
  refine ⟨compareRepresentatives Q Q'.quotientIso,
    compareRepresentatives_projection Q Q'.projection _ Q'.quotientProjection, ?_⟩
  intro e he
  haveI : Flat Q.projection.left := Q.flat
  haveI : Surjective Q.projection.left := Q.surjective
  haveI : LocallyOfFinitePresentation Q.projection.left := Q.finitePresentation
  haveI : Epi Q.projection := by
    letI : Epi Q.projection.left := inferInstance
    exact Over.epi_of_epi_left _
  apply Iso.ext
  rw [← cancel_epi Q.projection, he, compareRepresentatives_projection _ _ _ Q'.quotientProjection]

theorem quotientAffineComparison : QuotientAffineComparison.{u} := by
  intro k _ G H Q hn
  obtain ⟨L, f, A, q, i, hf, hq, hfac, himage, e, he⟩ := normalAffineQuotient G H hn
  exact ⟨L, A, f, q, i, compareRepresentatives Q e, hf, hq, hfac, himage,
    compareRepresentatives_projection Q q.hom.hom e he⟩

private lemma projection_eq_iff_of_pullback {Y : SchemeOver k} (q : G.X ⟶ Y)
    (hp : IsPullback prod.fst (rightMultiplication H) q q)
    (T : SchemeOver k) (g g' : T ⟶ G.X) :
    g ≫ q = g' ≫ q ↔ g⁻¹ * g' ∈ SubgroupSections H T := by
  change _ ↔ ∃ a : T ⟶ H.group.X, a ≫ H.inclusion.hom.hom = g⁻¹ * g'
  constructor
  · intro he
    let z := hp.lift g g' he
    have hz₁ : z ≫ prod.fst = g := hp.lift_fst _ _ _
    have hz₂ : z ≫ rightMultiplication H = g' := hp.lift_snd _ _ _
    refine ⟨z ≫ prod.snd, ?_⟩
    rw [← hz₂, rightMultiplication, MonObj.comp_mul, hz₁, inv_mul_cancel_left, Category.assoc]
  · rintro ⟨a, ha⟩
    have h₁ : prod.lift g a ≫ prod.fst = g := prod.lift_fst _ _
    have h₂ : prod.lift g a ≫ rightMultiplication H = g' := by
      rw [comp_rightMultiplication, ha, mul_inv_cancel_left]
    rw [← h₁, ← h₂, Category.assoc, Category.assoc, hp.w]

private theorem baseChangeMapIsPullback (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (q : X ⟶ Y) :
    IsPullback ((baseChange k K).map q).left (pullback.fst X.hom (fieldSpecMap k K))
      (pullback.fst Y.hom (fieldSpecMap k K)) q.left := by
  let f := fieldSpecMap k K
  let b := ((baseChange k K).map q).left
  have hXY : IsPullback (pullback.fst X.hom f) (pullback.snd X.hom f) (q.left ≫ Y.hom) f := by
    rw [Over.w q]
    exact IsPullback.of_hasPullback _ _
  have h₁ : b ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ q.left :=
    pullback.lift_fst _ _ _
  have h₂ : b ≫ pullback.snd Y.hom f = pullback.snd X.hom f := pullback.lift_snd _ _ _
  exact (IsPullback.of_bot (h₂.symm ▸ hXY) h₁.symm (IsPullback.of_hasPullback Y.hom f)).flip

private theorem baseChangeQuotientPullback (K : Type u) [Field K] [Algebra k K]
    (Q : Presentation H)
    (hs : IsClosedImmersion ((groupBaseChange k K).map H.inclusion).hom.hom.left) :
    let H' : Specs.ClosedSubgroup ((groupBaseChange k K).obj G) :=
      ⟨(groupBaseChange k K).obj H.group, (groupBaseChange k K).map H.inclusion, hs⟩
    IsPullback prod.fst (rightMultiplication H') ((baseChange k K).map Q.projection)
      ((baseChange k K).map Q.projection) := by
  intro H'
  let F := baseChange k K
  let e := PreservesLimitPair.iso F G.X H.group.X
  have hf : e.inv ≫ F.map prod.fst = prod.fst := PreservesLimitPair.iso_inv_fst F G.X H.group.X
  have hsnd : e.inv ≫ F.map prod.snd = prod.snd := PreservesLimitPair.iso_inv_snd F G.X H.group.X
  have ha : e.inv ≫ F.map (rightMultiplication H) = rightMultiplication H' := by
    change e.inv ≫ F.map (prod.fst * (prod.snd ≫ H.inclusion.hom.hom)) = _
    simp only [F.map_mul, F.map_comp, MonObj.comp_mul, ← Category.assoc, hf, hsnd]
    rfl
  change IsPullback (prod.fst : F.obj G.X ⨯ F.obj H.group.X ⟶ F.obj G.X)
    (rightMultiplication H') (F.map Q.projection) (F.map Q.projection)
  exact (F.map_isPullback (quotientPullback Q)).of_iso' e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hf.trans (Category.comp_id _).symm) (ha.trans (Category.comp_id _).symm)
    (by simp) (by simp)

theorem quotientBaseChange : QuotientBaseChange.{u} := by
  intro k K _ _ _ G H Q
  let F := baseChange k K
  have hs := baseChangeClosedSubgroup k K H.inclusion H.isClosedImmersion
  let H' : Specs.ClosedSubgroup ((groupBaseChange k K).obj G) :=
    ⟨(groupBaseChange k K).obj H.group, (groupBaseChange k K).map H.inclusion, hs⟩
  refine ⟨hs, ?_⟩
  have hp := baseChangeMapIsPullback K Q.projection
  haveI : Flat (F.map Q.projection).left :=
    MorphismProperty.of_isPullback (P := @Flat) hp.flip Q.flat
  haveI : Surjective (F.map Q.projection).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hp.flip Q.surjective
  haveI : LocallyOfFinitePresentation (F.map Q.projection).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hp.flip Q.finitePresentation
  exact represent_of_fppf H' (F.map Q.projection)
    (projection_eq_iff_of_pullback _ (baseChangeQuotientPullback K Q hs))


section ProjectiveLinear

open Specs.StandardGroups LaurentPolynomial

variable {I : Type u} [Fintype I] [DecidableEq I]

private def scalarMatrices (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I] :
    multiplicativePoints k ⟶ generalLinearPoints k I where
  app R := GrpCat.ofHom (Matrix.GeneralLinearGroup.scalar I)
  naturality R S f := by
    apply GrpCat.ext
    intro a
    change Matrix.GeneralLinearGroup.scalar I (Units.map f.hom.toMonoidHom a) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (Matrix.GeneralLinearGroup.scalar I a)
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.map_apply]
    change Matrix.scalar I (f.hom a.val) i j = f.hom (Matrix.scalar I a.val i j)
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]

private lemma scalarCoordinates_surjective [Nonempty I]
    (c : GLCoordinates k I →ₐ[k] LaurentPolynomial k)
    (t : (LaurentPolynomial k)ˣ) (ht : t.val = T 1)
    (hc : c.mapMatrix (universalMatrix k I) = Matrix.scalar I t.val) :
    Function.Surjective c := by
  classical
  let i : I := Classical.choice ‹Nonempty I›
  have htpos : (T 1 : LaurentPolynomial k) ∈ c.range := by
    refine ⟨universalMatrix k I i i, ?_⟩
    simpa [Matrix.scalar_apply, ht] using congrArg (fun M : Matrix I I (LaurentPolynomial k) ↦ M i i) hc
  let A := Matrix.GeneralLinearGroup.mk'' (universalMatrix k I)
    (LinearAlgebraicGroups.StandardGroups.isUnit_universalDeterminant k I)
  have hA : Matrix.GeneralLinearGroup.map c.toRingHom A =
      Matrix.GeneralLinearGroup.scalar I t := Units.ext hc
  have hi : (t⁻¹).val = (T (-1) : LaurentPolynomial k) := by
    apply (Units.mul_right_inj t).mp
    rw [Units.mul_inv, ht, ← T_add, add_neg_cancel, T_zero]
  have htneg : (T (-1) : LaurentPolynomial k) ∈ c.range := by
    refine ⟨A⁻¹ i i, ?_⟩
    change (Matrix.GeneralLinearGroup.map c.toRingHom A⁻¹) i i = _
    rw [map_inv, hA, ← map_inv]
    change Matrix.scalar I (t⁻¹).val i i = _
    simp [Matrix.scalar_apply, hi]
  intro p
  change p ∈ c.range
  induction p using LaurentPolynomial.induction_on with
  | h_C a => rw [C_eq_algebraMap]; exact c.range.algebraMap_mem a
  | h_add hp hq => exact c.range.add_mem hp hq
  | h_C_mul_T n a hp => rw [T_add, ← mul_assoc]; exact c.range.mul_mem hp htpos
  | h_C_mul_T_Z n a hp =>
    rw [sub_eq_add_neg, T_add, ← mul_assoc]
    exact c.range.mul_mem hp htneg

open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

private lemma scalarNormal {M L : Specs.AffineAlgebraicGroup k}
    (em : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
    (el : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k I)
    (s : M.val ⟶ L.val)
    (hs : ∀ (R : TestAlgebra k) (a : Points M.val.X R),
      el.hom.app R (a ≫ s.hom.hom) = Matrix.GeneralLinearGroup.scalar I (em.hom.app R a)) :
    Specs.IsNormalSubgroup s := by
  let X := L.val.X
  let Y := M.val.X
  refine ⟨snd X Y, ?_⟩
  apply hom_ext_of_points (X := X ⊗ Y)
  · haveI : IsAffine X.left := L.property.1
    haveI : IsAffine Y.left := M.property.1
    change IsAffine (pullback X.hom Y.hom)
    infer_instance
  · intro R p
    let a : Points X R := p ≫ fst X Y
    let b : Points Y R := p ≫ snd X Y
    let d : Points X R := b ≫ s.hom.hom
    have he : p ≫ (snd X Y ≫ s.hom.hom) = d := (Category.assoc _ _ _).symm
    rw [he]
    change d = p ≫ Specs.subgroupConjugation s
    rw [Specs.subgroupConjugation, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, he]
    change d = a * d * a⁻¹
    apply (ConcreteCategory.bijective_of_isIso (el.hom.app R)).1
    change (el.hom.app R).hom d = (el.hom.app R).hom (a * d * a⁻¹)
    rw [map_mul, map_mul, map_inv]
    have hd : (el.hom.app R).hom d = Matrix.GeneralLinearGroup.scalar I (em.hom.app R b) := hs R b
    rw [hd, ← Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]

theorem projectiveLinearQuotient : ProjectiveLinearQuotient.{u} := by
  intro k _ I _ _ _
  obtain ⟨hm, _, _, _, hM⟩ := LinearAlgebraicGroups.StandardGroups.multiplicativeGroupSpecification k
  obtain ⟨hl, _, _, _, _, _, _, hL⟩ :=
    LinearAlgebraicGroups.StandardGroups.generalLinearGroupSpecification k I
  letI := hm.hopf
  letI := hl.hopf
  let M := spectrum k (LaurentPolynomial k)
  let L := spectrum k (GLCoordinates k I)
  obtain ⟨eM, hEM, em, hmEval⟩ := hM
  obtain ⟨eL, hEL, el, hlEval⟩ := hL
  let τ := em.hom ≫ scalarMatrices k I ≫ el.inv
  obtain ⟨s, hs⟩ := (groupHomComparison k M.val L.val M.property.1).2 τ
  have hsPoint (R : TestAlgebra k) (a : Points M.val.X R) :
      el.hom.app R (a ≫ s.hom.hom) =
        Matrix.GeneralLinearGroup.scalar I (em.hom.app R a) := by
    have h := congrArg (fun f ↦ (f.app R) a) hs
    change a ≫ s.hom.hom =
      el.inv.app R (Matrix.GeneralLinearGroup.scalar I (em.hom.app R a)) at h
    rw [h, ← GrpCat.comp_apply, el.inv_hom_id_app]
    rfl
  let R := CommAlgCat.of k (LaurentPolynomial k)
  let a : Points M.val.X R := eM.hom.app R (toConv (AlgHom.id k R))
  let t : Rˣ := em.hom.app R a
  have ht : t.val = T 1 := hmEval R (AlgHom.id k R)
  let c : GLCoordinates k I →ₐ[k] R :=
    ((eL.inv.app R) (a ≫ s.hom.hom)).ofConv
  have hcPoint : eL.hom.app R (toConv c) = a ≫ s.hom.hom := by
    change eL.hom.app R (eL.inv.app R (a ≫ s.hom.hom)) = _
    rw [← GrpCat.comp_apply, eL.inv_hom_id_app]
    rfl
  have hc : c.mapMatrix (universalMatrix k I) = Matrix.scalar I t.val := by
    have he := hlEval R c
    rw [hcPoint, hsPoint R a] at he
    exact he.symm
  have hsSpec : s.hom.hom.left = Spec.map (CommRingCat.ofHom c.toRingHom) := by
    have ha : a.left = 𝟙 (Spec (CommRingCat.of R)) :=
      (hEM R (AlgHom.id k R)).trans (Spec.map_id _)
    have he := hEL R c
    rw [hcPoint, Over.comp_left] at he
    let b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (GLCoordinates k I)) := s.hom.hom.left
    change a.left ≫ b = _ at he
    change b = _
    rw [ha] at he
    exact (Category.id_comp b).symm.trans he
  have hclosed : IsClosedImmersion s.hom.hom.left := by
    rw [hsSpec]
    exact IsClosedImmersion.spec_of_surjective _ (scalarCoordinates_surjective c t ht hc)
  have hn := scalarNormal em el s hsPoint
  let H : Specs.ClosedSubgroup L.val := ⟨M.val, s, hclosed⟩
  obtain ⟨⟨P⟩, hP⟩ := homogeneousQuotient k L H
  obtain ⟨_, PGL, _, q, _, e, _, hq, _, _, he⟩ := quotientAffineComparison L H P hn
  exact ⟨hm, hl, em, el, s, hclosed, hsPoint, hn, P, PGL, q, e, (hP P).1, hq, he⟩

end ProjectiveLinear

end

end LinearAlgebraicGroups.HomogeneousQuotient
