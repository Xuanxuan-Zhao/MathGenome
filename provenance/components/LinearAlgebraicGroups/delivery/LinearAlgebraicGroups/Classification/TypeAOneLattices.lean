import Specs.LinearAlgebraicGroups.Classification.TypeAOneLattices
import LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny
import LinearAlgebraicGroups.Flag.HomogeneousQuotient
import LinearAlgebraicGroups.Descent.AdjointCocharacters
import LinearAlgebraicGroups.Classification.CentralIsogenies
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Affine.LieLeftExact
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.TypeAOneLattices

open _root_.LinearAlgebraicGroups.Specs
open Specs.TypeAOneLattices
open Specs.GeneralLinearCentralIsogeny Specs.CentralDerived
open Specs.GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open Specs.GeometricRadicals (IsReductive IsSplitReductive)
open Specs.CentralTorus (IsSchemeCentre)
open Specs.CentralIsogenies (IsCentralIsogeny)
open Specs.SchemeDerivedGroup (RepresentsQuotient)
open Specs.Unipotent (Index)

noncomputable section

set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.style.haveILetI false

open private reductive_of_central_quotient from LinearAlgebraicGroups.Descent.AdjointCocharacters
open private quotientSmooth from LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private scalarCentreIsTorus from LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny
open private reducedOfSmoothHopf from LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private torus_smooth smooth_lift_dual from LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private normalOfCentral from LinearAlgebraicGroups.Reductive.CentralDerived
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private subgroupInclusionFactors from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private groupIsoOfPoints from LinearAlgebraicGroups.Unipotent.Criteria

variable {k : Type u} [Field k]

private theorem centre_mul_comm {G : Specs.GroupScheme k} {Z : Specs.ClosedSubgroup G}
    (hz : IsSchemeCentre Z) {X : SchemeOver k} (x : X ⟶ G.X) (z : X ⟶ Z.group.X) :
    Commute x (z ≫ Z.inclusion.hom.hom) := by
  have hc := (hz X (z ≫ Z.inclusion.hom.hom)).mpr ⟨z, rfl⟩
  simpa using ((centralizes_iff _ _).mp hc X (𝟙 X) x).symm

set_option linter.style.haveILetI false in
private theorem multiplication_pullback
    {S G P : Specs.GroupScheme k} (f : S ⟶ G) (q : G ⟶ P)
    {Z : Specs.ClosedSubgroup G} (hZ : IsSchemeKernel q Z)
    (T : Specs.GroupScheme k) (i : T ≅ Z.group) :
    IsPullback (snd T.X S.X)
      ((fst T.X S.X ≫ i.hom.hom.hom ≫ Z.inclusion.hom.hom) * (snd T.X S.X ≫ f.hom.hom))
      (f.hom.hom ≫ q.hom.hom) q.hom.hom := by
  let j := Z.inclusion.hom.hom
  let a := i.hom.hom.hom
  let b := i.inv.hom.hom
  let m := (fst T.X S.X ≫ a ≫ j) * (snd T.X S.X ≫ f.hom.hom)
  have hj : j ≫ q.hom.hom = 1 := hZ.w
  have hm : ∀ {Y : SchemeOver k} (x : Y ⟶ T.X ⊗ S.X),
      x ≫ m = ((x ≫ fst T.X S.X) ≫ a ≫ j) * ((x ≫ snd T.X S.X) ≫ f.hom.hom) := by
    intro Y x
    simp only [m, MonObj.comp_mul, Category.assoc]
  have h : snd T.X S.X ≫ (f.hom.hom ≫ q.hom.hom) = m ≫ q.hom.hom := by
    simp only [m, MonObj.mul_comp, Category.assoc, hj, MonObj.comp_one, one_mul]
  letI : IsClosedImmersion j.left := Z.isClosedImmersion
  letI : Mono j := Over.mono_of_mono_left j
  haveI : IsIso a := (Grp.forget _).map_isIso i.hom
  have hba : b ≫ a = 𝟙 _ := by
    exact congrArg (fun g : Z.group ⟶ Z.group => g.hom.hom) i.inv_hom_id
  have hbaj : b ≫ a ≫ j = j := by rw [← Category.assoc, hba, Category.id_comp]
  have lifts (c : PullbackCone (f.hom.hom ≫ q.hom.hom) q.hom.hom) :
      ∃ z : c.pt ⟶ Z.group.X, z ≫ j = c.snd * (c.fst ≫ f.hom.hom)⁻¹ := by
    apply (schemeKernel_sections hZ _).mpr
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, c.condition, mul_inv_cancel]
  choose z hz using lifts
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk h
    (fun c => lift (z c ≫ b) c.fst) (fun c => lift_snd _ _) (fun c => ?_)
    (fun c t ht₁ ht₂ => ?_))
  · rw [hm, lift_fst, lift_snd, Category.assoc, hbaj, hz,
      inv_mul_cancel_right]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, ← cancel_mono a, ← cancel_mono j, Category.assoc (z _), Category.assoc (z _), hba, Category.id_comp, hz]
      change t ≫ m = c.snd at ht₂
      rw [hm, ht₁] at ht₂
      rw [← ht₂, mul_inv_cancel_right]
      exact Category.assoc _ _ _
    · exact ht₁.trans (lift_snd _ _).symm

set_option linter.style.haveILetI false in
private theorem finite_of_kernel_finite {S P : Specs.GroupScheme k} (f : S ⟶ P)
    [IsAffine S.X.left] [IsAffine P.X.left] [Flat f.hom.hom.left] [Surjective f.hom.hom.left] [LocallyOfFiniteType f.hom.hom.left]
    {N : Specs.ClosedSubgroup S} (hN : IsSchemeKernel f N) [IsFinite N.group.X.hom] :
    IsFinite f.hom.hom.left := by
  have hp := multiplication_pullback (𝟙 S) f hN N.group (Iso.refl _)
  rw [show (𝟙 S : S ⟶ S).hom.hom ≫ f.hom.hom = f.hom.hom from Category.id_comp _] at hp
  have hf : IsFinite (snd N.group.X S.X).left :=
    inferInstanceAs (IsFinite (pullback.snd N.group.X.hom S.X.hom))
  have huc : UniversallyClosed f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f.hom.hom.left)
      (g := f.hom.hom.left) (hp.map (Over.forget _))
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (show UniversallyClosed (snd N.group.X S.X).left from inferInstance)
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨⟨⟩, inferInstance⟩

private theorem transport_kernel {S G P T : Specs.GroupScheme k}
    {f : S ⟶ G} {q : G ⟶ P} {m : (T ⊗ S) ⟶ G}
    (h : IsPullback (secondProjection T S).hom.hom m.hom.hom (f ≫ q).hom.hom q.hom.hom)
    {J : Specs.ClosedSubgroup (T ⊗ S)} (hJ : IsSchemeKernel m J) :
    ∃ N : Specs.ClosedSubgroup S, N.group = J.group ∧ IsSchemeKernel (f ≫ q) N ∧
      ∃ e : N.group ≅ J.group, N.inclusion = e.hom ≫ J.inclusion ≫ secondProjection T S := by
  have hp := (hJ.flip.paste_vert h.flip).flip
  have hu : η[G.X] ≫ q.hom.hom = η[P.X] := IsMonHom.one_hom q.hom.hom
  rw [hu] at hp
  have hc : IsClosedImmersion (J.inclusion ≫ secondProjection T S).hom.hom.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hp.flip.map (Over.forget _))
      (by
        change IsClosedImmersion η[P.X].left
        haveI : Subsingleton ((𝟙_ (SchemeOver k)).left : Scheme) :=
          inferInstanceAs (Subsingleton (PrimeSpectrum k))
        exact isClosedImmersion_of_comp_eq_id _ _ (Over.w η[P.X]))
  exact ⟨⟨J.group, J.inclusion ≫ secondProjection T S, hc⟩, rfl, hp,
    Iso.refl _, by simp⟩


private theorem kernel_central {S G P : Specs.GroupScheme k} (f : S ⟶ G) (q : G ⟶ P)
    [Mono f.hom.hom] {Z : Specs.ClosedSubgroup G} (hz : IsSchemeKernel q Z)
    (hc : IsSchemeCentre Z) {N : Specs.ClosedSubgroup S} (hn : IsSchemeKernel (f ≫ q) N) :
    Centralizes (𝟙 S) N.inclusion.hom.hom := by
  obtain ⟨z, hz'⟩ := (schemeKernel_sections hz (N.inclusion.hom.hom ≫ f.hom.hom)).mpr
    (by exact (Category.assoc N.inclusion.hom.hom f.hom.hom q.hom.hom).trans hn.w)
  apply (centralizes_iff _ _).mpr
  intro X t x
  apply (cancel_mono f.hom.hom).mp
  change ((t ≫ N.inclusion.hom.hom) * x) ≫ f.hom.hom =
    (x * (t ≫ N.inclusion.hom.hom)) ≫ f.hom.hom
  change z ≫ Z.inclusion.hom.hom = N.inclusion.hom.hom ≫ f.hom.hom at hz'
  rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc, ← hz']
  simpa only [Category.assoc] using (centre_mul_comm hc (x ≫ f.hom.hom) (t ≫ z)).symm.eq

private theorem iso_projection_properties {G P : Specs.GroupScheme k}
    {Z : Specs.ClosedSubgroup G} (Q : Specs.QuotientEmbedding.Presentation Z)
    (q : G ⟶ P) (e : Q.scheme ≅ P.X) (he : Q.projection ≫ e.hom = q.hom.hom) :
    Flat q.hom.hom.left ∧ Surjective q.hom.hom.left ∧
      LocallyOfFinitePresentation q.hom.hom.left ∧ RepresentsQuotient Z q := by
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have eq : Q.projection.left ≫ e.hom.left = q.hom.hom.left :=
    congrArg (fun f => f.left) he
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← eq]
    exact MorphismProperty.comp_mem _ _ _ Q.flat (MorphismProperty.of_isIso _ _)
  · rw [← eq]
    exact MorphismProperty.comp_mem _ _ _ Q.surjective (MorphismProperty.of_isIso _ _)
  · rw [← eq]
    haveI : LocallyOfFinitePresentation Q.projection.left := Q.finitePresentation
    infer_instance
  · let Y := (fppfOver k).uliftYoneda.{u+1}
    use Q.quotientIso ≪≫ Y.mapIso e
    rw [Iso.trans_hom, ← Category.assoc, Q.quotientProjection]
    change Y.map Q.projection ≫ Y.map e.hom = Y.map q.hom.hom
    rw [← Y.map_comp, he]

private def invertRoots (k : Type u) [Field k] (n : ℕ) :
    Specs.DiagonalizableGroups.rootsOfUnityPoints k n ≅
      Specs.DiagonalizableGroups.rootsOfUnityPoints k n :=
  NatIso.ofComponents (fun R => MulEquiv.toGrpIso {
    toFun := Inv.inv
    invFun := Inv.inv
    left_inv := inv_inv
    right_inv := inv_inv
    map_mul' := by
      intro x y
      change (((x : rootsOfUnity n R) * (y : rootsOfUnity n R))⁻¹ : rootsOfUnity n R) =
        (x : rootsOfUnity n R)⁻¹ * (y : rootsOfUnity n R)⁻¹
      exact @mul_inv (rootsOfUnity n R) inferInstance x y })
    (by
      intro R A f
      apply GrpCat.ext
      intro z
      exact map_inv ((Specs.DiagonalizableGroups.rootsOfUnityPoints k n).map f).hom z)

private theorem matrix_centre_of_scalar_kernel {S : Specs.AffineAlgebraicGroup k} {n : ℕ}
    (hn : 0 < n) (s : SpecialMatrixPoints S n) (N : Specs.ClosedSubgroup S.val)
    (hN : Centralizes (𝟙 S.val) N.inclusion.hom.hom)
    (c : (groupPointsFunctor k).obj N.group ≅ Specs.DiagonalizableGroups.rootsOfUnityPoints k n)
    (hscalar : ∀ (R : TestAlgebra k) (x : Points N.group.X R),
      Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
        Matrix.GeneralLinearGroup.scalar (Index.{u} n) (c.hom.app R x).val) :
    IsSchemeCentre N := by
  let I : Specs.ClosedSubgroup S.val := ⟨S.val, 𝟙 _, by
    change IsClosedImmersion (𝟙 S.val.X.left)
    infer_instance⟩
  obtain ⟨C, hC⟩ := centralizerScheme k S I
  change IsSchemeCentre C at hC
  have hfactor : ∃ f : C.group ⟶ N.group, f ≫ N.inclusion = C.inclusion := by
    apply subgroupInclusionFactors (Specs.Unipotent.closedSubgroupAlgebraicGroup C).property.1
    intro R x
    let y := pointMap C.inclusion R x
    have hy : Centralizes (𝟙 S.val) y := (hC _ y).mpr ⟨x, rfl⟩
    have hy' : s.hom.app R y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Index.{u} n) R) := by
      apply Subgroup.mem_center_iff.mpr
      intro v
      obtain ⟨z, rfl⟩ := (s.app R).groupIsoToMulEquiv.surjective v
      have h := (centralizes_iff _ _).mp hy _ (𝟙 _) z
      change Commute ((𝟙 _) ≫ y) (z ≫ 𝟙 _) at h
      simpa only [Category.id_comp, Category.comp_id] using!
        (h.symm.map (s.app R).groupIsoToMulEquiv).eq
    obtain ⟨r, hr, hmat⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hy'
    have hr' : r ^ n = 1 := by simpa only [Fintype.card_ulift, Fintype.card_fin] using hr
    letI : NeZero n := ⟨hn.ne'⟩
    let ζ := rootsOfUnity.mkOfPowEq r hr'
    obtain ⟨w, hw⟩ := (c.app R).groupIsoToMulEquiv.surjective ζ
    refine ⟨w, (s.app R).groupIsoToMulEquiv.injective
      (Matrix.SpecialLinearGroup.toGL_injective ?_)⟩
    change Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R w)) =
      Matrix.SpecialLinearGroup.toGL (s.hom.app R y)
    rw [hscalar R w, show c.hom.app R w = ζ from hw]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    change Matrix.scalar (Index.{u} n) (↑ζ.val : R) = (s.hom.app R y).val
    simpa only [ζ, rootsOfUnity.val_mkOfPowEq_coe] using hmat
  obtain ⟨f, hf⟩ := hfactor
  intro X x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (hC X x).mp hx
    exact ⟨z ≫ f.hom.hom, (Category.assoc _ _ _).trans
      (congrArg (fun a : C.group ⟶ S.val => z ≫ a.hom.hom) hf)⟩
  · rintro ⟨z, rfl⟩
    apply (centralizes_iff _ _).mpr
    intro Y t y
    simpa only [Category.assoc] using (centralizes_iff _ _).mp hN Y (t ≫ z) y

open private detScalar from LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny

/-- The pullback of affine schemes over `k` is determined by its universal property
on spectra of test algebras. -/
private theorem isPullback_of_testAlgebras {B : TestAlgebra k} {X Y Z : SchemeOver k}
    [IsAffine X.left] [IsAffine Y.left] [IsAffine Z.left]
    {p : Points X B} {q : Points Y B} {f : X ⟶ Z} {g : Y ⟶ Z}
    (comm : p ≫ f = q ≫ g)
    (lifts : ∀ (A : TestAlgebra k) (x : Points X A) (y : Points Y A), x ≫ f = y ≫ g →
      ∃! w : Points ((testSpec k).obj (op B)) A, w ≫ p = x ∧ w ≫ q = y) :
    IsPullback p q f g := by
  have hp := (IsPullback.of_hasPullback f g).map (Over.forget _)
  have ha : IsAffine (pullback f g).left :=
    IsAffine.of_isPullback (show IsPullback (pullback.fst f g).left (pullback.snd f g).left
      f.left g.left from hp)
  obtain ⟨R, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr ha
  obtain ⟨w, hw, _⟩ := lifts R.unop (e.hom ≫ pullback.fst f g) (e.hom ≫ pullback.snd f g) (by
    simp only [Category.assoc, pullback.condition])
  let l := pullback.lift p q comm
  let i := e.inv ≫ w
  have h₁ : i ≫ p = pullback.fst f g := by
    dsimp [i]
    rw [Category.assoc, hw.1, e.inv_hom_id_assoc]
  have h₂ : i ≫ q = pullback.snd f g := by
    dsimp [i]
    rw [Category.assoc, hw.2, e.inv_hom_id_assoc]
  have hli : l ≫ i = 𝟙 _ := by
    obtain ⟨z, _, hu⟩ := lifts B p q comm
    exact (hu (l ≫ i) ⟨by simp [Category.assoc, h₁, l], by simp [Category.assoc, h₂, l]⟩).trans
      (hu (𝟙 _) ⟨Category.id_comp _, Category.id_comp _⟩).symm
  have hil : i ≫ l = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [Category.assoc, l, h₁, h₂]
  exact IsPullback.of_iso_pullback ⟨comm⟩ ⟨l, i, hli, hil⟩ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)

open Matrix (GeneralLinearGroup SpecialLinearGroup) in
/-- The determinant-root algebra represents the fibre of scalar multiplication. -/
private theorem scalar_rescaling_fibre {n : ℕ} {G S M : AffineAlgebraicGroup k}
    (g : MatrixPoints G n) (s : SpecialMatrixPoints S n)
    (a : (groupPointsFunctor k).obj M.val ≅ StandardGroups.multiplicativePoints k)
    {T : GroupScheme k} [IsAffine T.X.left] (t : T ≅ M.val)
    (m : (T ⊗ S.val) ⟶ G.val)
    (hm : ∀ (R : TestAlgebra k) (x : Points (T ⊗ S.val).X R),
      g.hom.app R (pointMap m R x) =
        GeneralLinearGroup.scalar (Index.{u} n)
          (a.hom.app R (pointMap (firstProjection T S.val ≫ t.hom) R x)) *
        SpecialLinearGroup.toGL
          (s.hom.app R (pointMap (secondProjection T S.val) R x)))
    (R : TestAlgebra k) (x : Points G.val.X R)
    {z : (determinantRootTestAlgebra R n (g.hom.app R x).det)ˣ}
    {v : Points (T ⊗ S.val).X (determinantRootTestAlgebra R n (g.hom.app R x).det)}
    (hz : z.val = AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (g.hom.app R x).det.val))
    (hscalar : a.hom.app _ (pointMap (firstProjection T S.val ≫ t.hom) _ v) = z)
    (hv : pointMap m _ v = mapPoints (determinantRootMap R n (g.hom.app R x).det) x) :
    IsPullback v ((testSpec k).map (determinantRootMap R n (g.hom.app R x).det).op)
      m.hom.hom x := by
  let d := (g.hom.app R x).det
  let B := determinantRootTestAlgebra R n d
  let b := determinantRootMap R n d
  let p : Polynomial R := Polynomial.X ^ n - Polynomial.C (d : R)
  let F := testSpec k
  let FF := algSpec.fullyFaithful (R := CommRingCat.of k)
  let χ := (groupPointsFunctor k).map (firstProjection T S.val ≫ t.hom) ≫ a.hom
  have χnat {A C : TestAlgebra k} (c : A ⟶ C) (y : Points (T ⊗ S.val).X A) :
      χ.app C (mapPoints c y) = Units.map c.hom.toMonoidHom (χ.app A y) :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (χ.naturality c)) y
  have point_eq_of_scalar (A : TestAlgebra k) (y y' : Points (T ⊗ S.val).X A)
      (h : χ.app A y = χ.app A y') (hprod : pointMap m A y = pointMap m A y') : y = y' := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (((groupPointsFunctor k).mapIso t ≪≫ a).app A).groupIsoToMulEquiv.injective h
    · apply (s.app A).groupIsoToMulEquiv.injective
      apply SpecialLinearGroup.toGL_injective
      have hmul := congrArg (fun w => g.hom.app A w) hprod
      rw [hm A y, hm A y'] at hmul
      change GeneralLinearGroup.scalar (Index.{u} n) (χ.app A y) * _ =
        GeneralLinearGroup.scalar (Index.{u} n) (χ.app A y') * _ at hmul
      rw [h] at hmul
      exact mul_left_cancel hmul
  letI : IsAffine S.val.X.left := S.property.1
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine (F.obj (op R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  letI : IsAffine (T ⊗ S.val).X.left :=
    IsAffine.of_isPullback ((IsPullback.of_hasPullback T.X.hom S.val.X.hom))
  refine isPullback_of_testAlgebras hv ?_
  intro A y f hf
  let c : R ⟶ A := (FF.preimage f).unop
  have hc : F.map c.op = f := FF.map_preimage f
  have hzA : (χ.app A y : Aˣ).val ^ n = c.hom (d : R) := by
    have hxy : pointMap m A y = mapPoints c x := by
      change y ≫ m.hom.hom = F.map c.op ≫ x
      rw [hc, hf]
    have hmat : g.hom.app A (pointMap m A y) =
        GeneralLinearGroup.map c.hom.toRingHom (g.hom.app R x) :=
      (congrArg (fun w => g.hom.app A w) hxy).trans (congrArg (fun τ => τ x) (g.hom.naturality c))
    have hdet := congrArg (GeneralLinearGroup.det : GeneralLinearGroup (Index.{u} n) A →* Aˣ) hmat
    rw [hm, map_mul, detScalar, SpecialLinearGroup.coeToGL_det, mul_one,
      GeneralLinearGroup.map_det] at hdet
    exact congrArg Units.val hdet
  have hzero : p.eval₂ c.hom.toRingHom (χ.app A y).val = 0 := by
    change (Polynomial.X ^ n - Polynomial.C (d : R)).eval₂ c.hom.toRingHom (χ.app A y).val = 0
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact sub_eq_zero.mpr hzA
  let e : B ⟶ A := CommAlgCat.ofHom (AdjoinRoot.liftAlgHom p c.hom (χ.app A y).val hzero)
  have heb : b ≫ e = c := by
    ext r
    exact AdjoinRoot.liftAlgHom_of p c.hom (χ.app A y).val hzero r
  have heroot : e.hom (AdjoinRoot.root p) = (χ.app A y).val :=
    AdjoinRoot.liftAlgHom_root p c.hom (χ.app A y).val hzero
  have he₂ : F.map e.op ≫ F.map b.op = f := by
    rw [← F.map_comp, ← op_comp, heb, hc]
  have he₁ : F.map e.op ≫ v = y := by
    change mapPoints e v = y
    apply point_eq_of_scalar
    · rw [χnat, show χ.app B v = z from hscalar]
      apply Units.ext
      change e.hom z.val = _
      rw [hz]
      exact heroot
    · change (F.map e.op ≫ v) ≫ m.hom.hom = y ≫ m.hom.hom
      rw [Category.assoc, show v ≫ m.hom.hom = F.map b.op ≫ x from hv,
        ← Category.assoc, he₂, hf]
  refine ⟨F.map e.op, ⟨he₁, he₂⟩, ?_⟩
  intro w hw
  let e' : B ⟶ A := (FF.preimage w).unop
  have he' : F.map e'.op = w := FF.map_preimage w
  have he'b : b ≫ e' = c := by
    apply Quiver.Hom.op_inj
    apply FF.map_injective
    change F.map (b ≫ e').op = F.map c.op
    rw [op_comp, F.map_comp, he', hc]
    exact hw.2
  have he'root : e'.hom (AdjoinRoot.root p) = (χ.app A y).val := by
    have hn := χnat e' v
    rw [show mapPoints e' v = y from (congrArg (· ≫ v) he').trans hw.1,
      show χ.app B v = z from hscalar] at hn
    rw [show AdjoinRoot.root p = z.val from hz.symm]
    exact congrArg Units.val hn.symm
  have eq : e' = e := by
    apply CommAlgCat.hom_ext
    exact AdjoinRoot.algHom_ext' (congrArg CommAlgCat.Hom.hom (he'b.trans heb.symm))
      (he'root.trans heroot.symm)
  rw [← he', eq]

set_option linter.style.haveILetI false in
/-- The canonical projective isogeny, including its determinant-rescaling pullback
and its roots-of-unity scheme kernel. -/
theorem matrixProjectiveIsogeny : MatrixProjectiveIsogeny.{u} := by
  intro k _ n hn G S M g s a
  obtain ⟨hG, Z, i, T, f, hf, hz, _, hi, _, hiscalar, hfpts, m, hm, hmf, hms, hmpts,
    hrescale, J, eJ, r, hJ, hJfin, _, hμpts, hJpts, hJet⟩ :=
    LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny.generalLinearCentralIsogeny
      k n hn G S M g s a
  have hcentral : Centralizes (𝟙 G.val) Z.inclusion.hom.hom :=
    (hz _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨⟨P⟩, hP⟩ := LinearAlgebraicGroups.HomogeneousQuotient.homogeneousQuotient k G Z
  obtain ⟨_, Q, _, q, _, e, _, hqk, _, _, he⟩ :=
    LinearAlgebraicGroups.HomogeneousQuotient.quotientAffineComparison G Z P
      (normalOfCentral Z hcentral)
  obtain ⟨hqf, hqs, hql, hqrep⟩ := iso_projection_properties P q e he
  have hzSmooth : Smooth Z.group.X.hom :=
    torus_smooth (Specs.Unipotent.closedSubgroupAlgebraicGroup Z) (scalarCentreIsTorus i a)
  have hqSmooth : Smooth q.hom.hom.left := by
    haveI : Smooth P.projection.left := quotientSmooth G P hzSmooth
    haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
    rw [← show P.projection.left ≫ e.hom.left = q.hom.hom.left from congrArg (·.left) he]
    exact smooth_comp _ _
  let A : ScalarQuotient g s a :=
    ⟨Z, i, hiscalar, Q, q, ⟨hz, hqk, hqrep, hqf, hqs, hql⟩, hqSmooth,
      reductive_of_central_quotient hG.1 hqk hz hqf hqs hql,
      P, (hP P).1, e, he, f, hfpts⟩
  letI : IsIso T.inclusion := hi
  have hpb : IsPullback (secondProjection T.group S.val).hom.hom m.hom.hom
      A.map.hom.hom q.hom.hom := by
    rw [hm]
    exact multiplication_pullback f q hqk T.group (asIso T.inclusion)
  have hpbs : IsPullback (secondProjection T.group S.val).hom.hom.left m.hom.hom.left
      A.map.hom.hom.left q.hom.hom.left := hpb.map (Over.forget _)
  haveI : Flat A.map.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hpbs.flip
      ⟨⟨hqs, hqf⟩, hql⟩ hmf
  haveI : Surjective A.map.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Surjective)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hpbs.flip
      ⟨⟨hqs, hqf⟩, hql⟩ hms
  obtain ⟨N, hNgroup, hN, eN, hNinc⟩ := transport_kernel hpb hJ
  haveI : IsFinite N.group.X.hom := by rw [hNgroup]; exact hJfin
  haveI : IsClosedImmersion f.hom.hom.left := hf
  haveI : Mono f.hom.hom := Over.mono_of_mono_left _
  haveI : IsAffine S.val.X.left := S.property.1
  haveI : IsAffine Q.val.X.left := Q.property.1
  haveI : LocallyOfFiniteType S.val.X.hom := S.property.2.1
  haveI : LocallyOfFiniteType (A.map.hom.hom.left ≫ Q.val.X.hom) := by
    rw [show A.map.hom.hom.left ≫ Q.val.X.hom = S.val.X.hom from Over.w A.map.hom.hom]
    infer_instance
  haveI : LocallyOfFiniteType A.map.hom.hom.left := locallyOfFiniteType_of_comp _ Q.val.X.hom
  have hfinite : IsFinite A.map.hom.hom.left := finite_of_kernel_finite A.map hN
  have hcentralN := kernel_central f q hqk hz hN
  refine ⟨A, ⟨hfinite, inferInstance, inferInstance, N, hN, hcentralN⟩,
    ?_, ⟨T, hi, m, hpb, hmf, hms, hmpts, ?_⟩⟩
  · let c := (groupPointsFunctor k).mapIso (eN ≪≫ eJ) ≪≫ r ≪≫ invertRoots k n
    let V := Specs.Unipotent.closedSubgroupAlgebraicGroup N
    letI : NeZero n := ⟨hn.ne'⟩
    let rootGroup := Specs.DiagonalizableGroups.diagonalGroup k
      (ULift.{u} (Multiplicative (ZMod n)))
    let e := groupIsoOfPoints (G := V) (H := rootGroup) (c ≪≫ r.symm)
    have he : (groupPointsFunctor k).mapIso e ≪≫ r = c := by
      apply Iso.ext
      change (groupPointsFunctor k).map e.hom ≫ r.hom = c.hom
      have hmap := Classical.choose_spec ((groupHomComparison k V.val rootGroup.val V.property.1).2
        (c ≪≫ r.symm).hom)
      rw [show (groupPointsFunctor k).map e.hom = (c ≪≫ r.symm).hom from hmap]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, r.inv_hom_id, Category.comp_id]
    have hscalar (R : TestAlgebra k) (x : Points N.group.X R) :
        Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
          Matrix.GeneralLinearGroup.scalar (Index.{u} n) (c.hom.app R x).val := by
      let y : Points J.group.X R := pointMap eN.hom R x
      have h := (hJpts R y).2
      have hl : Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap N.inclusion R x)) =
        Matrix.SpecialLinearGroup.toGL (s.hom.app R (pointMap (J.inclusion ≫
          secondProjection T.group S.val) R y)) := by
        rw [hNinc]
        rfl
      rw [hl, h]
      apply congrArg (Matrix.GeneralLinearGroup.scalar (Index.{u} n))
      change (((r.hom.app R) (pointMap eJ.hom R y)).val)⁻¹ =
        ((r.hom.app R) (pointMap ((eN ≪≫ eJ).hom) R x)).val⁻¹
      rfl
    refine ⟨N, e, r, hN, inferInstance,
      matrix_centre_of_scalar_kernel hn s N hcentralN c hscalar, hμpts, ?_, ?_⟩
    · rw [he]
      exact hscalar
    · intro p _ hp hpn
      have hnsm : ¬ Smooth N.group.X.hom := by
        intro hsm
        letI : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k hp.ne'⟩
        letI := hsm
        let i := (eN ≪≫ eJ).inv
        letI : IsIso i.hom.hom.left :=
          Functor.map_isIso ((Grp.forget (SchemeOver k)) ⋙ Over.forget _) i
        have hμ : Smooth (specGroup (Specs.SmoothnessAndIsogenies.rootsOfUnityCoordinates k n)).X.hom := by
          rw [← Over.w i.hom.hom]
          infer_instance
        exact LinearAlgebraicGroups.SmoothnessAndIsogenies.rootsOfUnityNonreduced k p n hn hpn
          ((affine_isReduced_iff _).mpr (reducedOfSmoothHopf _ hμ))
      exact ⟨hnsm, fun het => hJet p hp hpn (hNgroup ▸ het)⟩
  · intro R x
    let d := Matrix.GeneralLinearGroup.det (g.hom.app R x)
    obtain ⟨hfin, hfaith, z, v, hz, hpow, hscalar, hmatrix, hv⟩ := hrescale R x
    let Z₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup Z
    letI : IsAffine T.group.X.left :=
      (Specs.Unipotent.closedSubgroupAlgebraicGroup (G := Z₀) T).property.1
    let t := asIso T.inclusion ≪≫ i.symm
    exact ⟨(Polynomial.monic_X_pow_sub_C (d : R) hn.ne').free_adjoinRoot, hfin, hfaith,
      z, v, hz, hpow, hscalar, hmatrix, hv,
      scalar_rescaling_fibre g s a t m hmpts R x hz hscalar hv⟩


section Lie

open Specs.StandardGroups (multiplicativePoints)
open private matrixDual_kernel from LinearAlgebraicGroups.Affine.LieBracket

local notation "dual" => CommAlgCat.of k (DualNumber k)
private abbrev Matrix₂ (k : Type u) := Matrix (Index.{u} 2) (Index.{u} 2) k

variable {G S M : Specs.AffineAlgebraicGroup k}
variable {g : MatrixPoints G 2} {s : SpecialMatrixPoints S 2}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

private theorem smooth_differential_surjective {G H : Specs.GroupScheme k}
    (f : G ⟶ H) (hf : Smooth f.hom.hom.left) :
    Function.Surjective (mapPointKernel f) := by
  letI := hf
  intro y
  have hy : mapPoints (dualReduction k) y.toMul.val = (1 : Points G.X _) ≫ f.hom.hom :=
    y.toMul.property.trans (MonObj.one_comp _).symm
  obtain ⟨x, hx, hxy⟩ := smooth_lift_dual f.hom.hom _ _ hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

private theorem pointKernel_comp {G H I : Specs.GroupScheme k}
    (f : G ⟶ H) (g : H ⟶ I) (x : Lie k G) :
    mapPointKernel (f ≫ g) x = mapPointKernel g (mapPointKernel f x) :=
  (lieFunctoriality k).2.2 _ _ _ f g x

private theorem pointKernel_iso_surjective {G H : Specs.GroupScheme k} (e : G ≅ H) :
    Function.Surjective (mapPointKernel e.hom) := by
  intro x
  refine ⟨mapPointKernel e.inv x, ?_⟩
  rw [← pointKernel_comp, e.inv_hom_id]
  exact (lieFunctoriality k).2.1 _ _

private theorem gl_tangent_entries (g : MatrixPoints G 2)
    (x : Lie k G.val) (i j : Index.{u} 2) :
    (g.hom.app dual x.toMul.val).val i j =
      ((1 : Matrix₂ k) i j, glTangentCoefficient g x i j) := by
  apply TrivSqZeroExt.ext
  · exact congrArg (fun A : DualNumber (Matrix₂ k) => A.fst i j)
      (matrixDual_kernel (mapDualKernel g.hom x))
  · rfl

private theorem gl_sl_coefficient (Q : ScalarQuotient g s a) (x : Lie k S.val) :
    glTangentCoefficient g (mapPointKernel Q.f x) = slTangentCoefficient s x := by
  ext i j
  change ((g.hom.app dual (pointMap Q.f dual x.toMul.val)).val i j).snd =
    ((s.hom.app dual x.toMul.val).val i j).snd
  rw [Q.f_eq]
  rfl

private theorem gl_scalar_coefficient (Q : ScalarQuotient g s a) (x : Lie k M.val) :
    glTangentCoefficient g (mapPointKernel (Q.scalarIso.hom ≫ Q.Z.inclusion) x) =
      ((a.hom.app dual x.toMul.val).val.snd) • (1 : (Matrix₂ k)) := by
  ext i j
  change ((g.hom.app dual (pointMap (Q.scalarIso.hom ≫ Q.Z.inclusion) dual x.toMul.val)).val i j).snd = _
  rw [Q.scalar_eq, Matrix.GeneralLinearGroup.coe_scalar]
  by_cases hij : i = j
  · subst j
    simp [Matrix.scalar, Matrix.diagonal_apply_eq]
  · simp [Matrix.scalar, hij]

private theorem lie_scheme_kernel {G H : Specs.GroupScheme k} {N : Specs.ClosedSubgroup G}
    {f : G ⟶ H} (hN : IsSchemeKernel f N) :
    Function.Injective (mapPointKernel N.inclusion) ∧
      Set.range (mapPointKernel N.inclusion) = {x | mapPointKernel f x = 0} := by
  let E := Grp.trivial (SchemeOver k)
  let t : N.group ⟶ E := default
  let e : E ⟶ H := default
  let F := Grp.forget (SchemeOver k)
  have ht : F.map t = toUnit N.group.X := (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  have hp : IsPullback (F.map N.inclusion) (F.map t) (F.map f) (F.map e) := by
    rw [ht]
    exact hN
  exact lieKernelComparison k (Grp.isZero_trivial (SchemeOver k)).isTerminal
    (hp.of_map_of_faithful F)

private theorem projective_tangent_lifts_eq (Q : ScalarQuotient g s a) (x y : Lie k G.val) :
    mapPointKernel Q.q y = mapPointKernel Q.q x ↔
      ∃ z : Lie k M.val, y = mapPointKernel (Q.scalarIso.hom ≫ Q.Z.inclusion) z + x := by
  have hr := (lie_scheme_kernel Q.adjoint.2.1).2
  constructor
  · intro h
    have hdiff : y - x ∈ Set.range (mapPointKernel Q.Z.inclusion) := by
      rw [hr]
      change mapPointKernel Q.q (y - x) = 0
      rw [map_sub, h, sub_self]
    obtain ⟨z, hz⟩ := hdiff
    obtain ⟨w, rfl⟩ := pointKernel_iso_surjective Q.scalarIso z
    refine ⟨w, ?_⟩
    rw [pointKernel_comp, hz, sub_add_cancel]
  · rintro ⟨w, rfl⟩
    have hmem : mapPointKernel Q.Z.inclusion (mapPointKernel Q.scalarIso.hom w) ∈
        Set.range (mapPointKernel Q.Z.inclusion) := Set.mem_range_self _
    rw [hr] at hmem
    have hzero : mapPointKernel Q.q
        (mapPointKernel Q.Z.inclusion (mapPointKernel Q.scalarIso.hom w)) = 0 := hmem
    rw [map_add, pointKernel_comp, hzero, zero_add]

private theorem gl_differential_kernel (Q : ScalarQuotient g s a) (x : Lie k G.val) :
    mapPointKernel Q.q x = 0 ↔ glTangentCoefficient g x ∈ scalarLine k 2 := by
  obtain ⟨bG⟩ := (show Nonempty (IdentityLieStructure G.val) from identityLieBracket k G)
  obtain ⟨bM⟩ := (show Nonempty (IdentityLieStructure M.val) from identityLieBracket k M)
  letI : AddCommGroup (Lie k G.val) := bG.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := bG.lieAlgebra.toModule
  letI : AddCommGroup (Lie k M.val) := bM.lieRing.toAddCommGroup
  letI : Module k (Lie k M.val) := bM.lieAlgebra.toModule
  obtain ⟨dG, hdG, _⟩ := lieGeneralLinear k (Index.{u} 2) G g bG
  obtain ⟨dM, hdM, _⟩ := lieMultiplicativeGroup k M a bM
  have hr := (lie_scheme_kernel Q.adjoint.2.1).2
  change Set.range (mapPointKernel Q.Z.inclusion) = {p | mapPointKernel Q.q p = 0} at hr
  have hz (y : Lie k M.val) :
      glTangentCoefficient g (mapPointKernel Q.Z.inclusion (mapPointKernel Q.scalarIso.hom y)) =
        dM y • (1 : (Matrix₂ k)) := by
    rw [← pointKernel_comp, gl_scalar_coefficient, hdM]
  rw [← show x ∈ {p | mapPointKernel Q.q p = 0} ↔ mapPointKernel Q.q x = 0 from Iff.rfl,
    ← hr]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := pointKernel_iso_surjective Q.scalarIso z
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨y, hy⟩ := dM.surjective c
    refine ⟨mapPointKernel Q.scalarIso.hom y, dG.injective ?_⟩
    rw [hdG, hdG, hz, hy, hc]

/-- The tangent map to the scalar quotient is the class map on matrices. -/
theorem projectiveLieComparison : ProjectiveLieComparison.{u} := by
  intro k _ G S M g s a Q b
  letI : IsAffine Q.P.val.X.left := Q.P.property.1
  letI : IsAffine G.val.X.left := G.property.1
  obtain ⟨bG⟩ := identityLieBracket k G
  letI : LieRing (Lie k Q.P.val) := b.lieRing
  letI : LieAlgebra k (Lie k Q.P.val) := b.lieAlgebra
  letI : LieRing (Lie k G.val) := bG.lieRing
  letI : LieAlgebra k (Lie k G.val) := bG.lieAlgebra
  letI : AddCommGroup (Lie k Q.P.val) := b.lieRing.toAddCommGroup
  letI : Module k (Lie k Q.P.val) := b.lieAlgebra.toModule
  letI : AddCommGroup (Lie k G.val) := bG.lieRing.toAddCommGroup
  letI : Module k (Lie k G.val) := bG.lieAlgebra.toModule
  obtain ⟨dG, hdG, hdGbracket⟩ := lieGeneralLinear k (Index.{u} 2) G g bG
  obtain ⟨dq, hdq⟩ := identityDifferentialLieHom k G.val Q.P.val Q.q bG b
  let L : (Matrix₂ k) →ₗ[k] Lie k Q.P.val := dq.toLinearMap.comp dG.symm.toLinearMap
  have hL (x : Lie k G.val) : L (dG x) = mapPointKernel Q.q x := by
    change dq (dG.symm (dG x)) = _
    rw [LinearEquiv.symm_apply_apply, hdq]
  have hlift := smooth_differential_surjective Q.q Q.smooth
  have hsur : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := hlift y
    exact ⟨dG x, (hL x).trans hx⟩
  have hker : LinearMap.ker L = scalarLine k 2 := by
    ext A
    obtain ⟨x, rfl⟩ := dG.surjective A
    rw [LinearMap.mem_ker, hL, hdG]
    have hzero := congrArg (fun A : AddGroup (PointKernel Q.P.val) => A.toZero.zero) b.group_law
    exact (Iff.of_eq (congrArg (fun z => mapPointKernel Q.q x = z) hzero)).trans
      (gl_differential_kernel Q x)
  let e := (L.quotKerEquivOfSurjective hsur).symm.trans (Submodule.quotEquivOfEq _ _ hker)
  have hclass (x : Lie k G.val) :
      e (mapPointKernel Q.q x) = (scalarLine k 2).mkQ (glTangentCoefficient g x) := by
    rw [← hL]
    change (Submodule.quotEquivOfEq _ _ hker)
      ((L.quotKerEquivOfSurjective hsur).symm (L (dG x))) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.quotEquivOfEq_mk]
    exact congrArg (scalarLine k 2).mkQ (hdG x)
  refine ⟨hlift, gl_tangent_entries g, projective_tangent_lifts_eq Q, e, hclass, ?_, ?_⟩
  · intro x
    change e (mapPointKernel (Q.f ≫ Q.q) x) = _
    rw [pointKernel_comp, hclass, gl_sl_coefficient Q]
  · intro x y
    change e (b.lieRing.toBracket.bracket (mapPointKernel Q.q x) (mapPointKernel Q.q y)) = _
    rw [← identityLieBracketNaturality k G.val Q.P.val Q.q bG b x y, hclass,
      ← hdG (bG.lieRing.toBracket.bracket x y), hdGbracket x y, hdG x, hdG y]

/-- In characteristic two, the tangent space of the scheme kernel is the scalar line. -/
theorem projectiveLieKernelInCharacteristicTwo : ProjectiveLieKernelInCharacteristicTwo.{u} := by
  intro k _ _ G S M g s a Q hkernel
  have hclass (x : Lie k S.val) :
      mapPointKernel Q.map x = 0 ↔ slTangentCoefficient s x ∈ scalarLine k 2 := by
    change mapPointKernel (Q.f ≫ Q.q) x = 0 ↔ _
    rw [pointKernel_comp, gl_differential_kernel Q, gl_sl_coefficient Q]
  obtain ⟨N, eN, _, hN, _, _, _, _, _⟩ := hkernel
  refine ⟨hclass, N, eN, hN, ?_⟩
  intro b
  haveI : IsAffine N.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup N).property.1
  haveI : IsAffine S.val.X.left := S.property.1
  obtain ⟨bS⟩ := identityLieBracket k S
  letI : LieRing (Lie k N.group) := b.lieRing
  letI : LieAlgebra k (Lie k N.group) := b.lieAlgebra
  letI : LieRing (Lie k S.val) := bS.lieRing
  letI : LieAlgebra k (Lie k S.val) := bS.lieAlgebra
  letI : AddCommGroup (Lie k N.group) := b.lieRing.toAddCommGroup
  letI : Module k (Lie k N.group) := b.lieAlgebra.toModule
  letI : AddCommGroup (Lie k S.val) := bS.lieRing.toAddCommGroup
  letI : Module k (Lie k S.val) := bS.lieAlgebra.toModule
  obtain ⟨dS, hdS, _⟩ := lieSpecialLinear k (Index.{u} 2) S s bS
  obtain ⟨di, hdi⟩ := identityDifferentialLieHom k N.group S.val N.inclusion b bS
  obtain ⟨hinj, hr⟩ := lie_scheme_kernel hN
  let j : Index.{u} 2 := ⟨0⟩
  let entry : LinearMap.ker (Matrix.traceLinearMap (Index.{u} 2) k k) →ₗ[k] k :=
    ⟨⟨fun A => A.val j j, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  let L : Lie k N.group →ₗ[k] k := entry.comp (dS.toLinearMap.comp di.toLinearMap)
  have hcoord (z : Lie k N.group) : L z = slTangentCoefficient s (mapPointKernel N.inclusion z) j j := by
    change (dS (di z)).val j j = _
    rw [hdS, hdi]
  have hmat (z : Lie k N.group) :
      slTangentCoefficient s (mapPointKernel N.inclusion z) = L z • 1 := by
    have hz : mapPointKernel N.inclusion z ∈ Set.range (mapPointKernel N.inclusion) := ⟨z, rfl⟩
    rw [hr] at hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
      ((hclass _).mp (show mapPointKernel Q.map (mapPointKernel N.inclusion z) = 0 from hz))
    rw [hcoord, ← hc]
    have he : ((c • (1 : Matrix₂ k)) j j) = c := by simp
    rw [he]
  have hs : Function.Surjective L := by
    intro c
    let A : Matrix₂ k := c • 1
    have hA : A ∈ LinearMap.ker (Matrix.traceLinearMap (Index.{u} 2) k k) := by
      change Matrix.trace A = 0
      have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
      simp [A, Matrix.trace_smul, Matrix.trace_one, Fintype.card_ulift, htwo]
    let x := dS.symm ⟨A, hA⟩
    have hx : slTangentCoefficient s x = A := by
      rw [← hdS]
      exact congrArg Subtype.val (dS.apply_symm_apply ⟨A, hA⟩)
    have hk : x ∈ Set.range (mapPointKernel N.inclusion) := by
      rw [hr]
      apply (hclass _).mpr
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    obtain ⟨z, hz⟩ := hk
    refine ⟨z, ?_⟩
    rw [hcoord, hz, hx]
    simp [A]
  have hi : Function.Injective L := by
    intro x y hxy
    apply hinj
    apply dS.injective
    apply Subtype.ext
    rw [hdS, hdS, hmat, hmat, hxy]
  exact ⟨LinearEquiv.ofBijective L ⟨hi, hs⟩, hmat⟩

end Lie


section Ratio

open Specs.StandardGroups (multiplicativePoints generalLinearPoints)
open Specs.GeneralLinearStructure (IsDiagonal)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Matrix

open private diagonalMatrixHom diagonalMatrixHom_val diagonal_units_surjective isIso_of_bijective_points
  from LinearAlgebraicGroups.Reductive.GeneralLinearStructure
open private liftPointGroupHom from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private productAlgebraicGroup from LinearAlgebraicGroups.Reductive.CentralDerived
open private scheme_hom_spec from LinearAlgebraicGroups.Unipotent.CentralSeries
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private geometricallyMaximal_image from LinearAlgebraicGroups.Classification.CentralIsogenies

variable {G S M : Specs.AffineAlgebraicGroup k}
variable {g : MatrixPoints G 2} {s : SpecialMatrixPoints S 2}
variable {a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k}

private theorem pointMap_comp {F H J : Specs.GroupScheme k} (f : F ⟶ H) (h : H ⟶ J)
    (R : TestAlgebra k) (x : Points F.X R) :
    pointMap (f ≫ h) R x = pointMap h R (pointMap f R x) := rfl

private def ratioEntries {R : Type u} [CommRing R] (z : Rˣ) (i : Index.{u} 2) : Rˣ :=
  if i = firstIndex then z else 1

private theorem ratioEntries_one_or_last (i : Index.{u} 2) : i = firstIndex ∨ i = lastIndex := by
  rcases i with ⟨i⟩
  fin_cases i <;> simp [firstIndex, lastIndex]

private def ratioMatrices (k : Type u) [Field k] :
    multiplicativePoints k ⟶ generalLinearPoints k (Index.{u} 2) where
  app R := GrpCat.ofHom ((diagonalMatrixHom _ R).comp
    { toFun := ratioEntries
      map_one' := by funext i; simp [ratioEntries]
      map_mul' := by intro x y; funext i; by_cases hi : i = firstIndex <;> simp [ratioEntries, hi] })
  naturality R A f := by
    apply GrpCat.ext
    intro z
    apply Units.ext
    change (diagonalMatrixHom _ A (ratioEntries (Units.map f.hom.toMonoidHom z))).val =
      ((diagonalMatrixHom _ R (ratioEntries z)).val).map f.hom
    rw [diagonalMatrixHom_val, diagonalMatrixHom_val, diagonal_map (map_zero f.hom)]
    congr 1
    funext i
    by_cases hi : i = firstIndex <;> simp [ratioEntries, hi]

private def ratioSection (g : MatrixPoints G 2)
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k) : M.val ⟶ G.val :=
  (AffineAlgebraicGroup.groupHomEquiv M G).symm (a.hom ≫ ratioMatrices k ≫ g.inv)

private theorem ratioSection_point (R : TestAlgebra k) (x : Points M.val.X R) :
    g.hom.app R (pointMap (ratioSection g a) R x) =
      diagonalMatrixHom _ R (ratioEntries (a.hom.app R x)) := by
  unfold ratioSection
  rw [show pointMap ((AffineAlgebraicGroup.groupHomEquiv M G).symm
      (a.hom ≫ ratioMatrices k ≫ g.inv)) R x = (a.hom ≫ ratioMatrices k ≫ g.inv).app R x
      from scheme_hom_spec _ R x]
  exact (g.app R).groupIsoToMulEquiv.apply_symm_apply _

private theorem scalar_mul_ratio {R : Type u} [CommRing R] (w z : Rˣ) :
    (GeneralLinearGroup.scalar (Index.{u} 2) w * diagonalMatrixHom _ R (ratioEntries z)).val =
      Matrix.diagonal (fun i => ((w * ratioEntries z i : Rˣ) : R)) := by
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar, diagonalMatrixHom_val]
  change Matrix.diagonal _ * Matrix.diagonal _ = _
  rw [Matrix.diagonal_mul_diagonal]
  rfl

private theorem diag_entries_unique {R : Type u} [CommRing R] {w z v t : Rˣ}
    (h : Matrix.diagonal (fun i => ((w * ratioEntries z i : Rˣ) : R)) =
      Matrix.diagonal (fun i => ((v * ratioEntries t i : Rˣ) : R))) : w = v ∧ z = t := by
  have hw : w = v := Units.ext (by
    simpa [ratioEntries, firstIndex, lastIndex] using congrArg (fun A => A lastIndex lastIndex) h)
  have hz : w * z = v * t := Units.ext (by
    simpa [ratioEntries] using congrArg (fun A => A firstIndex firstIndex) h)
  exact ⟨hw, mul_left_cancel (by simpa [hw] using hz : v * z = v * t)⟩

private abbrev ScalarRatioProduct (Q : ScalarQuotient g s a) :=
  productAlgebraicGroup (Specs.Unipotent.closedSubgroupAlgebraicGroup Q.Z) M

private abbrev scalarFactor (Q : ScalarQuotient g s a) :=
  firstProjection Q.Z.group M.val ≫ Q.Z.inclusion

private abbrev ratioFactor (Q : ScalarQuotient g s a) :=
  secondProjection Q.Z.group M.val ≫ ratioSection g a

private def diagonalProductPoints (Q : ScalarQuotient g s a) :
    (groupPointsFunctor k).obj (ScalarRatioProduct Q).val ⟶ (groupPointsFunctor k).obj G.val :=
  let F := groupPointsFunctor k
  let A := ScalarRatioProduct Q
  let f := F.map (scalarFactor Q)
  let h := F.map (ratioFactor Q)
  { app := fun R => GrpCat.ofHom {
      toFun := fun x => (f.app R).hom x * (h.app R).hom x
      map_one' := by rw [map_one, map_one, mul_one]
      map_mul' := by
        intro x y
        rw [map_mul, map_mul]
        have hc : Commute ((f.app R).hom y) ((h.app R).hom x) := by
          change Commute (y ≫ (scalarFactor Q).hom.hom) (x ≫ (ratioFactor Q).hom.hom)
          exact (centre_mul_comm Q.adjoint.1 _ (y ≫ (firstProjection Q.Z.group M.val).hom.hom)).symm
        exact hc.mul_mul_mul_comm ((f.app R).hom x) ((h.app R).hom y) }
    naturality := by
      intro R B b
      apply GrpCat.ext
      intro x
      change f.app B (mapPoints b x) * h.app B (mapPoints b x) =
        (((groupPointsFunctor k).obj G.val).map b).hom (f.app R x * h.app R x)
      rw [map_mul]
      exact congrArg₂ (· * ·)
        (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (f.naturality b)) x)
        (DFunLike.congr_fun (congrArg GrpCat.Hom.hom (h.naturality b)) x) }

private theorem diagonalProductPoints_val (Q : ScalarQuotient g s a)
    (R : TestAlgebra k) (x : Points (ScalarRatioProduct Q).val.X R) :
    let w : Rˣ := a.hom.app R (pointMap (firstProjection Q.Z.group M.val ≫ Q.scalarIso.inv) R x)
    let z : Rˣ := a.hom.app R (pointMap (secondProjection Q.Z.group M.val) R x)
    (g.hom.app R ((diagonalProductPoints Q).app R x)).val =
      Matrix.diagonal (fun i => ((w * ratioEntries z i : Rˣ) : R)) := by
  change (g.hom.app R (pointMap (scalarFactor Q) R x * pointMap (ratioFactor Q) R x)).val = _
  rw [show g.hom.app R (pointMap (scalarFactor Q) R x * pointMap (ratioFactor Q) R x) =
      g.hom.app R (pointMap (scalarFactor Q) R x) * g.hom.app R (pointMap (ratioFactor Q) R x)
    from map_mul (g.hom.app R).hom _ _]
  rw [show scalarFactor Q = (firstProjection Q.Z.group M.val ≫ Q.scalarIso.inv) ≫
        (Q.scalarIso.hom ≫ Q.Z.inclusion) by simp [scalarFactor, Category.assoc],
    pointMap_comp _ (Q.scalarIso.hom ≫ Q.Z.inclusion), Q.scalar_eq]
  change ((GeneralLinearGroup.scalar (Index.{u} 2) _ : GeneralLinearGroup (Index.{u} 2) R) *
    (show GeneralLinearGroup (Index.{u} 2) R from
      g.hom.app R (pointMap (secondProjection Q.Z.group M.val ≫ ratioSection g a) R x))).val = _
  rw [pointMap_comp (secondProjection Q.Z.group M.val) (ratioSection g a), ratioSection_point]
  exact scalar_mul_ratio _ _

private theorem diagonalProductIso (Q : ScalarQuotient g s a) (D : Specs.ClosedSubgroup G.val)
    (hD : ∀ (R : TestAlgebra k) (x : Points G.val.X R),
      x ∈ SubgroupSections D ((testSpec k).obj (op R)) ↔ IsDiagonal (g.hom.app R x)) :
    ∃ e : (Q.Z.group ⊗ M.val) ≅ D.group,
      e.hom.hom.hom ≫ D.inclusion.hom.hom =
        (fst Q.Z.group.X M.val.X ≫ Q.Z.inclusion.hom.hom) *
          (snd Q.Z.group.X M.val.X ≫ (ratioSection g a).hom.hom) := by
  let E := ScalarRatioProduct Q
  let D₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup D
  have hlift (R : TestAlgebra k) (x : Points E.val.X R) :
      ∃ y : Points D.group.X R, pointMap D.inclusion R y = (diagonalProductPoints Q).app R x := by
    apply (hD R _).mpr
    intro i j hij
    rw [diagonalProductPoints_val, Matrix.diagonal_apply_ne _ hij]
  obtain ⟨d, hd⟩ := liftPointGroupHom E.property.1 D (diagonalProductPoints Q) hlift
  have hpt (R : TestAlgebra k) (x : Points E.val.X R) :
      pointMap (d ≫ D.inclusion) R x = (diagonalProductPoints Q).app R x :=
    congrArg (fun τ => τ.app R x) hd
  have hmono : Mono D.inclusion.hom.hom := by
    haveI := D.isClosedImmersion
    exact Over.mono_of_mono_left _
  have hbij (R : TestAlgebra k) : Function.Bijective (pointMap d R) := by
    constructor
    · intro x y hxy
      have hh : (diagonalProductPoints Q).app R x = (diagonalProductPoints Q).app R y := by
        rw [← hpt R x, ← hpt R y, pointMap_comp, pointMap_comp, hxy]
      have hm := congrArg (fun p => (g.hom.app R p).val) hh
      rw [diagonalProductPoints_val, diagonalProductPoints_val] at hm
      obtain ⟨hw, hz⟩ := diag_entries_unique hm
      apply CartesianMonoidalCategory.hom_ext
      · have hi : IsIso Q.scalarIso.inv.hom.hom := (Grp.forget _).map_isIso Q.scalarIso.inv
        apply (cancel_mono Q.scalarIso.inv.hom.hom).mp
        exact (a.app R).groupIsoToMulEquiv.injective hw
      · exact (a.app R).groupIsoToMulEquiv.injective hz
    · intro y
      obtain ⟨z, hz⟩ := diagonal_units_surjective (g.hom.app R (pointMap D.inclusion R y))
        ((hD R _).mp ⟨y, rfl⟩)
      let w := z lastIndex
      let t := z firstIndex / w
      let p := (a.app R).groupIsoToMulEquiv.symm w ≫ Q.scalarIso.hom.hom.hom
      let q := (a.app R).groupIsoToMulEquiv.symm t
      let x : Points E.val.X R := lift p q
      refine ⟨x, (cancel_mono D.inclusion.hom.hom).mp ?_⟩
      change pointMap (d ≫ D.inclusion) R x = pointMap D.inclusion R y
      apply (g.app R).groupIsoToMulEquiv.injective
      apply Units.ext
      change (g.hom.app R (pointMap (d ≫ D.inclusion) R x)).val =
        (g.hom.app R (pointMap D.inclusion R y)).val
      rw [hpt R x, diagonalProductPoints_val Q R x, ← hz, diagonalMatrixHom_val]
      have hw : a.hom.app R (pointMap (firstProjection Q.Z.group M.val ≫ Q.scalarIso.inv) R x) = w := by
        change (a.app R).groupIsoToMulEquiv ((lift p q ≫ fst _ _) ≫ Q.scalarIso.inv.hom.hom) = _
        rw [lift_fst]
        change (a.app R).groupIsoToMulEquiv
          (((a.app R).groupIsoToMulEquiv.symm w ≫ Q.scalarIso.hom.hom.hom) ≫ Q.scalarIso.inv.hom.hom) = _
        have he := congrArg (fun f : M.val ⟶ M.val => f.hom.hom) Q.scalarIso.hom_inv_id
        rw [Category.assoc, show Q.scalarIso.hom.hom.hom ≫ Q.scalarIso.inv.hom.hom = 𝟙 _ from he,
          Category.comp_id, MulEquiv.apply_symm_apply]
      have ht : a.hom.app R (pointMap (secondProjection Q.Z.group M.val) R x) = t := by
        change (a.app R).groupIsoToMulEquiv (lift p q ≫ snd _ _) = _
        rw [lift_snd]
        exact MulEquiv.apply_symm_apply _ _
      rw [hw, ht]
      congr 1
      funext i
      rcases ratioEntries_one_or_last i with rfl | rfl
      · simp [ratioEntries, t, div_eq_mul_inv, mul_left_comm, mul_inv_cancel]
      · simp [ratioEntries, w, firstIndex, lastIndex]
  haveI : IsIso d := isIso_of_bijective_points (G := E) (H := D₀) d hbij
  refine ⟨asIso d, ?_⟩
  apply hom_ext_of_points E.property.1
  intro R x
  change pointMap (d ≫ D.inclusion) R x = _
  rw [hpt]
  change pointMap (scalarFactor Q) R x * pointMap (ratioFactor Q) R x = _
  rw [MonObj.comp_mul]
  rfl


private theorem closed_descends_affine {V X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    {fst : V ⟶ X} {snd : V ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hf : Flat f) (hs : Surjective f)
    (hc : IsClosedImmersion fst) : IsClosedImmersion g := by
  letI := hf
  letI := hs
  letI := hc
  let X' := X.isoSpec
  let Y' := Y.isoSpec
  let Z' := Z.isoSpec
  let f' := X'.inv ≫ f ≫ Z'.hom
  let g' := Y'.inv ≫ g ≫ Z'.hom
  have hp : IsPullback (fst ≫ X'.hom) (snd ≫ Y'.hom) f' g' :=
    h.of_iso (Iso.refl _) X' Y' Z' (by simp) (by simp) (by simp [f']) (by simp [g'])
  have hc' : IsClosedImmersion (pullback.fst f' g') := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion hp.isoPullback.hom,
      hp.isoPullback_hom_fst]
    infer_instance
  have hspec (R A : CommRingCat.{u}) (φ : R ⟶ A) :
      IsClosedImmersion (Spec.map φ) ↔ Function.Surjective φ.hom :=
    HasAffineProperty.SpecMap_iff_of_affineAnd IsClosedImmersion.hasAffineProperty
      RingHom.surjective_respectsIso _
  have hg' : IsClosedImmersion g' := by
    apply of_pullback_fst_Spec_of_codescendsAlong (P := @IsClosedImmersion)
      (P' := @Flat ⊓ @Surjective) (f := f') (g := g') RingHom.FaithfullyFlat.codescendsAlong_surjective
      (fun h => (flat_and_surjective_SpecMap_iff _).mp h) (hspec _ _ _)
    · exact ⟨inferInstanceAs (Flat f'), inferInstanceAs (Surjective f')⟩
    · exact hc'
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ Z'.hom,
    ← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion Y'.inv]
  exact hg'

private theorem unit_group_split
    (a : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k) : IsSplitTorus M.val := by
  let B := Specs.StandardGroups.multiplicativePowerGroup k (Index.{u} 1)
  let e : multiplicativePoints k ≅ Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} 1) :=
    NatIso.ofComponents (fun R => (MulEquiv.piUnique (fun _ : Index.{u} 1 => Rˣ)).symm.toGrpIso)
      (by intro R A f; apply GrpCat.ext; intro z; rfl)
  let b := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} 1)
  exact ⟨1, ⟨groupIsoOfPoints (G := M) (H := B)
    (a ≪≫ e ≪≫ b.symm)⟩⟩

private theorem ratio_projection_flat_surj (Q : ScalarQuotient g s a) :
    Flat (secondProjection Q.Z.group M.val).hom.hom.left ∧
      Surjective (secondProjection Q.Z.group M.val).hom.hom.left := by
  haveI : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Surjective Q.Z.group.X.hom :=
    ⟨fun x => ⟨(η[Q.Z.group.X]).left (IsLocalRing.closedPoint k), Subsingleton.elim _ _⟩⟩
  change Flat (pullback.snd Q.Z.group.X.hom M.val.X.hom) ∧
    Surjective (pullback.snd Q.Z.group.X.hom M.val.X.hom)
  exact ⟨inferInstance, inferInstance⟩

/-- The split ratio torus is closed and geometrically maximal in the scalar quotient. -/
theorem projectiveRatioTorus : ProjectiveRatioTorus.{u} := by
  intro k _ G S M g s a Q
  obtain ⟨D, _, hD, _, hDsplit, _, _, _, _, _, hc, _, hDmax, _⟩ :=
    GeneralLinearStructure.generalLinearBorelPair k 2 (by decide) G g
  have hDmax' : IsGeometricallyMaximal D := ⟨hc, hDmax⟩
  obtain ⟨e, he⟩ := diagonalProductIso Q D hD
  let j := ratioSection g a ≫ Q.q
  let r := e.inv ≫ secondProjection Q.Z.group M.val
  let F := Grp.forget (SchemeOver k)
  have hp : IsPullback D.inclusion.hom.hom r.hom.hom Q.q.hom.hom j.hom.hom := by
    have hh := (multiplication_pullback (ratioSection g a) Q.q Q.adjoint.2.1
      Q.Z.group (Iso.refl _)).flip
    apply hh.of_iso (F.mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · change ((fst _ _ ≫ 𝟙 _ ≫ Q.Z.inclusion.hom.hom) *
          (snd _ _ ≫ (ratioSection g a).hom.hom)) ≫ 𝟙 _ = e.hom.hom.hom ≫ D.inclusion.hom.hom
      simpa only [Category.comp_id, Category.id_comp] using he.symm
    · change _ ≫ 𝟙 _ = F.map e.hom ≫ F.map r
      simp only [Category.comp_id, r, Functor.map_comp, ← F.map_comp_assoc, e.hom_inv_id,
        F.map_id, Category.id_comp]
      rfl
    · exact (Category.comp_id _).symm
    · rfl
  haveI : IsAffine M.val.X.left := M.property.1
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffine Q.P.val.X.left := Q.P.property.1
  have hj : IsClosedImmersion j.hom.hom.left :=
    closed_descends_affine (f := Q.q.hom.hom.left) (g := j.hom.hom.left)
      (hp.map (Over.forget _)) Q.adjoint.2.2.2.1 Q.adjoint.2.2.2.2.1 D.isClosedImmersion
  let U : Specs.ClosedSubgroup Q.P.val := ⟨M.val, j, hj⟩
  have hcomm : r ≫ U.inclusion = D.inclusion ≫ Q.q :=
    Grp.hom_ext _ _ hp.w.symm
  have hrf : Flat r.hom.hom.left := by
    haveI : IsIso e.inv.hom.hom.left := (F ⋙ Over.forget _).map_isIso e.inv
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
      (ratio_projection_flat_surj Q).1
  have hrs : Surjective r.hom.hom.left := by
    haveI : IsIso e.inv.hom.hom.left := (F ⋙ Over.forget _).map_isIso e.inv
    exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso _ _)
      (ratio_projection_flat_surj Q).2
  have hZ : IsSubgroupOf Q.Z D := by
    apply subgroupInclusionFactors (Specs.Unipotent.closedSubgroupAlgebraicGroup Q.Z).property.1
    intro R z
    obtain ⟨w, rfl⟩ := (asIso ((groupPointsFunctor k).map Q.scalarIso.hom)).app R
      |>.groupIsoToMulEquiv.surjective z
    apply (hD R _).mpr
    intro i l hil
    change (g.hom.app R (pointMap (Q.scalarIso.hom ≫ Q.Z.inclusion) R w)).val i l = 0
    rw [Q.scalar_eq, GeneralLinearGroup.coe_scalar]
    exact diagonal_apply_ne _ hil
  have hs : IsSplitTorus U.group := unit_group_split a
  have hm : IsGeometricallyMaximal U :=
    geometricallyMaximal_image G Q.P
      (GeneralLinearStructure.generalLinearReductive k 2 (by decide) G g) D hDsplit hDmax'
      U hs Q.q r ⟨hcomm, hrf, hrs⟩ Q.Z
      ⟨Q.adjoint.2.1, Q.adjoint.2.2.2.1, Q.adjoint.2.2.2.2.1,
        Q.adjoint.2.2.2.2.2, Q.adjoint.2.2.1⟩ hZ
  refine ⟨⟨D, hD, hDmax', U, hs, hm, Iso.refl _, r, hp, ?_⟩⟩
  intro R x
  let y := pointMap e.inv R x
  have hx : pointMap D.inclusion R x =
      pointMap (scalarFactor Q) R y * pointMap (ratioFactor Q) R y := by
    have hh := congrArg (fun f => y ≫ f) he
    have hi : y ≫ e.hom.hom.hom = x := ((groupPointsFunctor k).mapIso e).app R
      |>.groupIsoToMulEquiv.apply_symm_apply x
    rw [← Category.assoc, hi, MonObj.comp_mul] at hh
    exact hh
  let w : Rˣ := a.hom.app R (pointMap (firstProjection Q.Z.group M.val ≫ Q.scalarIso.inv) R y)
  let z : Rˣ := a.hom.app R (pointMap (secondProjection Q.Z.group M.val) R y)
  have hA : (g.hom.app R (pointMap D.inclusion R x)).val =
      Matrix.diagonal (fun l => ((w * ratioEntries z l : Rˣ) : R)) := by
    rw [hx]
    exact diagonalProductPoints_val Q R y
  change (z : R) * (g.hom.app R (pointMap D.inclusion R x)).val lastIndex lastIndex =
    (g.hom.app R (pointMap D.inclusion R x)).val firstIndex firstIndex
  rw [hA]
  simp [ratioEntries, show lastIndex.{u} ≠ firstIndex.{u} by decide, mul_comm]

open Specs.SpecialLinearDatum (DiagonalTorus determinantOneUnits)
open Specs.CentralIsogenies (IsTorusRestriction)
open private determinantRootLift from LinearAlgebraicGroups.Reductive.GeneralLinearCentralIsogeny
open private flatOfSurjectiveHom from LinearAlgebraicGroups.Reductive.CentralDerived

private theorem determinantOne_sizeTwo {R : Type u} [CommRing R] (z : Index.{u} 1 → Rˣ) :
    determinantOneUnits z firstIndex = (z ⟨0⟩)⁻¹ ∧
      determinantOneUnits z lastIndex = z ⟨0⟩ := by
  constructor
  · change (∏ j : Index.{u} 1, z j)⁻¹ = _
    rw [Fintype.prod_unique]
    congr 1
  · rfl

private theorem surjective_of_point_lifts {G P : Specs.AffineAlgebraicGroup k} (f : G.val ⟶ P.val)
    (h : ∀ (R : TestAlgebra k) (x : Points P.val.X R), ∃ (A : TestAlgebra k) (b : R ⟶ A),
      Surjective ((testSpec k).map b.op).left ∧
      ∃ y : Points G.val.X A, pointMap f A y = mapPoints b x) :
    Surjective f.hom.hom.left := by
  obtain ⟨R, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr P.property.1
  obtain ⟨A, b, hb, y, hy⟩ := h R.unop e.hom
  haveI := hb
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have hsur : Surjective (((testSpec k).map b.op).left ≫ e.hom.left) := inferInstance
  have heq : y.left ≫ f.hom.hom.left = ((testSpec k).map b.op).left ≫ e.hom.left :=
    congrArg (fun z => z.left) hy
  rw [← heq] at hsur
  exact Surjective.of_comp y.left f.hom.hom.left

/-- The quotient of the determinant-one diagonal is given by the square of its first entry. -/
theorem rankOneTorusRestriction : RankOneTorusRestriction.{u} := by
  intro k _ G S M g s a Q U T
  let S₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup
  let P₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup U.subgroup
  obtain ⟨i, hi⟩ : ∃ i : T.subgroup.group ⟶ U.diagonal.group,
      i ≫ U.diagonal.inclusion = T.subgroup.inclusion ≫ Q.f := by
    apply subgroupInclusionFactors S₀.property.1
    intro R x
    apply (U.diagonal_points R _).mpr
    change IsDiagonal (g.hom.app R (pointMap Q.f R (pointMap T.subgroup.inclusion R x)))
    rw [Q.f_eq]
    intro i j hij
    have h := T.matrix R x
    change (Matrix.SpecialLinearGroup.toGL
      (s.hom.app R (x ≫ T.subgroup.inclusion.hom.hom))).val i j = 0
    change (s.hom.app R (x ≫ T.subgroup.inclusion.hom.hom)).val i j = 0
    rw [h, Matrix.diagonal_apply_ne _ hij]
  let p := i ≫ U.ratio
  have hp : p ≫ U.subgroup.inclusion = T.subgroup.inclusion ≫ Q.map := by
    have hh : U.ratio ≫ U.subgroup.inclusion = U.diagonal.inclusion ≫ Q.q :=
      Grp.hom_ext _ _ U.pullback.w.symm
    change (i ≫ U.ratio) ≫ U.subgroup.inclusion = T.subgroup.inclusion ≫ (Q.f ≫ Q.q)
    rw [Category.assoc, hh, ← Category.assoc, hi, Category.assoc]
  have hpow (R : TestAlgebra k) (x : Points T.subgroup.group.X R) :
      a.hom.app R (pointMap (p ≫ U.coordinate.hom) R x) =
        (determinantOneUnits (T.pointsIso.hom.app R x) firstIndex) ^ 2 := by
    have h := U.ratio_eq R (pointMap i R x)
    have hA : (g.hom.app R (pointMap U.diagonal.inclusion R (pointMap i R x))).val =
        Matrix.diagonal (fun j => (determinantOneUnits (T.pointsIso.hom.app R x) j : R)) := by
      rw [← pointMap_comp, hi, pointMap_comp, Q.f_eq]
      exact T.matrix R x
    dsimp only at h
    rw [hA, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
    let t : Rˣ := determinantOneUnits (T.pointsIso.hom.app R x) firstIndex
    let w : Rˣ := determinantOneUnits (T.pointsIso.hom.app R x) lastIndex
    let z : Rˣ := a.hom.app R (pointMap (p ≫ U.coordinate.hom) R x)
    have hzw : z * w = t := Units.ext h
    obtain ⟨ht, hw⟩ := determinantOne_sizeTwo (T.pointsIso.hom.app R x)
    change t = _ at ht
    change w = _ at hw
    have hwt : w = t⁻¹ := by rw [hw, ht, inv_inv]
    change z = t ^ 2
    apply mul_right_cancel (b := w)
    rw [hzw, hwt, pow_two, mul_assoc, mul_inv_cancel, mul_one]
  have hsur : Surjective p.hom.hom.left := by
    apply surjective_of_point_lifts (G := S₀) (P := P₀)
    intro R x
    let d : Rˣ := a.hom.app R (pointMap U.coordinate.hom R x)
    let A := determinantRootTestAlgebra R 2 d
    let b := determinantRootMap R 2 d
    obtain ⟨_, hb, z, _, hz⟩ := determinantRootLift (by decide : 0 < 2) R d
    letI := hb
    let u : Index.{u} 1 → Aˣ := fun _ => z⁻¹
    let y := (T.pointsIso.app A).groupIsoToMulEquiv.symm u
    have hb' : Surjective ((testSpec k).map b.op).left := by
      constructor
      change Function.Surjective (PrimeSpectrum.comap (algebraMap R (determinantRootAlgebra R 2 d)))
      exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    refine ⟨A, b, hb', y, ?_⟩
    apply (((groupPointsFunctor k).mapIso U.coordinate ≪≫ a).app A).groupIsoToMulEquiv.injective
    change a.hom.app A (pointMap (p ≫ U.coordinate.hom) A y) =
      a.hom.app A (pointMap U.coordinate.hom A (mapPoints b x))
    rw [hpow]
    have he : T.pointsIso.hom.app A y = u := (T.pointsIso.app A).groupIsoToMulEquiv.apply_symm_apply u
    rw [he, (determinantOne_sizeTwo u).1, show u ⟨0⟩ = z⁻¹ from rfl, inv_inv, hz]
    exact (DFunLike.congr_fun (congrArg GrpCat.Hom.hom
      (((groupPointsFunctor k).mapIso U.coordinate ≪≫ a).hom.naturality b)) x).symm
  have hs : Smooth U.subgroup.group.X.hom :=
    torus_smooth P₀ (scalarCentreIsTorus U.coordinate.symm a)
  haveI : LocallyOfFiniteType U.subgroup.group.X.hom := P₀.property.2.1
  haveI : IsLocallyNoetherian U.subgroup.group.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian U.subgroup.group.X.hom
  haveI : LocallyOfFiniteType (p.hom.hom.left ≫ U.subgroup.group.X.hom) := by
    rw [Over.w p.hom.hom]
    exact S₀.property.2.1
  haveI : LocallyOfFiniteType p.hom.hom.left :=
    locallyOfFiniteType_of_comp p.hom.hom.left U.subgroup.group.X.hom
  exact ⟨p, ⟨hp, flatOfSurjectiveHom (A := S₀) (B := P₀) p hs hsur, hsur⟩,
    inferInstance, hpow⟩


section Lattices

open Specs.CharacterDescent (Character Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.CharacterPairing (powerMorphism pairing characterValue absoluteRoots)
open Specs.AbstractPairing (Root)
open Specs.AbstractPairing (IsAttachedCoroot)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint cocharacterPoint)
open Specs.SpecialLinearDatum (LatticeIdentification RootIdentification RootIndices root)
open Specs.Pinning (AttachedDatum)
open Specs.SpecialLinearDatum (UpperTriangularBorel)
open Specs.CentralIsogenies (characterPullback)

open private toMultiplicativeGroup toMultiplicativeGroup_points
  from LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
open private unitEquiv unitEquiv_unitPoint from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private pairing_eq_iff powerEquiv powerEquiv_apply
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private characterUnit_cocharacter from LinearAlgebraicGroups.RootData.RootGroups
open private matrixRootCharacter matrixRootCharacter_value
  from LinearAlgebraicGroups.RootData.SpecialLinearDatum

private abbrev RankOneTorus (k : Type u) [Field k] := specGroup (groupAlgebra k IntegerCharacters.{u})

private theorem gmPoints_identification {X : Specs.AffineAlgebraicGroup k}
    (d : (groupPointsFunctor k).obj X.val ≅ multiplicativePoints k)
    (R : TestAlgebra k) (t : Points X.val.X R) :
    unitEquiv R (pointMap (toMultiplicativeGroup X d).inv R t) = d.hom.app R t := by
  let e := toMultiplicativeGroup X d
  let y := pointMap e.inv R t
  have ht : pointMap e.hom R y = t := (((groupPointsFunctor k).mapIso e).app R)
    |>.groupIsoToMulEquiv.apply_symm_apply t
  have h := congrArg (fun f => f.app R y) (toMultiplicativeGroup_points X d)
  change d.hom.app R (pointMap e.hom R y) = unitEquiv R y at h
  exact h.symm.trans (congrArg (d.hom.app R) ht)

private theorem unitPoint_surjective (R : TestAlgebra k) :
    Function.Surjective (unitPoint (k := k) R) := by
  intro x
  exact ⟨unitEquiv R x, (unitEquiv R).injective (unitEquiv_unitPoint R _)⟩

private theorem gm_hom_ext {X : Specs.GroupScheme k} {f g : RankOneTorus k ⟶ X}
    (h : ∀ (R : TestAlgebra k) (z : Rˣ), cocharacterPoint f R z = cocharacterPoint g R z) : f = g := by
  apply Grp.hom_ext
  have hAffine : IsAffine (RankOneTorus k).X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra k IntegerCharacters.{u})))
    infer_instance
  apply hom_ext_of_points hAffine
  intro R t
  obtain ⟨z, rfl⟩ := unitPoint_surjective R t
  exact h R z

private theorem power_unit (n : ℤ) (R : TestAlgebra k) (z : Rˣ) :
    pointMap (powerMorphism (k := k) n) R (unitPoint R z) = unitPoint R (z ^ n) := by
  let e := 𝟙 (RankOneTorus k)
  have hpair : pairing (RankOneTorus k) (powerMorphism n) e = n :=
    (pairing_eq_iff _ _ _).mp (Category.id_comp _)
  have he : cocharacterPoint e R z = unitPoint R z := by
    change unitPoint R z ≫ 𝟙 (RankOneTorus k).X = unitPoint R z
    exact Category.comp_id _
  have h := characterUnit_cocharacter (powerMorphism n) e R z
  rw [he, hpair] at h
  apply (unitEquiv R).injective
  rw [unitEquiv_unitPoint]
  exact h

private theorem power_one :
    powerMorphism (k := k) 1 = 𝟙 (RankOneTorus k) := by
  apply gm_hom_ext
  intro R z
  change pointMap (powerMorphism 1) R (unitPoint R z) = unitPoint R z
  rw [power_unit, zpow_one]

private theorem power_comp (m n : ℤ) :
    powerMorphism (k := k) m ≫ powerMorphism n = powerMorphism (m * n) := by
  apply gm_hom_ext
  intro R z
  change pointMap (powerMorphism m ≫ powerMorphism n) R (unitPoint R z) =
    pointMap (powerMorphism (m * n)) R (unitPoint R z)
  rw [pointMap_comp, power_unit, power_unit, power_unit, _root_.zpow_mul]

private theorem dual_generators {X : Specs.GroupScheme k} (e : RankOneTorus k ≅ X) :
    DualGenerators e := by
  have hp : Function.Bijective (powerMorphism (k := k)) :=
    (funext fun n => powerEquiv_apply (k := k) n) ▸ (powerEquiv (k := k)).bijective
  refine ⟨(pairing_eq_iff _ _ _).mp (e.hom_inv_id.trans power_one.symm), ?_, ?_⟩
  · intro χ
    obtain ⟨n, hn⟩ := hp.2 (e.hom ≫ χ)
    refine ⟨n, ?_, ?_⟩
    · change χ = e.inv ≫ powerMorphism n
      rw [hn, e.inv_hom_id_assoc]
    · intro m hm
      change χ = e.inv ≫ powerMorphism m at hm
      apply hp.1
      rw [hn, hm, e.hom_inv_id_assoc]
  · intro c
    obtain ⟨n, hn⟩ := hp.2 (c ≫ e.inv)
    refine ⟨n, ?_, ?_⟩
    · change c = powerMorphism n ≫ e.hom
      rw [hn, Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro m hm
      change c = powerMorphism m ≫ e.hom at hm
      apply hp.1
      rw [hn, hm, Category.assoc, e.hom_inv_id, Category.comp_id]

private def firstUnitPoints (k : Type u) [Field k] :
    Specs.StandardGroups.multiplicativePowerPoints k (Index.{u} 1) ≅ multiplicativePoints k :=
  NatIso.ofComponents (fun R => MulEquiv.toGrpIso
    { toFun := fun z => (z ⟨0⟩)⁻¹
      invFun := fun z _ => z⁻¹
      left_inv := by
        intro z
        funext i
        change ((z ⟨0⟩ : Rˣ)⁻¹)⁻¹ = z i
        rw [inv_inv]
        exact congrArg z (Subsingleton.elim _ _)
      right_inv := inv_inv
      map_mul' := by intro x y; exact mul_inv (x ⟨0⟩ : Rˣ) (y ⟨0⟩ : Rˣ) })
    (by intro R A b; apply GrpCat.ext; intro z; exact map_inv (Units.map b.hom.toMonoidHom) _)

private abbrev sourceMark (T : DiagonalTorus s) : RankOneTorus k ≅ T.subgroup.group :=
  toMultiplicativeGroup (Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup)
    (T.pointsIso ≪≫ firstUnitPoints k)

private abbrev ratioMark (Q : ScalarQuotient g s a) (U : RatioTorus Q) :
    RankOneTorus k ≅ U.subgroup.group :=
  toMultiplicativeGroup (Specs.Unipotent.closedSubgroupAlgebraicGroup U.subgroup)
    ((groupPointsFunctor k).mapIso U.coordinate ≪≫ a)

private theorem gm_ratio_maps (Q : ScalarQuotient g s a) (U : RatioTorus Q) (T : DiagonalTorus s)
    {p : T.subgroup.group ⟶ U.subgroup.group}
    (hp : ∀ (R : TestAlgebra k) (x : Points T.subgroup.group.X R),
      a.hom.app R (pointMap (p ≫ U.coordinate.hom) R x) =
        (determinantOneUnits (T.pointsIso.hom.app R x) firstIndex) ^ 2) :
    p ≫ (ratioMark Q U).inv = (sourceMark T).inv ≫ powerMorphism 2 := by
  apply Grp.hom_ext
  apply hom_ext_of_points (Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup).property.1
  intro R x
  apply (unitEquiv R).injective
  let d := determinantOneUnits (T.pointsIso.hom.app R x) firstIndex
  have hP : unitEquiv R (pointMap (p ≫ (ratioMark Q U).inv) R x) =
      a.hom.app R (pointMap (p ≫ U.coordinate.hom) R x) :=
    gmPoints_identification (X := Specs.Unipotent.closedSubgroupAlgebraicGroup U.subgroup)
      ((groupPointsFunctor k).mapIso U.coordinate ≪≫ a) R (pointMap p R x)
  have hS : unitEquiv R (pointMap (sourceMark T).inv R x) = d :=
    (gmPoints_identification (X := Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup)
      (T.pointsIso ≪≫ firstUnitPoints k) R x).trans
        (determinantOne_sizeTwo (T.pointsIso.hom.app R x)).1.symm
  obtain ⟨z, hz⟩ := unitPoint_surjective R (pointMap (sourceMark T).inv R x)
  have hzd : z = d :=
    (unitEquiv_unitPoint R z).symm.trans ((congrArg (unitEquiv R) hz).trans hS)
  change unitEquiv R (pointMap (p ≫ (ratioMark Q U).inv) R x) =
    unitEquiv R (pointMap ((sourceMark T).inv ≫ powerMorphism 2) R x)
  rw [hP, hp, pointMap_comp, ← hz, power_unit, unitEquiv_unitPoint]
  exact (congrArg (fun r : Rˣ => r ^ (2 : ℕ)) hzd).symm

private theorem gm_forward_coordinate {X : Specs.AffineAlgebraicGroup k}
    (d : (groupPointsFunctor k).obj X.val ≅ multiplicativePoints k) (R : TestAlgebra k) (t : Rˣ) :
    d.hom.app R (cocharacterPoint (toMultiplicativeGroup X d).hom R t) = t := by
  have h := congrArg (fun f => f.app R (unitPoint R t)) (toMultiplicativeGroup_points X d)
  change _ = unitEquiv R (unitPoint R t) at h
  exact h.trans (unitEquiv_unitPoint R t)

private theorem sourceMark_entries (T : DiagonalTorus s) (R : TestAlgebra k) (t : Rˣ) :
    let d := determinantOneUnits (T.pointsIso.hom.app R (cocharacterPoint (sourceMark T).hom R t))
    d firstIndex = t ∧ d lastIndex = t⁻¹ := by
  let x := cocharacterPoint (sourceMark T).hom R t
  have ht := gm_forward_coordinate (X := Specs.Unipotent.closedSubgroupAlgebraicGroup T.subgroup)
    (T.pointsIso ≪≫ firstUnitPoints k) R t
  change (T.pointsIso.hom.app R x ⟨0⟩ : Rˣ)⁻¹ = t at ht
  have hd := determinantOne_sizeTwo (T.pointsIso.hom.app R x)
  exact ⟨hd.1.trans ht, hd.2.trans ((inv_inv _).symm.trans (congrArg Inv.inv ht))⟩

private theorem sourceMark_matrix (T : DiagonalTorus s) (R : TestAlgebra k) (t : Rˣ) :
    (s.hom.app R (pointMap T.subgroup.inclusion R (cocharacterPoint (sourceMark T).hom R t))).val =
      Matrix.diagonal (fun i => ((if i = firstIndex then t else t⁻¹ : Rˣ) : R)) := by
  let x := cocharacterPoint (sourceMark T).hom R t
  let d := determinantOneUnits (T.pointsIso.hom.app R x)
  refine (T.matrix R x).trans ?_
  change Matrix.diagonal (fun i => (d i : R)) = _
  have hd : d firstIndex = t ∧ d lastIndex = t⁻¹ := sourceMark_entries T R t
  apply congrArg Matrix.diagonal
  funext i
  rcases ratioEntries_one_or_last i with rfl | rfl
  · simp [hd.1]
  · simp [hd.2, show lastIndex.{u} ≠ firstIndex.{u} by decide]

private theorem marked_point_surjective {X : Specs.GroupScheme k} (e : RankOneTorus k ≅ X)
    (R : TestAlgebra k) : Function.Surjective (cocharacterPoint e.hom R) := by
  intro x
  obtain ⟨t, ht⟩ := unitPoint_surjective R (pointMap e.inv R x)
  refine ⟨t, ?_⟩
  change pointMap e.hom R (unitPoint R t) = x
  rw [ht]
  exact ((groupPointsFunctor k).mapIso e).app R |>.groupIsoToMulEquiv.apply_symm_apply x

private theorem marked_pairing {X : Specs.GroupScheme k} (e : RankOneTorus k ≅ X) (m n : ℤ) :
    pairing X (e.inv ≫ powerMorphism m) (powerMorphism n ≫ e.hom) = n * m := by
  apply (pairing_eq_iff _ _ _).mp
  change (powerMorphism n ≫ e.hom) ≫ e.inv ≫ powerMorphism m = powerMorphism (n * m)
  rw [Category.assoc, e.hom_inv_id_assoc, power_comp]

private theorem marked_character_value {X : Specs.GroupScheme k} (e : RankOneTorus k ≅ X)
    (m : ℤ) (R : TestAlgebra k) (t : Rˣ) :
    characterValue (e.inv ≫ powerMorphism m) R (cocharacterPoint e.hom R t) = (↑(t ^ m) : R) := by
  have hp : pairing X (e.inv ≫ powerMorphism m) e.hom = m := by
    apply (pairing_eq_iff _ _ _).mp
    change e.hom ≫ e.inv ≫ powerMorphism m = _
    exact e.hom_inv_id_assoc _
  simpa only [hp] using (RootData.CharacterPairing.characterPairingComposition X
    (e.inv ≫ powerMorphism m) e.hom).2 R t

private def signedRootIndex (j : ℤ) : RootIndices 2 :=
  if j = 1 then ⟨(0, 1), by decide⟩ else ⟨(1, 0), by decide⟩

private theorem signedRootIndex_surjective (p : RootIndices 2) :
    ∃ j : ℤ, (j = 1 ∨ j = -1) ∧ p = signedRootIndex j := by
  rcases p with ⟨⟨i, l⟩, h⟩
  fin_cases i <;> fin_cases l
  · exact (h rfl).elim
  · exact ⟨1, Or.inl rfl, rfl⟩
  · exact ⟨-1, Or.inr rfl, rfl⟩
  · exact (h rfl).elim

private theorem signedRoot_character {T : DiagonalTorus s} {L : LatticeIdentification T}
    (W : RootIdentification T L) (j : ℤ) (hj : j = 1 ∨ j = -1) :
    (W.indices (signedRootIndex j)).val = (sourceMark T).inv ≫ powerMorphism (2 * j) := by
  let p := signedRootIndex j
  have hp : (W.indices p).val = matrixRootCharacter L p.val.1 p.val.2 := by
    change Additive.ofMul (W.indices p).val =
      Additive.ofMul (matrixRootCharacter L p.val.1 p.val.2)
    apply L.characters.injective
    change L.characters (Additive.ofMul (W.indices p).val) =
      L.characters (L.characters.symm (root 2 p.val.1 p.val.2))
    rw [W.character_eq, LinearEquiv.apply_symm_apply]
  apply RootData.CharacterPairing.characterValuesDetectCharacters T.split
  intro R x
  obtain ⟨t, rfl⟩ := marked_point_surjective (sourceMark T) R x
  rw [hp, matrixRootCharacter_value, marked_character_value]
  let d := determinantOneUnits (T.pointsIso.hom.app R (cocharacterPoint (sourceMark T).hom R t))
  have hd : d firstIndex = t ∧ d lastIndex = t⁻¹ := sourceMark_entries T R t
  rcases hj with rfl | rfl
  · change (↑(d firstIndex * (d lastIndex)⁻¹) : R) = ↑(t ^ ((2 : ℤ) * 1))
    rw [hd.1, hd.2, inv_inv, mul_one]
    change (↑(t * t) : R) = ↑(t ^ (2 : ℕ))
    rw [pow_two]
  · change (↑(d lastIndex * (d firstIndex)⁻¹) : R) = ↑(t ^ ((2 : ℤ) * -1))
    rw [hd.1, hd.2, show (2 : ℤ) * -1 = -(2 : ℤ) by decide, _root_.zpow_neg]
    change (↑(t⁻¹ * t⁻¹) : R) = ↑((t ^ (2 : ℕ))⁻¹)
    rw [pow_two, mul_inv]

private theorem signedRoot_coroot {T : DiagonalTorus s} {L : LatticeIdentification T}
    {W : RootIdentification T L} {B : UpperTriangularBorel T L W} (D : AttachedDatum B.pair)
    (j : ℤ) (hj : j = 1 ∨ j = -1) :
    IsAttachedCoroot T.subgroup (W.indices (signedRootIndex j))
      (powerMorphism j ≫ (sourceMark T).hom) := by
  letI := D.comm
  let α := W.indices (signedRootIndex j)
  let c := Additive.toMul (D.datum.rootDatum.coroot α)
  have htwo : pairing T.subgroup.group α.val c = 2 := by
    rw [← D.datum.pairing_eq, ← D.datum.root_eq]
    exact D.datum.rootDatum.root_coroot_two α
  obtain ⟨m, hm, _⟩ := (dual_generators (sourceMark T)).2.2 c
  rw [show α.val = _ from signedRoot_character W j hj, hm, marked_pairing] at htwo
  have h : m = j := by rcases hj with rfl | rfl <;> norm_num at htwo ⊢ <;> omega
  rw [h] at hm
  exact hm ▸ D.datum.attached α

private theorem projective_root_character (Q : ScalarQuotient g s a) (U : RatioTorus Q)
    (T : DiagonalTorus s) {p : T.subgroup.group ⟶ U.subgroup.group}
    (hi : Function.Injective (characterPullback p))
    (hpow : p ≫ (ratioMark Q U).inv = (sourceMark T).inv ≫ powerMorphism 2)
    (χ : Character U.subgroup.group) (j : ℤ)
    (hc : characterPullback p χ = (sourceMark T).inv ≫ powerMorphism (2 * j)) :
    χ = (ratioMark Q U).inv ≫ powerMorphism j := by
  apply hi
  change p ≫ χ = p ≫ (ratioMark Q U).inv ≫ powerMorphism j
  change p ≫ χ = _ at hc
  rw [hc, ← Category.assoc, hpow, Category.assoc, power_comp]

/-- The actual determinant-one and ratio coordinates give the two type A₁ lattices. -/
theorem rankOneLatticeComparison : RankOneLatticeComparison.{u} := by
  intro k _ G S M g s a Q U hf
  obtain ⟨T, L, W, B, D, _, _, _⟩ := RootData.SpecialLinearDatum.matrixPinnedDatum k 1 S s
  obtain ⟨p, hp, hfp, hpoint⟩ := rankOneTorusRestriction k G S M g s a Q U T
  let eS := sourceMark T
  let eP := ratioMark Q U
  have hpull : p ≫ eP.inv = eS.inv ≫ powerMorphism 2 := gm_ratio_maps Q U T hpoint
  have hpush : eS.hom ≫ p = powerMorphism 2 ≫ eP.hom := by
    apply (cancel_mono eP.inv).mp
    rw [Category.assoc, hpull, eS.hom_inv_id_assoc, Category.assoc, eP.hom_inv_id, Category.comp_id]
  obtain ⟨hinj, _, hroots, hcoroot⟩ :=
    Classification.CentralIsogenies.centralIsogenyComparison S Q.P B.reductive Q.reductive
      T.subgroup U.subgroup T.split B.maximal U.split U.maximal Q.map p hf hp.1 hp.2.2
  obtain ⟨hcomm, ⟨DP⟩⟩ :=
    RootData.AbstractPairing.abstractPairing Q.P Q.reductive U.subgroup U.split U.maximal
  letI := hcomm
  refine ⟨T, p, eS, eP, ⟨B.reductive, T.subgroup, T.split, B.maximal⟩,
    ⟨Q.reductive, U.subgroup, U.split, U.maximal⟩, B.maximal, hp, hfp,
    dual_generators eS, dual_generators eP, sourceMark_matrix T, ?_, hpull, hpush, ?_, ?_, ?_⟩
  · intro R t
    exact gm_forward_coordinate (X := Specs.Unipotent.closedSubgroupAlgebraicGroup U.subgroup)
      ((groupPointsFunctor k).mapIso U.coordinate ≪≫ a) R t
  · intro j hj
    let α := W.indices (signedRootIndex j)
    have hα := signedRoot_character W j hj
    have hc := signedRoot_coroot D j hj
    obtain ⟨χ, hχ, h⟩ := hroots.surjOn α.property
    let β : Root U.subgroup := ⟨χ, hχ⟩
    have hpullβ : characterPullback p χ = eS.inv ≫ powerMorphism (2 * j) := h.trans hα
    have hβ := projective_root_character Q U T hinj hpull χ j hpullβ
    have hroot : characterPullback p χ ∈ absoluteRoots T.subgroup := h.symm ▸ α.property
    have hα' : (⟨characterPullback p χ, hroot⟩ : Root T.subgroup) = α := Subtype.ext h
    have hDP := DP.attached β
    have hcP := (hcoroot χ hχ hroot).2 (powerMorphism j ≫ eS.hom)
      (Additive.toMul (DP.rootDatum.coroot β)) (hα'.symm ▸ hc) hDP
    have hcp : Additive.toMul (DP.rootDatum.coroot β) = powerMorphism (2 * j) ≫ eP.hom := by
      rw [← hcP, Category.assoc, hpush, ← Category.assoc, power_comp, mul_comm j 2]
    exact ⟨α, β, hα, hβ, hc, hcp ▸ hDP⟩
  · intro α
    obtain ⟨i, rfl⟩ := W.indices.surjective α
    obtain ⟨j, hj, rfl⟩ := signedRootIndex_surjective i
    exact ⟨j, hj, signedRoot_character W j hj⟩
  · intro β
    let α : Root T.subgroup := ⟨characterPullback p β.val, hroots.mapsTo β.property⟩
    obtain ⟨i, hi⟩ := W.indices.surjective α
    obtain ⟨j, hj, rfl⟩ := signedRootIndex_surjective i
    have hα : characterPullback p β.val = eS.inv ≫ powerMorphism (2 * j) :=
      (congrArg Subtype.val hi).symm.trans (signedRoot_character W j hj)
    exact ⟨j, hj, projective_root_character Q U T hinj hpull β.val j hα⟩

end Lattices
end Ratio
end
end LinearAlgebraicGroups.Classification.TypeAOneLattices
