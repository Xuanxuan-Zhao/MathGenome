import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizerAction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizerAction

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (GroupScheme ClosedSubgroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)
open Specs.ExceptionalResidueCentralizerAction

open private centralizes_iff mono_over from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private fibrePointsEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private forgetFibrePoint_natural from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralFibreRootCoordinates

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K]

private def moveTwist (galois : K ≃+* K) {R S : TestAlgebra K} (f : twist galois R ⟶ S) :
    R ⟶ twist galois.symm S := by
  let g := (CommAlgCat.homEquivCommRingCat (twist galois R) S) f
  refine (CommAlgCat.homEquivCommRingCat R (twist galois.symm S)).symm
    ⟨g.val, RingHom.ext fun x => ?_⟩
  change g.val.hom (algebraMap K R x) = algebraMap K S (galois x)
  have h := DFunLike.congr_fun g.property (galois x)
  change g.val.hom (algebraMap K R (galois.symm (galois x))) = algebraMap K S (galois x) at h
  simpa only [galois.symm_apply_apply] using h

private theorem forget_map (G : IntegralGroup.{u}) {R S : TestAlgebra K} (f : R ⟶ S)
    (p : GroupPoints ((fibre K).obj G) R) :
    forgetFibrePoint G S (mapPoints f p) =
      changeRingHom G (integralRingMap f.hom.toRingHom) (forgetFibrePoint G R p) :=
  forgetFibrePoint_natural G f p

private theorem scheme_ext_on_algebras {X Y : SchemeOver K} {f g : X ⟶ Y}
    (h : ∀ (T : TestAlgebra K) (r : Points X T), r ≫ f = r ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  let U := X.left.affineCover
  apply U.hom_ext
  intro i
  let V : SchemeOver K := Over.mk (U.f i ≫ X.hom)
  let m : V ⟶ X := Over.homMk (U.f i) rfl
  have hV : IsAffine V.left := inferInstanceAs (IsAffine (X.left.affineCover.X i))
  obtain ⟨T, ⟨chart⟩⟩ := essImage_algSpec.mpr hV
  have he := h T.unop (chart.hom ≫ m)
  have hm : m ≫ f = m ≫ g := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg (chart.inv ≫ ·) he
  exact congrArg (fun q => q.left) hm

private theorem centralizes_of_tests {G H : GroupScheme K} {X : SchemeOver K}
    (i : H ⟶ G) (f : X ⟶ G.X)
    (h : ∀ (R : TestAlgebra K) (a : Points X R) (b : GroupPoints H R),
      Commute (a ≫ f) (b ≫ i.hom.hom)) : Centralizes i f := by
  apply scheme_ext_on_algebras
  intro R v
  have hv := (h R (v ≫ snd H.X X) (v ≫ fst H.X X)).eq
  have he := mul_inv_eq_iff_eq_mul.mpr hv
  simpa only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using he

private def pointHom {G H : GroupScheme K} (f : G ⟶ H) (R : TestAlgebra K) :
    GroupPoints G R →* GroupPoints H R :=
  IsMonHom.monoidHom f.hom.hom ((testSpec K).obj (op R))

variable {D : BasedRootDatum.{u}} {M : IntegralMarking D}
  {d : ℕ} {y : D.Y} (C : MarkedCentralizer M K d y)

private theorem include_injective (R : TestAlgebra K) :
    Function.Injective (pointHom (inclusion C) R) := by
  have : Mono C.component.inclusion.hom.hom :=
    mono_over _ C.component.isClosedImmersion
  have : Mono C.centralizer.inclusion.hom.hom :=
    mono_over _ C.centralizer.isClosedImmersion
  intro p q h
  change p ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom =
    q ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom at h
  simp only [← Category.assoc] at h
  exact (cancel_mono C.component.inclusion.hom.hom).mp
    ((cancel_mono C.centralizer.inclusion.hom.hom).mp h)

private theorem extend_eq (R : TestAlgebra K)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) :
    extend R n = forgetFibrePoint M.group R (mapPoints (scalarHom R) n) := by
  rw [forget_map]
  rfl

private theorem extend_mul (R : TestAlgebra K)
    (n b : GroupPoints (fibreGroup M K) (baseAlgebra K)) :
    extend R (b * n) = extend R b * extend R n := by
  change changeRingHom M.group _ ((fibrePointsEquiv M.group (baseAlgebra K)) (b * n)) = _
  rw [map_mul, map_mul]
  rfl

private theorem extend_natural {R S : TestAlgebra K} (f : R ⟶ S)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) :
    changeRingHom M.group (integralRingMap f.hom.toRingHom) (extend R n) = extend S n := by
  rw [extend_eq R n, extend_eq S n, ← forget_map M.group f (mapPoints (scalarHom R) n)]
  congr 1
  have h : scalarHom R ≫ f = scalarHom S := by
    apply CommAlgCat.hom_ext
    ext
  simp only [mapPoints, ← Category.assoc, ← Functor.map_comp, ← op_comp, h]

private def integralAction (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) (R : TestAlgebra K) :
    IntegralPoints M.group (integralRing R) →* IntegralPoints M.group (integralRing R) :=
  (MulAut.conj (extend R n)).toMonoidHom.comp
    (IsMonHom.monoidHom δ.asIso.hom.hom.hom (integralSpec.obj (op (integralRing R))))

private theorem integralAction_natural (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    {R S : TestAlgebra K} (f : R ⟶ S) (z : IntegralPoints M.group (integralRing R)) :
    changeRingHom M.group (integralRingMap f.hom.toRingHom) (integralAction δ n R z) =
    integralAction δ n S (changeRingHom M.group (integralRingMap f.hom.toRingHom) z) := by
  let a := integralRingMap f.hom.toRingHom
  change changeRingHom M.group a (extend R n * deltaPoint δ z * (extend R n)⁻¹) =
    extend S n * deltaPoint δ (changeRingHom M.group a z) * (extend S n)⁻¹
  have h : changeRingHom M.group a (deltaPoint δ z) =
      deltaPoint δ (changeRingHom M.group a z) :=
    (Category.assoc (integralSpec.map a.op) z δ.asIso.hom.hom.hom).symm
  have he : changeRingHom M.group a (extend R n) = extend S n := extend_natural f n
  simp only [map_mul, map_inv, he, h]

private def ambient (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) (R : TestAlgebra K) :
    GroupPoints (fibreGroup M K) R →* GroupPoints (fibreGroup M K) (twist galois R) :=
  (fibrePointsEquiv M.group (twist galois R)).symm.toMonoidHom.comp
    ((integralAction δ n (twist galois R)).comp (fibrePointsEquiv M.group R).toMonoidHom)

private theorem ambient_forget (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) (R : TestAlgebra K)
    (p : GroupPoints (fibreGroup M K) R) :
    forgetFibrePoint M.group (twist galois R) (ambient galois δ n R p) =
      integralAction δ n (twist galois R) (forgetFibrePoint M.group R p) :=
  (fibrePointsEquiv M.group (twist galois R)).apply_symm_apply _

private theorem ambient_natural (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K)) {R S : TestAlgebra K} (f : R ⟶ S)
    (p : GroupPoints (fibreGroup M K) R) :
    mapPoints (twistHom galois f) (ambient galois δ n R p) =
      ambient galois δ n S (mapPoints f p) := by
  apply (fibrePointsEquiv M.group (twist galois S)).injective
  change forgetFibrePoint M.group _ _ = forgetFibrePoint M.group _ _
  rw [forget_map M.group (twistHom galois f) (ambient galois δ n R p),
    ambient_forget galois δ n R p, integralAction_natural,
    ambient_forget galois δ n S (mapPoints f p), forget_map M.group f p]
  rfl

private theorem full_corrector_fixes (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    (b : GroupPoints C.component.group (baseAlgebra K)) (hn : FixesMarkedImage C δ n)
    (R : TestAlgebra K) (r : GroupPoints C.mu R) :
    integralAction δ (pointHom (inclusion C) _ b * n) R
      (forgetFibrePoint M.group R (r ≫ C.image.hom.hom)) =
      forgetFibrePoint M.group R (r ≫ C.image.hom.hom) := by
  let bu := pointHom (inclusion C) (baseAlgebra K) b
  let z := forgetFibrePoint M.group R (r ≫ C.image.hom.hom)
  have hbu : Centralizes C.image bu :=
    (C.represents _ _).mpr ⟨b ≫ C.component.inclusion.hom.hom, Category.assoc _ _ _⟩
  have hcomm := (centralizes_iff C.image bu).mp hbu _
    ((testSpec K).map (scalarHom R).op) r
  have hc : Commute (extend R bu) z := by
    rw [extend_eq]
    exact hcomm.map (fibrePointsEquiv M.group R).toMonoidHom
  change extend R (bu * n) * deltaPoint δ z * (extend R (bu * n))⁻¹ = z
  rw [extend_mul]
  calc
    _ = extend R bu * (extend R n * deltaPoint δ z * (extend R n)⁻¹) *
        (extend R bu)⁻¹ := by group
    _ = extend R bu * z * (extend R bu)⁻¹ := by rw [hn R r]
    _ = z := mul_inv_eq_iff_eq_mul.mpr hc.eq

private theorem ambient_centralizes (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    (b : GroupPoints C.component.group (baseAlgebra K)) (hn : FixesMarkedImage C δ n)
    (R : TestAlgebra K) (p : GroupPoints (fibreGroup M K) R)
    (hp : Centralizes C.image p) :
    Centralizes C.image (ambient galois δ (pointHom (inclusion C) _ b * n) R p) := by
  let q := pointHom (inclusion C) (baseAlgebra K) b * n
  apply centralizes_of_tests
  intro S a r
  let ff := algSpec.fullyFaithful (R := CommRingCat.of K)
  let f := (ff.preimage a).unop
  have ha : (testSpec K).map f.op = a := ff.map_preimage a
  let S' := twist galois.symm S
  let t : rootsOfUnity d S := C.unitPoints.hom.app S r
  let e := (C.unitPoints.app S').groupIsoToMulEquiv
  let r' : GroupPoints C.mu S' := e.symm t
  have hr : forgetFibrePoint M.group S' (r' ≫ C.image.hom.hom) =
      forgetFibrePoint M.group S (r ≫ C.image.hom.hom) := by
    rw [C.image_cocharacter, C.image_cocharacter]
    have he : C.unitPoints.hom.app S' r' = t := e.apply_symm_apply t
    rw [he]
  have h := (centralizes_iff C.image p).mp hp _
    ((testSpec K).map (moveTwist galois f).op) r'
  have h' := h.map (fibrePointsEquiv M.group S').toMonoidHom
  apply (commute_map_iff (fibrePointsEquiv M.group S).injective).mp
  rw [← ha]
  change Commute (forgetFibrePoint M.group S (mapPoints f (ambient galois δ q R p)))
    (forgetFibrePoint M.group S (r ≫ C.image.hom.hom))
  rw [forget_map, ambient_forget, integralAction_natural]
  have h'' := h'.map (integralAction δ q S)
  change Commute
    (integralAction δ q S (forgetFibrePoint M.group S' (mapPoints (moveTwist galois f) p)))
    (integralAction δ q S (forgetFibrePoint M.group S' (r' ≫ C.image.hom.hom))) at h''
  rw [forget_map, hr, full_corrector_fixes C δ n b hn S r] at h''
  exact h''

private theorem component_connected : ConnectedSpace ↥(C.component.group.X.left) := by
  have := C.component_open
  have h : _root_.IsConnected (Set.range C.component.inclusion.hom.hom.left) := by
    rw [C.component_range]
    exact isConnected_connectedComponent
  let e := C.component.inclusion.hom.hom.left.isOpenEmbedding.isEmbedding.toHomeomorph
  exact e.connectedSpace_iff.mpr (Subtype.connectedSpace h)

private theorem pointHom_map {G H : GroupScheme K} (i : G ⟶ H)
    {R S : TestAlgebra K} (f : R ⟶ S) (p : GroupPoints G R) :
    pointHom i S (mapPoints f p) = mapPoints f (pointHom i R p) :=
  Category.assoc ((testSpec K).map f.op) p i.hom.hom

private theorem chart_factors (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    (b : GroupPoints C.component.group (baseAlgebra K)) (hn : FixesMarkedImage C δ n)
    {A : TestAlgebra K} (chart : (testSpec K).obj (op A) ≅ C.component.group.X) :
    ∃ p : GroupPoints C.component.group (twist galois A),
      pointHom (inclusion C) _ p =
        ambient galois δ (pointHom (inclusion C) _ b * n) A
          (pointHom (inclusion C) _ chart.hom) := by
  let q := pointHom (inclusion C) (baseAlgebra K) b * n
  let p : GroupPoints (fibreGroup M K) A := pointHom (inclusion C) A chart.hom
  have hp : Centralizes C.image p :=
    (C.represents _ _).mpr ⟨chart.hom ≫ C.component.inclusion.hom.hom, Category.assoc _ _ _⟩
  obtain ⟨c, hc⟩ := (C.represents _ _).mp (ambient_centralizes C galois δ n b hn A p hp)
  change ((testSpec K).obj (op (twist galois A))) ⟶ C.centralizer.group.X at c
  change c ≫ C.centralizer.inclusion.hom.hom = ambient galois δ q A p at hc
  let fSpec := algSpec.fullyFaithful (R := CommRingCat.of K)
  let e : A ⟶ baseAlgebra K :=
    (fSpec.preimage ((1 : GroupPoints C.component.group (baseAlgebra K)) ≫ chart.inv)).unop
  have he : (testSpec K).map e.op =
      (1 : GroupPoints C.component.group (baseAlgebra K)) ≫ chart.inv :=
    fSpec.map_preimage _
  have hp_one : mapPoints e p = 1 := by
    change (testSpec K).map e.op ≫ chart.hom ≫ (inclusion C).hom.hom = 1
    rw [he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, MonObj.one_comp]
  have hc_one : mapPoints (twistHom galois e) c =
      (1 : GroupPoints C.centralizer.group (twist galois (baseAlgebra K))) := by
    have : Mono C.centralizer.inclusion.hom.hom :=
      mono_over _ C.centralizer.isClosedImmersion
    apply (cancel_mono C.centralizer.inclusion.hom.hom).mp
    change ((testSpec K).map (twistHom galois e).op ≫ c) ≫
      C.centralizer.inclusion.hom.hom = 1 ≫ C.centralizer.inclusion.hom.hom
    rw [Category.assoc, hc, MonObj.one_comp]
    change mapPoints (twistHom galois e) (ambient galois δ q A p) = 1
    rw [ambient_natural, hp_one, map_one]
  have hr : η[C.centralizer.group.X].left (IsLocalRing.closedPoint K) ∈ Set.range c.left := by
    let x : ↥((testSpec K).obj (op (twist galois (baseAlgebra K)))).left :=
      IsLocalRing.closedPoint K
    refine ⟨((testSpec K).map (twistHom galois e).op).left x, ?_⟩
    calc
      _ = (mapPoints (twistHom galois e) c).left x := (Scheme.Hom.comp_apply _ _ x).symm
      _ = (1 : GroupPoints C.centralizer.group (twist galois (baseAlgebra K))).left x :=
        congrArg (fun z => z.left x) hc_one
      _ = _ := by
        rw [Hom.one_def]
        let T := (testSpec K).obj (op (twist galois (baseAlgebra K)))
        change (T.hom ≫ η[C.centralizer.group.X].left) x = _
        rw [Scheme.Hom.comp_apply]
        have h : T.hom x = IsLocalRing.closedPoint K :=
          Subsingleton.elim (α := ↥(Spec (CommRingCat.of K))) _ _
        exact congrArg (η[C.centralizer.group.X].left ·) h
  have hcA : ConnectedSpace ↥((testSpec K).obj (op (twist galois A))).left := by
    change ConnectedSpace ↥((testSpec K).obj (op A)).left
    let iso := (Over.forget (Spec (CommRingCat.of K))).mapIso chart
    exact iso.hom.homeomorph.connectedSpace_iff.mpr (component_connected C)
  have := hcA
  have hrange : Set.range c.left ⊆ Set.range C.component.inclusion.hom.hom.left := by
    rw [C.component_range]
    exact (isConnected_range c.left.continuous).isPreconnected.subset_connectedComponent hr
  have := C.component_open
  let l := IsOpenImmersion.lift C.component.inclusion.hom.hom.left c.left hrange
  have hl : l ≫ C.component.inclusion.hom.hom.left = c.left :=
    IsOpenImmersion.lift_fac _ _ _
  let a : (testSpec K).obj (op (twist galois A)) ⟶ C.component.group.X :=
    Over.homMk l (by
      rw [← Over.w C.component.inclusion.hom.hom, ← Category.assoc, hl, Over.w])
  have ha : a ≫ C.component.inclusion.hom.hom = c := Over.OverMorphism.ext hl
  exact ⟨a, by
    change a ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom = _
    rw [← Category.assoc, ha, hc]⟩

private theorem action_exists (galois : K ≃+* K) (δ : Aut M.group)
    (n : GroupPoints (fibreGroup M K) (baseAlgebra K))
    (b : GroupPoints C.component.group (baseAlgebra K)) (hn : FixesMarkedImage C δ n)
    (R : TestAlgebra K) (p : GroupPoints C.component.group R) :
    ∃ p' : GroupPoints C.component.group (twist galois R),
      pointHom (inclusion C) _ p' =
        ambient galois δ (pointHom (inclusion C) _ b * n) R (pointHom (inclusion C) _ p) := by
  obtain ⟨A, ⟨chart⟩⟩ := essImage_algSpec.mpr C.component_affine
  obtain ⟨a, ha⟩ := chart_factors C galois δ n b hn chart
  let ff := algSpec.fullyFaithful (R := CommRingCat.of K)
  let f : A.unop ⟶ R := (ff.preimage (p ≫ chart.inv)).unop
  have hf : (testSpec K).map f.op = p ≫ chart.inv := ff.map_preimage _
  have hchart : mapPoints f chart.hom = p := by
    change (testSpec K).map f.op ≫ chart.hom = p
    rw [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨mapPoints (twistHom galois f) a, ?_⟩
  rw [pointHom_map, ha, ambient_natural, ← pointHom_map (inclusion C) f chart.hom, hchart]

/-- The scaled operator acts naturally on all points of the given open identity component. -/
theorem connectedCentralizerAction : ConnectedCentralizerAction.{u} := by
  intro K _ D M d y C galois δ n b hn
  let q := pointHom (inclusion C) (baseAlgebra K) b * n
  let image (R : TestAlgebra K) := pointHom (inclusion C) R
  let liftPoint (R : TestAlgebra K) (p : GroupPoints C.component.group R) :=
    (action_exists C galois δ n b hn R p).choose
  have hLift (R : TestAlgebra K) (p : GroupPoints C.component.group R) :
      image (twist galois R) (liftPoint R p) = ambient galois δ q R (image R p) :=
    (action_exists C galois δ n b hn R p).choose_spec
  let action (R : TestAlgebra K) :
      GroupPoints C.component.group R →* GroupPoints C.component.group (twist galois R) :=
    { toFun := liftPoint R
      map_one' := by
        apply include_injective C (twist galois R)
        change image (twist galois R) (liftPoint R 1) = image (twist galois R) 1
        rw [hLift, map_one, map_one, map_one]
      map_mul' := fun p p' => by
        apply include_injective C (twist galois R)
        change image (twist galois R) (liftPoint R (p * p')) =
          image (twist galois R) (liftPoint R p * liftPoint R p')
        rw [hLift, map_mul, map_mul, map_mul, hLift, hLift] }
  refine ⟨action, ?_, ?_⟩
  · intro R p p'
    have h : PointFormula C galois δ n b R p p' ↔
        image (twist galois R) p' = ambient galois δ q R (image R p) := by
      rw [← (fibrePointsEquiv M.group (twist galois R)).injective.eq_iff]
      change _ ↔ forgetFibrePoint M.group (twist galois R) (image (twist galois R) p') =
        forgetFibrePoint M.group (twist galois R) (ambient galois δ q R (image R p))
      rw [ambient_forget]
      rfl
    rw [h, ← hLift, (include_injective C (twist galois R)).eq_iff]
    rfl
  · intro R S f p
    apply include_injective C (twist galois S)
    change pointHom (inclusion C) _ (mapPoints (twistHom galois f) (liftPoint R p)) =
      image (twist galois S) (liftPoint S (mapPoints f p))
    rw [pointHom_map]
    change mapPoints (twistHom galois f) (image (twist galois R) (liftPoint R p)) = _
    rw [hLift R p, hLift S (mapPoints f p), ambient_natural]
    change _ = ambient galois δ q S (pointHom (inclusion C) _ (mapPoints f p))
    rw [pointHom_map]

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalResidueCentralizerAction
