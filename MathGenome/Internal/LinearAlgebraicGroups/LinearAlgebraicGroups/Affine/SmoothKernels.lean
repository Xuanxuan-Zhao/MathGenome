import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SmoothKernels
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open Coalgebra Bialgebra WithConv _root_.Specs.AdvCommAlg.Differentials.Tangent

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem surjective_of_equiv_square {X Y X' Y' : Type*}
    (e : X ≃ X') (d : Y ≃ Y') {f : X' → Y'} {g : X → Y}
    (h : ∀ x, f (e x) = d (g x)) : Function.Surjective f ↔ Function.Surjective g := by
  constructor
  · intro hf y
    obtain ⟨x, hx⟩ := hf (d y)
    exact ⟨e.symm x, d.injective (by rw [← h, e.apply_symm_apply, hx])⟩
  · intro hg y
    obtain ⟨x, hx⟩ := hg (d.symm y)
    exact ⟨e x, by rw [h, hx, d.apply_symm_apply]⟩

open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

variable {k : Type u} [Field k]

/-- The two maps from `G × N` to `G` are the first projection and right multiplication. -/
private theorem kernelTorsorSquare {G H : Specs.GroupScheme k} {f : G ⟶ H}
    {N : Specs.ClosedSubgroup G} (h : Specs.IsSchemeKernel f N) :
    let x := fst G.X N.group.X
    let n := snd G.X N.group.X ≫ N.inclusion.hom.hom
    IsPullback x (x * n) f.hom.hom f.hom.hom := by
  dsimp only
  let x := fst G.X N.group.X
  let y := snd G.X N.group.X
  let i := N.inclusion.hom.hom
  let F := f.hom.hom
  have hi {T : SchemeOver k} (v : T ⟶ N.group.X) : (v ≫ i) ≫ F = 1 :=
    (schemeKernel_sections h (v ≫ i)).mp ⟨v, rfl⟩
  have hw : x ≫ F = (x * (y ≫ i)) ≫ F := by
    rw [MonObj.mul_comp, hi, mul_one]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_)
  · intro c
    have hd : (c.fst⁻¹ * c.snd) ≫ F = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, c.condition, inv_mul_cancel]
    let v := h.lift (c.fst⁻¹ * c.snd) (toUnit c.pt) hd
    exact CartesianMonoidalCategory.lift c.fst v
  · intro c
    exact lift_fst _ _
  · intro c
    rw [MonObj.comp_mul, lift_fst, ← Category.assoc, lift_snd, h.lift_fst, mul_inv_cancel_left]
  · intro c m hm₁ hm₂
    apply BinaryFan.IsLimit.hom_ext (tensorProductIsBinaryProduct G.X N.group.X)
    · change m ≫ x = CartesianMonoidalCategory.lift c.fst _ ≫ x
      rw [lift_fst]
      exact hm₁
    · change m ≫ y = CartesianMonoidalCategory.lift c.fst _ ≫ y
      rw [lift_snd]
      apply h.hom_ext
      · rw [h.lift_fst]
        have hh : c.fst * ((m ≫ y) ≫ i) = c.snd := by
          change m ≫ (x * (y ≫ i)) = c.snd at hm₂
          rwa [MonObj.comp_mul, hm₁, ← Category.assoc] at hm₂
        rw [← hh, inv_mul_cancel_left]
      · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _

private theorem smooth_map_iff_smooth_kernel {G H : Specs.GroupScheme k}
    {f : G ⟶ H} {N : Specs.ClosedSubgroup G} (h : Specs.IsSchemeKernel f N)
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left] [QuasiCompact f.hom.hom.left] :
    Smooth f.hom.hom.left ↔ Smooth N.group.X.hom := by
  constructor
  · intro hf
    have h' := (Over.forget (Spec (CommRingCat.of k))).map_isPullback h
    exact MorphismProperty.of_isPullback h' hf
  · intro hN
    let U := Over.forget (Spec (CommRingCat.of k))
    let x := fst G.X N.group.X
    let y := snd G.X N.group.X
    have hp : IsPullback x.left y.left G.X.hom N.group.X.hom :=
      U.map_isPullback (IsPullback.of_is_product'
        (tensorProductIsBinaryProduct G.X N.group.X) isTerminalTensorUnit)
    have hs : Smooth x.left := MorphismProperty.of_isPullback hp.flip hN
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (U.map_isPullback (kernelTorsorSquare h))
      ⟨⟨inferInstanceAs (Surjective f.hom.hom.left), inferInstanceAs (Flat f.hom.hom.left)⟩,
        inferInstanceAs (QuasiCompact f.hom.hom.left)⟩ hs

private abbrev hopfAlgHom {A B : HopfAlgebraCategory k} (a : A ⟶ B) : A →ₐ[k] B :=
  a.hom.toAlgHom

private theorem counit_hopfAlgHom {A B : HopfAlgebraCategory k} (a : A ⟶ B) (x : A) :
    counitAlgHom k B (hopfAlgHom a x) = counitAlgHom k A x :=
  CoalgHomClass.counit_comp_apply a.hom x

private def cotangentMap {A B : HopfAlgebraCategory k} (a : A ⟶ B) :
    PointCotangent (counitAlgHom k A) →ₗ[k] PointCotangent (counitAlgHom k B) :=
  Ideal.mapCotangent _ _ (hopfAlgHom a) fun x hx =>
    (counit_hopfAlgHom a x).trans hx

private def coordinateTangentMap {A B : HopfAlgebraCategory k} (a : A ⟶ B) :
    DualKernel (convolutionPoints B) → DualKernel (convolutionPoints A) :=
  fun x => (hopfKernelLifts A).symm ⟨(hopfKernelLifts B x).val.comp (hopfAlgHom a), by
    ext b
    exact (AlgHom.congr_fun (hopfKernelLifts B x).property (hopfAlgHom a b)).trans
      (counit_hopfAlgHom a b)⟩

private theorem coordinateTangentMap_iff {A B : HopfAlgebraCategory k} (a : A ⟶ B) :
    Function.Surjective (coordinateTangentMap a) ↔ Function.Injective (cotangentMap a) := by
  obtain ⟨eA, hA, _⟩ := hopfTangentComparison k A
  obtain ⟨eB, hB, _⟩ := hopfTangentComparison k B
  have h (L : PointTangent (counitAlgHom k B)) :
      coordinateTangentMap a (eB L) = eA ((cotangentMap a).dualMap L) := by
    apply eA.symm.injective
    rw [AddEquiv.symm_apply_apply]
    apply LinearMap.ext
    intro c
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ c
    rw [← hA, AddEquiv.apply_symm_apply]
    exact hB L ⟨hopfAlgHom a x, (counit_hopfAlgHom a x).trans x.property⟩
  exact (surjective_of_equiv_square eB.toEquiv eA.toEquiv h).trans
    LinearMap.dualMap_surjective_iff

private abbrev augmentation (A : HopfAlgebraCategory k) := RingHom.ker (counitAlgHom k A).toRingHom

private def augmentationPart (A : HopfAlgebraCategory k) (x : A) : augmentation A :=
  ⟨x - algebraMap k A (counitAlgHom k A x), by
    change counitAlgHom k A (x - algebraMap k A (counitAlgHom k A x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]⟩

private def augmentationClass (A : HopfAlgebraCategory k) (x : A) :
    PointCotangent (counitAlgHom k A) :=
  (augmentation A).toCotangent (augmentationPart A x)

private theorem augmentationPart_add (A : HopfAlgebraCategory k) (x y : A) :
    augmentationPart A (x + y) = augmentationPart A x + augmentationPart A y := by
  apply Subtype.ext
  change x + y - algebraMap k A (counitAlgHom k A (x + y)) = _
  rw [map_add, map_add]
  change _ = (x - _) + (y - _)
  ring

private theorem augmentationPart_mul (A : HopfAlgebraCategory k) (x y : A) :
    augmentationPart A (x * y) =
      counitAlgHom k A x • augmentationPart A y +
        counitAlgHom k A y • augmentationPart A x +
        augmentationPart A x * augmentationPart A y := by
  apply Subtype.ext
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def]
  change x * y - algebraMap k A (counitAlgHom k A (x * y)) =
    algebraMap k A (counitAlgHom k A x) * (y - algebraMap k A (counitAlgHom k A y)) +
    algebraMap k A (counitAlgHom k A y) * (x - algebraMap k A (counitAlgHom k A x)) +
      (x - algebraMap k A (counitAlgHom k A x)) * (y - algebraMap k A (counitAlgHom k A y))
  rw [map_mul, map_mul]
  ring

private theorem cotangentMap_augmentationClass {A B : HopfAlgebraCategory k} (a : A ⟶ B) (x : A) :
    cotangentMap a (augmentationClass A x) = augmentationClass B (hopfAlgHom a x) := by
  rw [augmentationClass, cotangentMap, Ideal.mapCotangent_toCotangent, augmentationClass]
  congr 1
  apply Subtype.ext
  change hopfAlgHom a (x - algebraMap k A (counitAlgHom k A x)) =
    hopfAlgHom a x - algebraMap k B (counitAlgHom k B (hopfAlgHom a x))
  rw [map_sub, AlgHom.commutes, counit_hopfAlgHom a]

private theorem squareZero_mul {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    {x y : R} (hx : x ∈ I) (hy : y ∈ I) : x * y = 0 := by
  have hc : x * y ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  simpa only [hI, Ideal.mem_bot] using hc

private def identityLift {C : Type u} [CommRing C] [Algebra k C] (A : HopfAlgebraCategory k)
    (I : Ideal C) (hI : I ^ 2 = ⊥)
    (L : PointCotangent (counitAlgHom k A) →ₗ[k] I) : A →ₐ[k] C where
  toFun x := algebraMap k C (counitAlgHom k A x) + (L (augmentationClass A x) : C)
  map_zero' := by
    have h : augmentationPart A 0 = 0 := Subtype.ext (by simp [augmentationPart])
    simp [augmentationClass, h]
  map_one' := by
    have h : augmentationPart A 1 = 0 := Subtype.ext (by simp [augmentationPart])
    simp [augmentationClass, h]
  map_add' x y := by
    simp only [augmentationClass, augmentationPart_add, map_add, Submodule.coe_add]
    ring
  map_mul' x y := by
    have H : (augmentation A).toCotangent (augmentationPart A x * augmentationPart A y) = 0 := by
      rw [Ideal.toCotangent_eq_zero, pow_two]
      exact Ideal.mul_mem_mul (augmentationPart A x).property (augmentationPart A y).property
    have hd : L (augmentationClass A (x * y)) =
        counitAlgHom k A x • L (augmentationClass A y) +
          counitAlgHom k A y • L (augmentationClass A x) := by
      have H' : ((augmentation A).toCotangent.restrictScalars k)
          (augmentationPart A x * augmentationPart A y) = 0 := H
      simp only [augmentationClass, augmentationPart_mul, map_add,
        ← LinearMap.restrictScalars_apply k (augmentation A).toCotangent,
        map_smul, H', add_zero]
    rw [hd, map_mul, map_mul]
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Algebra.smul_def]
    have hz : (L (augmentationClass A x) : C) * (L (augmentationClass A y) : C) = 0 :=
      squareZero_mul I hI (L _).property (L _).property
    linear_combination -hz
  commutes' r := by
    have h : augmentationPart A (algebraMap k A r) = 0 := Subtype.ext (by simp [augmentationPart])
    simp [augmentationClass, h]

/-- A point reducing to the counit is determined by a linear map from the identity cotangent
space to the square-zero ideal. -/
private theorem identityLift_exists {C : Type u} [CommRing C] [Algebra k C] (A : HopfAlgebraCategory k)
    (I : Ideal C) (hI : I ^ 2 = ⊥) (g : A →ₐ[k] C)
    (hg : (Ideal.Quotient.mkₐ k I).comp g = (Algebra.ofId k (C ⧸ I)).comp (counitAlgHom k A)) :
    ∃ L, identityLift A I hI L = g := by
  let L₀ : augmentation A →ₗ[k] I :=
    g.toLinearMap.restrict (p := (augmentation A).restrictScalars k) (q := I.restrictScalars k)
      (by
        intro x hx
        have h := AlgHom.congr_fun hg x
        change Ideal.Quotient.mk I (g x) = algebraMap k (C ⧸ I) (counitAlgHom k A x) at h
        rw [show counitAlgHom k A x = 0 from hx, map_zero] at h
        exact Ideal.Quotient.eq_zero_iff_mem.mp h)
  let L := Ideal.Cotangent.lift L₀ (by
    intro x y
    apply Subtype.ext
    change g ((x : A) * (y : A)) = 0
    rw [map_mul]
    exact squareZero_mul I hI (L₀ x).property (L₀ y).property)
  refine ⟨L, AlgHom.ext fun x => ?_⟩
  change algebraMap k C (counitAlgHom k A x) + (L (augmentationClass A x) : C) = g x
  rw [augmentationClass, Ideal.Cotangent.lift_toCotangent]
  change algebraMap k C (counitAlgHom k A x) +
    g (x - algebraMap k A (counitAlgHom k A x)) = g x
  rw [map_sub, AlgHom.commutes]
  ring

private theorem identityLift_reduces {C : Type u} [CommRing C] [Algebra k C]
    (A : HopfAlgebraCategory k) (I : Ideal C) (hI : I ^ 2 = ⊥)
    (L : PointCotangent (counitAlgHom k A) →ₗ[k] I) :
    (Ideal.Quotient.mkₐ k I).comp (identityLift A I hI L) =
      (Algebra.ofId k (C ⧸ I)).comp (counitAlgHom k A) := by
  ext x
  change Ideal.Quotient.mk I (algebraMap k C (counitAlgHom k A x) +
    (L (augmentationClass A x) : C)) = algebraMap k (C ⧸ I) (counitAlgHom k A x)
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr (L _).property, add_zero]
  rfl

private def convolutionPrecomp {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (R : TestAlgebra k) : (convolutionPoints B).obj R →* (convolutionPoints A).obj R where
  toFun v := toConv (v.ofConv.comp (hopfAlgHom a))
  map_one' := by
    apply WithConv.ofConv_injective
    ext x
    change algebraMap k R (counitAlgHom k B (hopfAlgHom a x)) =
      algebraMap k R (counitAlgHom k A x)
    rw [counit_hopfAlgHom]
  map_mul' v w := WithConv.ofConv_injective (AlgHom.convMul_comp_bialgHom_distrib v w a.hom)

/-- Lift first over the field and then correct the lift by an infinitesimal point at
the identity. The correction is possible for every square-zero ideal since the
injective cotangent map splits over the field. -/
private theorem formallySmooth_of_cotangentMap_injective {A B : HopfAlgebraCategory k}
    (a : A ⟶ B) [Algebra.FormallySmooth k B] (ha : Function.Injective (cotangentMap a)) :
    (hopfAlgHom a).toRingHom.FormallySmooth := by
  letI : Algebra A B := (hopfAlgHom a).toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algHom (hopfAlgHom a)
  change Algebra.FormallySmooth A B
  obtain ⟨s, hs⟩ := (cotangentMap a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ha)
  apply Algebra.FormallySmooth.of_comp_surjective
  intro C _ _ I hI g
  letI : Algebra k C := ((algebraMap A C).comp (algebraMap k A)).toAlgebra
  letI : IsScalarTower k A C := IsScalarTower.of_algebraMap_eq' rfl
  let r : CommAlgCat.of k C ⟶ CommAlgCat.of k (C ⧸ I) :=
    CommAlgCat.ofHom (Ideal.Quotient.mkₐ k I)
  let rA := ((convolutionPoints A).map r).hom
  let rB := ((convolutionPoints B).map r).hom
  let F := convolutionPrecomp a (CommAlgCat.of k C)
  let v : (convolutionPoints A).obj (CommAlgCat.of k C) :=
    toConv (IsScalarTower.toAlgHom k A C)
  obtain ⟨u, hu⟩ := Algebra.FormallySmooth.comp_surjective k B I hI (g.restrictScalars k)
  let U : (convolutionPoints B).obj (CommAlgCat.of k C) := toConv u
  let d := (F U)⁻¹ * v
  have ht : rA (F U) = rA v := by
    apply WithConv.ofConv_injective
    change (Ideal.Quotient.mkₐ k I).comp (u.comp (hopfAlgHom a)) = _
    rw [← AlgHom.comp_assoc, hu]
    ext x
    exact g.commutes x
  have hd : rA d = 1 := by
    rw [map_mul, map_inv, ht, inv_mul_cancel]
  obtain ⟨L, hL⟩ := identityLift_exists A I hI d.ofConv (congrArg WithConv.ofConv hd)
  let w := identityLift B I hI (L.comp s)
  let W : (convolutionPoints B).obj (CommAlgCat.of k C) := toConv w
  have hw : F W = d := by
    apply WithConv.ofConv_injective
    change w.comp (hopfAlgHom a) = d.ofConv
    rw [← hL]
    apply AlgHom.ext
    intro x
    change algebraMap k C (counitAlgHom k B (hopfAlgHom a x)) +
      ((L.comp s) (augmentationClass B (hopfAlgHom a x)) : C) = _
    rw [counit_hopfAlgHom, ← cotangentMap_augmentationClass, LinearMap.comp_apply,
      ← LinearMap.comp_apply s (cotangentMap a), hs, LinearMap.id_apply]
    rfl
  have hh : F (U * W) = v := by
    rw [map_mul, hw, mul_inv_cancel_left]
  have hz : rB W = 1 := WithConv.ofConv_injective (identityLift_reduces B I hI _)
  refine ⟨{ (U * W).ofConv with commutes' := fun x => ?_ }, ?_⟩
  · exact AlgHom.congr_fun (congrArg WithConv.ofConv hh) x
  · have he := map_mul rB U W
    rw [hz, mul_one] at he
    exact AlgHom.ext fun x => (AlgHom.congr_fun (congrArg WithConv.ofConv he) x).trans
      (AlgHom.congr_fun hu x)

private theorem coordinateTangentMap_surjective_of_formallySmooth {A B : HopfAlgebraCategory k}
    (a : A ⟶ B) (h : (hopfAlgHom a).toRingHom.FormallySmooth) :
    Function.Surjective (coordinateTangentMap a) := by
  letI : Algebra A B := (hopfAlgHom a).toRingHom.toAlgebra
  letI : Algebra.FormallySmooth A B := h
  letI : IsScalarTower k A B := IsScalarTower.of_algHom (hopfAlgHom a)
  intro y
  let v := (hopfKernelLifts A y).val
  letI : Algebra A (DualNumber k) := v.toAlgebra
  letI : Algebra A k := (counitAlgHom k A).toAlgebra
  let r : DualNumber k →ₐ[A] k :=
    { TrivSqZeroExt.fstHom k k k with
      commutes' := AlgHom.congr_fun (hopfKernelLifts A y).property }
  let g : B →ₐ[A] k :=
    { counitAlgHom k B with commutes' := counit_hopfAlgHom a }
  have hsur : Function.Surjective r := TrivSqZeroExt.fst_surjective
  have hn : IsNilpotent (RingHom.ker r.toRingHom) := by
    change IsNilpotent (TrivSqZeroExt.kerIdeal k k)
    exact ⟨2, TrivSqZeroExt.kerIdeal_sq k k⟩
  let w := Algebra.FormallySmooth.liftOfSurjective g r hsur hn
  have hw := Algebra.FormallySmooth.comp_liftOfSurjective g r hsur hn
  let w' : B →ₐ[k] DualNumber k :=
    { w.toRingHom with
      commutes' := fun r => by
        change w (algebraMap k B r) = algebraMap k (DualNumber k) r
        rw [← (hopfAlgHom a).commutes r]
        exact (w.commutes (algebraMap k A r)).trans (v.commutes r) }
  let x : PointLifts k B k (counitAlgHom k B) :=
    ⟨w', AlgHom.ext fun b => AlgHom.congr_fun hw b⟩
  refine ⟨(hopfKernelLifts B).symm x, ?_⟩
  apply (hopfKernelLifts A).injective
  apply Subtype.ext
  rw [coordinateTangentMap, Equiv.apply_symm_apply]
  change ((hopfKernelLifts B ((hopfKernelLifts B).symm x)).val).comp (hopfAlgHom a) = v
  rw [Equiv.apply_symm_apply]
  exact AlgHom.ext w.commutes

open private dualKernelIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.IdentityTangent

private theorem tangentOfSpec_natural {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (x : DualKernel (convolutionPoints B)) :
    mapPointKernel (specGroupMap a) (dualKernelIso (hopfSpecPointIso B) x) =
      dualKernelIso (hopfSpecPointIso A) (coordinateTangentMap a x) := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom x.toMul.val.ofConv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (hopfAlgHom a).toRingHom) = _
  exact (Spec.map_comp (CommRingCat.ofHom (hopfAlgHom a).toRingHom)
    (CommRingCat.ofHom x.toMul.val.ofConv.toRingHom)).symm

private theorem tangentOfSpec_surjective_iff {A B : HopfAlgebraCategory k} (a : A ⟶ B) :
    Function.Surjective (mapPointKernel (specGroupMap a)) ↔
      Function.Surjective (coordinateTangentMap a) := by
  exact surjective_of_equiv_square (dualKernelIso (hopfSpecPointIso B)).toEquiv
    (dualKernelIso (hopfSpecPointIso A)).toEquiv (tangentOfSpec_natural a)

private theorem tangent_comp {G H L : Specs.GroupScheme k} (f : G ⟶ H) (g : H ⟶ L)
    (x : Lie k G) : mapPointKernel (f ≫ g) x = mapPointKernel g (mapPointKernel f x) := by
  apply Subtype.ext
  change (((groupPointsFunctor k).map (f ≫ g)).app _).hom x.toMul.val = _
  rw [Functor.map_comp]
  rfl

private theorem tangent_id (G : Specs.GroupScheme k) (x : Lie k G) :
    mapPointKernel (𝟙 G) x = x := by
  apply Subtype.ext
  change x.toMul.val ≫ 𝟙 G.X = x.toMul.val
  exact Category.comp_id _

private def tangentIso {G H : Specs.GroupScheme k} (e : G ≅ H) : Lie k G ≃ Lie k H where
  toFun := mapPointKernel e.hom
  invFun := mapPointKernel e.inv
  left_inv x := by rw [← tangent_comp, e.hom_inv_id, tangent_id]
  right_inv x := by rw [← tangent_comp, e.inv_hom_id, tangent_id]

private theorem smooth_iff_tangent_surjective_of_spec {A B : HopfAlgebraCategory k}
    (a : A ⟶ B) [IsNoetherianRing A] [Algebra.FiniteType k B]
    [Algebra.FormallySmooth k B] :
    Smooth (specGroupMap a).hom.hom.left ↔ Function.Surjective (mapPointKernel (specGroupMap a)) := by
  rw [tangentOfSpec_surjective_iff]
  change Smooth (Spec.map (CommRingCat.ofHom (hopfAlgHom a).toRingHom)) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  constructor
  · intro h
    exact coordinateTangentMap_surjective_of_formallySmooth a h.formallySmooth
  · intro h
    refine (RingHom.smooth_def).mpr ⟨formallySmooth_of_cotangentMap_injective a
      ((coordinateTangentMap_iff a).mp h), ?_⟩
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k A)
    change ((hopfAlgHom a).toRingHom.comp (algebraMap k A)).FiniteType
    rw [show (hopfAlgHom a).toRingHom.comp (algebraMap k A) = algebraMap k B from
      RingHom.ext (hopfAlgHom a).commutes]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem smoothKernelIffLieSurjective : Specs.SmoothKernelIffLieSurjective.{u} := by
  intro k _ G H f N hN hG _ hFlat hSurj
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine H.val.X.left := H.property.1
  letI : Flat f.hom.hom.left := hFlat
  letI : Surjective f.hom.hom.left := hSurj
  rw [← smooth_map_iff_smooth_kernel hN]
  let G' : AffineGroupCategory k := ⟨G.val, G.property.1⟩
  let H' : AffineGroupCategory k := ⟨H.val, H.property.1⟩
  let B := coordinateHopf G'
  let A := coordinateHopf H'
  let eG : specGroup B ≅ G.val := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso G')
  let eH : specGroup A ≅ H.val := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso H')
  let f' : specGroup B ⟶ specGroup A := eG.hom ≫ f ≫ eH.inv
  let a : A ⟶ B := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage f').unop
  have ha : specGroupMap a = f' := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f'
  have hcomm : eG.hom ≫ f = specGroupMap a ≫ eH.hom := by
    rw [ha]
    simp [f']
  let U := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hscheme : U.map eG.hom ≫ U.map f = U.map (specGroupMap a) ≫ U.map eH.hom := by
    simpa only [Functor.map_comp] using congrArg U.map hcomm
  have hS : Smooth f.hom.hom.left ↔ Smooth (specGroupMap a).hom.hom.left := by
    change Smooth (U.map f) ↔ Smooth (U.map (specGroupMap a))
    let P : MorphismProperty Scheme.{u} := @Smooth
    change P (U.map f) ↔ P (U.map (specGroupMap a))
    rw [← P.cancel_left_of_respectsIso (U.map eG.hom), hscheme,
      P.cancel_right_of_respectsIso]
  have hT : Function.Surjective (mapPointKernel f) ↔
      Function.Surjective (mapPointKernel (specGroupMap a)) := by
    apply surjective_of_equiv_square (tangentIso eG) (tangentIso eH)
    intro x
    change mapPointKernel f (mapPointKernel eG.hom x) =
      mapPointKernel eH.hom (mapPointKernel (specGroupMap a) x)
    rw [← tangent_comp, ← tangent_comp, hcomm]
  have finiteCoordinates {P : Specs.GroupScheme k} {D : HopfAlgebraCategory k}
      (e : specGroup D ≅ P) [LocallyOfFiniteType P.X.hom] : Algebra.FiniteType k D := by
    apply (hopfSpec_locallyOfFiniteType_iff k D).mp
    rw [← e.hom.hom.hom.w]
    exact inferInstanceAs (LocallyOfFiniteType (U.map e.hom ≫ P.X.hom))
  letI : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  letI : LocallyOfFiniteType H.val.X.hom := H.property.2.1
  letI : Algebra.FiniteType k B := finiteCoordinates eG
  letI : Algebra.FiniteType k A := finiteCoordinates eH
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hsG : Smooth (specGroup B).X.hom := by
    rw [← eG.hom.hom.hom.w]
    exact inferInstanceAs (Smooth (U.map eG.hom ≫ G.val.X.hom))
  have hAlg : (algebraMap k B).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsG
  letI : Algebra.FormallySmooth k B := ((RingHom.smooth_algebraMap).mp hAlg).formallySmooth
  rw [hS, hT]
  exact smooth_iff_tangent_surjective_of_spec a

section Frobenius

open Specs.RelativeFrobenius Polynomial
open private liftSemilinear liftSemilinear_apply extAlong extensionInclusion
  augmentation_additive kernelIdeal_of_augmentation presentsSchemeKernel alphaCoordinate_pow
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

private theorem scalarTensor_algebraMap {R S : Type u} [Field R] [Field S]
    (σ : R →+* S) (A : HopfAlgebraCategory R) (c : R) :
    scalarTensor σ A (σ c) 1 = scalarTensor σ A 1 (algebraMap R A c) := by
  letI : Algebra R S := σ.toAlgebra
  change (σ c) ⊗ₜ[R] (1 : A) = (1 : S) ⊗ₜ[R] algebraMap R A c
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
  change (σ c) ⊗ₜ[R] (1 : A) = (σ c * 1) ⊗ₜ[R] (1 : A)
  rw [mul_one]

/-- Base change of a polynomial algebra along Frobenius keeps the polynomial generator. -/
private def polynomialTwistEquiv {A : HopfAlgebraCategory k} (e : A ≃ₐ[k] Polynomial k) :
    twistCoordinates k p A ≃ₐ[k] Polynomial k := by
  let σ := frobenius k p
  let g : A →+* Polynomial k := (Polynomial.mapRingHom σ).comp e.toRingEquiv.toRingHom
  let h : ∀ r, g (algebraMap k A r) = algebraMap k (Polynomial k) (σ r) := by
    intro r
    change (e (algebraMap k A r)).map σ = _
    rw [AlgEquiv.commutes]
    exact Polynomial.map_C _
  let φ := liftSemilinear σ A (Polynomial k) g h
  let ψ : Polynomial k →ₐ[k] twistCoordinates k p A :=
    Polynomial.aeval (scalarTensor σ A 1 (e.symm Polynomial.X))
  have hφ : φ (scalarTensor σ A 1 (e.symm Polynomial.X)) = Polynomial.X := by
    rw [liftSemilinear_apply, one_smul]
    change (e (e.symm Polynomial.X)).map σ = _
    rw [AlgEquiv.apply_symm_apply, Polynomial.map_X]
  refine AlgEquiv.ofAlgHom φ ψ (Polynomial.algHom_ext ?_) (extAlong σ A ?_)
  · rw [AlgHom.comp_apply, Polynomial.aeval_X, hφ]
    rfl
  · intro b
    obtain ⟨b, rfl⟩ := e.symm.surjective b
    let j := extensionInclusion σ A
    change ψ (φ (j (e.symm b))) = j (e.symm b)
    have hmaps : ψ.toRingHom.comp ((Polynomial.mapRingHom σ)) =
        j.comp e.symm.toRingEquiv.toRingHom := by
      apply Polynomial.ringHom_ext
      · intro c
        change ψ ((Polynomial.C c).map σ) = j (e.symm (Polynomial.C c))
        rw [Polynomial.map_C]
        change ψ (algebraMap k (Polynomial k) (σ c)) =
          j (e.symm (algebraMap k (Polynomial k) c))
        rw [AlgHom.commutes, AlgEquiv.commutes]
        exact scalarTensor_algebraMap σ A c
      · change ψ ((Polynomial.X : Polynomial k).map σ) = _
        rw [Polynomial.map_X, Polynomial.aeval_X]
        rfl
    change ψ (φ (scalarTensor σ A 1 (e.symm b))) = _
    rw [liftSemilinear_apply, one_smul]
    change ψ ((e (e.symm b)).map σ) = _
    rw [AlgEquiv.apply_symm_apply]
    exact congrArg (fun h : Polynomial k →+* twistCoordinates k p A => h b) hmaps

private theorem polynomialTwistEquiv_generator {A : HopfAlgebraCategory k}
    (e : A ≃ₐ[k] Polynomial k) :
    (polynomialTwistEquiv p e).symm Polynomial.X =
      scalarTensor (frobenius k p) A 1 (e.symm Polynomial.X) := by
  change Polynomial.aeval (scalarTensor (frobenius k p) A 1 (e.symm Polynomial.X))
    Polynomial.X = _
  exact Polynomial.aeval_X _

private theorem polynomialFrobenius_formula {A : HopfAlgebraCategory k} (e : A ≃ₐ[k] Polynomial k)
    (a : twistCoordinates k p A ⟶ A) (ha : PullbackFormula k p A a) :
    e.toAlgHom.comp ((hopfAlgHom a).comp (polynomialTwistEquiv p e).symm.toAlgHom) =
      Polynomial.expand k p := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, polynomialTwistEquiv_generator,
    Polynomial.expand_X]
  change e (a.hom (scalarTensor (frobenius k p) A 1 (e.symm Polynomial.X))) = _
  rw [ha, one_smul, map_pow, AlgEquiv.apply_symm_apply]

omit [Fact p.Prime] [CharP k p] in
private theorem polynomialFrobenius_coeff (hp : 0 < p) (q : Polynomial k)
    (n : ℕ) (i j : Fin p) :
    ((Polynomial.expand k p q) * Polynomial.X ^ (j : ℕ)).coeff (n * p + (i : ℕ)) =
      if i = j then q.coeff n else 0 := by
  split_ifs with h
  · subst j
    rw [Polynomial.coeff_mul_X_pow, Polynomial.coeff_expand_mul hp]
  · rw [Polynomial.coeff_mul_X_pow']
    split_ifs with hle
    · rw [Polynomial.coeff_expand hp, ite_eq_right]
      intro hd
      obtain ⟨d, hd⟩ := hd
      have hsum : n * p + (i : ℕ) = p * d + (j : ℕ) := by omega
      have hmod := congrArg (· % p) hsum
      simp only [Nat.mul_add_mod_self_left, Nat.mul_add_mod_self_right,
        Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
      exact h (Fin.ext hmod)
    · rfl

private def polynomialFrobenius_basis {A : HopfAlgebraCategory k} (e : A ≃ₐ[k] Polynomial k)
    (a : twistCoordinates k p A ⟶ A) (ha : PullbackFormula k p A a) :
    letI : Algebra (twistCoordinates k p A) A := (hopfAlgHom a).toRingHom.toAlgebra
    Module.Basis (Fin p) (twistCoordinates k p A) A := by
  let T := twistCoordinates k p A
  letI : Algebra T A := (hopfAlgHom a).toRingHom.toAlgebra
  let θ := polynomialTwistEquiv p e
  let v : Fin p → A := fun i => e.symm Polynomial.X ^ (i : ℕ)
  have ha' (q : T) : e (hopfAlgHom a q) = Polynomial.expand k p (θ q) := by
    have h := AlgHom.congr_fun (polynomialFrobenius_formula p e a ha) (θ q)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, θ, AlgEquiv.symm_apply_apply] using h
  have hsmul (q : T) (i : Fin p) : e (q • v i) =
      Polynomial.expand k p (θ q) * Polynomial.X ^ (i : ℕ) := by
    rw [Algebra.smul_def, map_mul]
    change e (hopfAlgHom a q) * e (e.symm Polynomial.X ^ (i : ℕ)) = _
    rw [ha', map_pow, AlgEquiv.apply_symm_apply]
  refine Module.Basis.mk (v := v) ?_ ?_
  · apply Fintype.linearIndependent_iff.mpr
    intro g hg i
    apply θ.injective
    apply Polynomial.ext
    intro n
    have hc := congrArg (fun x => (e x).coeff (n * p + (i : ℕ))) hg
    simp only [map_sum, hsmul, Polynomial.finsetSum_coeff,
      polynomialFrobenius_coeff p (Fact.out : p.Prime).pos, map_zero, Polynomial.coeff_zero] at hc ⊢
    simpa [eq_comm] using hc
  · let S := Submodule.span T (Set.range v)
    suffices ∀ q : Polynomial k, e.symm q ∈ S by
      intro x _
      simpa only [AlgEquiv.symm_apply_apply] using this (e x)
    intro q
    induction q using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
    | monomial n c =>
      let i : Fin p := ⟨n % p, Nat.mod_lt _ (Fact.out : p.Prime).pos⟩
      let b := θ.symm (Polynomial.monomial (n / p) c)
      have h : e.symm (Polynomial.monomial n c) = b • v i := by
        apply e.injective
        rw [AlgEquiv.apply_symm_apply, hsmul, AlgEquiv.apply_symm_apply, Polynomial.expand_monomial]
        simp only [← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add]
        have hn : n / p * p + (i : ℕ) = n := by
          change n / p * p + n % p = n
          rw [Nat.mul_comm, Nat.add_comm, Nat.mod_add_div]
        rw [hn]
      rw [h]
      exact S.smul_mem b (Submodule.subset_span ⟨i, rfl⟩)

private theorem dualNumber_pow_frobenius (z : DualNumber k) :
    z ^ p = TrivSqZeroExt.inl (z.fst ^ p) := by
  letI : CharP (DualNumber k) p :=
    CharP.of_ringHom_of_ne_zero (algebraMap k (DualNumber k)) p (Fact.out : p.Prime).ne_zero
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Fact.out : p.Prime).two_le
  have hz : (TrivSqZeroExt.inr z.snd : DualNumber k) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  calc
    z ^ (2 + n) = (TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd) ^ (2 + n) :=
      congrArg (· ^ (2 + n)) (by ext <;> simp)
    _ = TrivSqZeroExt.inl (z.fst ^ (2 + n)) := by
      rw [add_pow_char, pow_add (TrivSqZeroExt.inr _), hz, zero_mul, add_zero,
        TrivSqZeroExt.inl_pow]

private theorem frobenius_coordinateTangent_zero {A : HopfAlgebraCategory k}
    (a : twistCoordinates k p A ⟶ A) (ha : PullbackFormula k p A a)
    (x : DualKernel (convolutionPoints A)) : coordinateTangentMap a x = 0 := by
  apply (hopfKernelLifts (twistCoordinates k p A)).injective
  apply Subtype.ext
  change (hopfKernelLifts A x).val.comp (hopfAlgHom a) =
    (TrivSqZeroExt.inlAlgHom k k k).comp (counitAlgHom k (twistCoordinates k p A))
  apply extAlong (frobenius k p) A
  intro b
  have hx := AlgHom.congr_fun (hopfKernelLifts A x).property b
  change ((hopfKernelLifts A x).val b).fst = counitAlgHom k A b at hx
  change (hopfKernelLifts A x).val (a.hom (scalarTensor (frobenius k p) A 1 b)) =
    TrivSqZeroExt.inl (counitAlgHom k (twistCoordinates k p A) (scalarTensor (frobenius k p) A 1 b))
  rw [← counit_hopfAlgHom a]
  change (hopfKernelLifts A x).val (a.hom (scalarTensor (frobenius k p) A 1 b)) =
    TrivSqZeroExt.inl (counitAlgHom k A (a.hom (scalarTensor (frobenius k p) A 1 b)))
  rw [ha, one_smul, map_pow, map_pow, dualNumber_pow_frobenius p, hx]

omit [CharP k p] in
private theorem alphaCoordinates_not_reduced : ¬ _root_.IsReduced (AlphaCoordinates k p) := by
  intro h
  have hz : alphaCoordinate k p = 0 :=
    IsNilpotent.eq_zero ⟨p, alphaCoordinate_pow p⟩
  have hm : (Polynomial.X : Polynomial k) ∈ alphaIdeal k p :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hm
  have h := congrArg (fun q : Polynomial k => q.coeff 1) hq
  rw [Polynomial.coeff_X_one, mul_comm, Polynomial.coeff_mul_X_pow',
    ite_eq_right (by have := (Fact.out : p.Prime).two_le; omega)] at h
  exact one_ne_zero h

open private isReduced_of_smooth_over_field
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

theorem additiveFrobeniusBoundary : Specs.AdditiveFrobeniusBoundary.{u} := by
  intro k _ p _ _ A e he a ha
  unfold Specs.AdditiveFrobeniusBoundaryAt
  dsimp only
  let T := twistCoordinates k p A
  letI : Algebra T A := (hopfAlgHom a).toRingHom.toAlgebra
  let F := specGroupMap a
  let b := polynomialFrobenius_basis p e a ha
  letI : Module.Free T A := Module.Free.of_basis b
  letI : Nontrivial A := e.symm.injective.nontrivial
  letI : Module.FaithfullyFlat T A := inferInstance
  have hSmooth {D : HopfAlgebraCategory k} (eD : D ≃ₐ[k] Polynomial k) :
      Smooth (specGroup D).X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k D)))
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    have hPoly : Algebra.Smooth k (Polynomial k) :=
      ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    exact (RingHom.smooth_algebraMap (R := k) (S := D)).mpr (Algebra.Smooth.of_equiv eD.symm)
  have hFlat : Flat F.hom.hom.left := by
    change Flat (Spec.map (CommRingCat.ofHom (hopfAlgHom a).toRingHom))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact inferInstanceAs (Module.Flat T A)
  have hSurj : Surjective F.hom.hom.left :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := T) (B := A)⟩
  have hIdeals : (kernelIdeal a).map e.toAlgHom = alphaIdeal k p := by
    rw [kernelIdeal_of_augmentation p a ha (e.symm Polynomial.X) (augmentation_additive e he),
      Ideal.map_span, Set.image_singleton]
    simp
  have hPres := presentsSchemeKernel a e _ hIdeals
  refine ⟨hSmooth e, hSmooth (polynomialTwistEquiv p e), hFlat, hSurj, ⟨b⟩, ?_, hPres, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := (dualKernelIso (hopfSpecPointIso A)).surjective x
    rw [tangentOfSpec_natural, frobenius_coordinateTangent_zero p a ha, map_zero]
  · obtain ⟨hh, _, _, j, _⟩ := hPres
    letI := hh
    let Q := hopfQuotient A (kernelIdeal a)
    let q := hopfQuotientMap A (kernelIdeal a)
    let M : Specs.ClosedSubgroup (specGroup A) := ⟨specGroup Q, specGroupMap q,
      (hopfMapClosedImmersion k q).mpr (Ideal.Quotient.mk_surjective (I := kernelIdeal a))⟩
    have hp := (Grp.forget (SchemeOver k)).map_isPullback (schemeKernel k a).1
    let E : (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ (SchemeOver k) :=
      Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
        change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
        rw [Spec.map_id, Category.comp_id])
    have hM : Specs.IsSchemeKernel F M := by
      change IsPullback (specGroupMap q).hom.hom (toUnit (specGroup Q).X) F.hom.hom η[(specGroup T).X]
      change IsPullback (specGroupMap q).hom.hom (specGroupMap (hopfUnit Q)).hom.hom
        F.hom.hom (specGroupMap (hopfCounit T)).hom.hom at hp
      refine hp.of_iso (Iso.refl _) (Iso.refl _) E (Iso.refl _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ?_
        ((Category.comp_id _).trans (Category.id_comp _).symm) ?_
      · simp only [Iso.refl_hom, Category.id_comp]
        exact toUnit_unique _ _
      · apply Over.OverMorphism.ext
        change (specGroupMap (hopfCounit T)).hom.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ (η[(specGroup T).X]).left
        rw [Category.comp_id, Category.id_comp, (hopfSpecOperations k T).2.1]
        rfl
    refine ⟨M, hM, ?_⟩
    intro hs
    have hr := isReduced_of_smooth_over_field M.group.X.hom
    have hQ : _root_.IsReduced Q := (affine_isReduced_iff (CommRingCat.of Q)).mp hr
    exact alphaCoordinates_not_reduced (k := k) p (isReduced_of_injective j.symm j.symm.injective)

theorem additiveFrobeniusExample : Specs.AdditiveFrobeniusExample.{u} := by
  intro k _ p _ _
  obtain ⟨h, hd, he, hi, hp⟩ := StandardGroups.additiveGroupSpecification k
  letI := h.hopf
  let A := CommHopfAlgCat.of k (Polynomial k)
  let a := RelativeFrobenius.pullback p A
  have ha := RelativeFrobenius.pullback_formula p A
  refine ⟨h, hd, he, hi, hp, a, ha, ?_⟩
  exact additiveFrobeniusBoundary k p A AlgEquiv.refl he a ha

end Frobenius

end

end LinearAlgebraicGroups
