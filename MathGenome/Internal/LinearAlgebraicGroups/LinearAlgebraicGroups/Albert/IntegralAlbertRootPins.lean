import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralAlbertRootPins
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootCoordinates
import Mathlib.LinearAlgebra.Contraction

open AlgebraicGeometry WithConv
open scoped TensorProduct AlgebraMonoidAlgebra

universe u

namespace LinearAlgebraicGroups.Albert.IntegralAlbertRootPins

open Specs.IntegralAlbertRootPins
open Specs.IntegralRecognition (Tangent dualCoefficients HasWeight IsWeightBasis)
open Specs.IntegralCentralQuotient (IntegralRing HopfSpectrum)

open private pointConvolutionGroup torusConjugation torusConjugation_eval counit_torusConjugation
  torusWeightProjection_idempotent torusProjection_comul
  tensorMonomialCoeff tangentWeightProjection
  restrictPoint restrictPoint_one restrictPoint_mul
  augmentedCotangent_free augmentedCotangent_finite integralRing_isDomain
  integralRing_isPrincipalIdealRing
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootCoordinates

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option linter.style.haveILetI false
attribute [local instance] pointConvolutionGroup

section Cotangent

variable {R A S : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing S] [Algebra R S]

local notation "ε" => Bialgebra.counitAlgHom R A
local notation "I" => RingHom.ker (ε).toRingHom
local notation "C" => IdentityCotangent R A
local notation "δ" => (identityDifferential (R := R) (A := A))

private theorem aug_val (a : A) :
    (augmentationPart (R := R) a : A) = a - algebraMap R A (ε a) := rfl

private theorem differential_ideal (a : I) :
    δ a.val = (I).toCotangent a := by
  have h : augmentationPart (R := R) a.val = a := by
    apply Subtype.ext
    rw [aug_val]
    have ha : ε a.val = 0 := a.property
    rw [ha, map_zero, sub_zero]
  exact congrArg (I).toCotangent h

private theorem differential_surj : Function.Surjective δ := by
  intro z
  obtain ⟨a, rfl⟩ := (I).toCotangent_surjective z
  exact ⟨a.val, differential_ideal a⟩

private theorem differential_const (r : R) : δ (algebraMap R A r) = 0 := by
  have h : augmentationPart (algebraMap R A r) = (0 : I) := by
    apply Subtype.ext
    rw [aug_val, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    rfl
  change (I).toCotangent (augmentationPart _) = 0
  rw [h, map_zero]

private theorem differential_mul (a b : A) :
    δ (a * b) = ε a • δ b + ε b • δ a := by
  let x : I := augmentationPart a
  let y : I := augmentationPart b
  have he : augmentationPart (a * b) = x * y + ε a • y + ε b • x := by
    apply Subtype.ext
    change (augmentationPart (a * b) : A) =
      (x : A) * (y : A) + ε a • (y : A) + ε b • (x : A)
    simp only [x, y, aug_val, Algebra.smul_def, map_mul]
    ring
  change (I).toCotangent (augmentationPart _) = ε a • (I).toCotangent y + ε b • (I).toCotangent x
  have hz : (I).toCotangent (x * y) = 0 :=
    ((I).toCotangent_eq_zero _).2 (by rw [pow_two]; exact Ideal.mul_mem_mul x.property y.property)
  rw [he, map_add, map_add, hz, zero_add]
  rw [← LinearMap.restrictScalars_apply R (I).toCotangent, map_smul,
    ← LinearMap.restrictScalars_apply R (I).toCotangent, map_smul]
  rfl

private abbrev RelativeTangent (R A S : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A]
    [CommRing S] [Algebra R S] :=
  {p : A →ₐ[R] DualNumber S //
    (TrivSqZeroExt.fstHom R S S).comp p = (Algebra.ofId R S).comp (Bialgebra.counitAlgHom R A)}

private def ofFunctional (f : C →ₗ[R] S) : RelativeTangent R A S := by
  let d := f.comp δ
  let p : A →ₐ[R] DualNumber S :=
    { toFun := fun a => (algebraMap R S (ε a), d a)
      map_zero' := TrivSqZeroExt.ext (by simp) (map_zero d)
      map_one' := TrivSqZeroExt.ext (by simp) (by
        change f (δ 1) = 0
        rw [← map_one (algebraMap R A), differential_const, map_zero])
      map_add' := fun a b => TrivSqZeroExt.ext (by simp) (map_add d a b)
      map_mul' := fun a b => TrivSqZeroExt.ext (by simp) (by
        change f (δ (a * b)) =
          algebraMap R S (ε a) * f (δ b) + f (δ a) * algebraMap R S (ε b)
        rw [differential_mul, map_add, map_smul, map_smul, Algebra.smul_def,
          Algebra.smul_def, mul_comm (algebraMap R S (ε b))])
      commutes' := fun r => TrivSqZeroExt.ext (by
        change algebraMap R S (ε (algebraMap R A r)) = algebraMap R S r
        rw [AlgHom.commutes, Algebra.algebraMap_self_apply]) (by
        change f (δ (algebraMap R A r)) = 0
        rw [differential_const, map_zero]) }
  exact ⟨p, AlgHom.ext fun _ => rfl⟩

private def slope (p : A →ₐ[R] DualNumber S) : A →ₗ[R] S :=
  ((TrivSqZeroExt.sndHom (R := S) (M := S)).restrictScalars R).comp p.toLinearMap

private def functional (p : RelativeTangent R A S) : C →ₗ[R] S :=
  Ideal.Cotangent.lift ((slope p.val).comp ((I).subtype.restrictScalars R)) fun a b => by
    change (p.val (a.val * b.val)).snd = 0
    have ha : (p.val a.val).fst = 0 :=
      (DFunLike.congr_fun p.property a.val).trans (by
        change algebraMap R S (ε a.val) = 0
        rw [(show ε a.val = 0 from a.property), map_zero])
    have hb : (p.val b.val).fst = 0 :=
      (DFunLike.congr_fun p.property b.val).trans (by
        change algebraMap R S (ε b.val) = 0
        rw [(show ε b.val = 0 from b.property), map_zero])
    rw [map_mul, DualNumber.snd_mul, ha, hb, zero_mul, mul_zero, add_zero]

private theorem functional_differential (p : RelativeTangent R A S) (a : A) :
    functional p (δ a) = (p.val a).snd := by
  change (p.val (augmentationPart (R := R) a : A)).snd = _
  rw [aug_val, map_sub, AlgHom.commutes]
  change (p.val a).snd - 0 = _
  exact sub_zero _

private theorem relativeTangent_ext {p q : RelativeTangent R A S}
    (h : ∀ a, (p.val a).snd = (q.val a).snd) : p = q := by
  apply Subtype.ext
  apply AlgHom.ext
  intro a
  exact TrivSqZeroExt.ext
    ((DFunLike.congr_fun p.property a).trans (DFunLike.congr_fun q.property a).symm) (h a)

end Cotangent

section Conjugation

variable {R A X : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]

local notation "ε" => Bialgebra.counitAlgHom R A
local notation "H" => MonoidAlgebra R X
local notation "δ" => (identityDifferential (R := R) (A := A))

private theorem conjugation_eq (t : A →ₐc[R] H) : conjugationPullback t = torusConjugation t := rfl

private theorem projection_idempotent (t : A →ₐc[R] H) (χ : X) (a : A) :
    characterProjection t χ (characterProjection t χ a) = characterProjection t χ a :=
  torusWeightProjection_idempotent t χ a

variable {S B : Type u} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
  [Algebra S B] [IsScalarTower R S B]

private def coefficientExtension : DualNumber S →ₐ[R] DualNumber B :=
  (dualCoefficients B).restrictScalars R

private def evaluateConjugation (p : RelativeTangent R A S) (s : H →ₐ[R] B) :
    A ⊗[R] H →ₐ[R] DualNumber B :=
  Algebra.TensorProduct.lift (coefficientExtension.comp p.val)
    ((TrivSqZeroExt.inlAlgHom R B B).comp s) (fun _ _ => Commute.all _ _)

private def conjugateSlope (d : A →ₗ[R] S) (s : H →ₐ[R] B) :
    (A ⊗[R] H) →ₗ[R] B :=
  LinearMap.mul' R B ∘ₗ TensorProduct.map
    (((Algebra.linearMap S B).restrictScalars R).comp d) s.toLinearMap

private theorem evaluateConjugation_snd (p : RelativeTangent R A S) (s : H →ₐ[R] B)
    (z : A ⊗[R] H) :
    (evaluateConjugation p s z).snd = conjugateSlope (slope p.val) s z := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    simp only [evaluateConjugation, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
      DualNumber.snd_mul, conjugateSlope, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.mul'_apply]
    change algebraMap S B (p.val a).fst * 0 + algebraMap S B (p.val a).snd * s b = _
    rw [mul_zero, zero_add]
    rfl
  · intro x y hx hy
    rw [map_add, TrivSqZeroExt.snd_add, map_add, hx, hy]

private theorem evaluateConjugation_fst (t : A →ₐc[R] H)
    (p : RelativeTangent R A S) (s : H →ₐ[R] B) (a : A) :
    (evaluateConjugation p s (conjugationPullback t a)).fst = algebraMap R B (ε a) := by
  have he :
      (TrivSqZeroExt.fstHom R B B).comp (evaluateConjugation p s) =
        (Algebra.TensorProduct.lid R B).toAlgHom.comp (Algebra.TensorProduct.map ε s) := by
    apply AlgHom.ext
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro x y
      simp only [AlgHom.comp_apply, evaluateConjugation, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.map_tmul]
      change algebraMap S B (p.val x).fst * s y = ε x • s y
      have h : (p.val x).fst = algebraMap R S (ε x) := DFunLike.congr_fun p.property x
      rw [h, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]
  have hfac : Algebra.TensorProduct.map ε s =
      (Algebra.TensorProduct.map (AlgHom.id R R) s).comp
        (Algebra.TensorProduct.map ε (AlgHom.id R H)) := by
    rw [← Algebra.TensorProduct.map_comp, AlgHom.id_comp, AlgHom.comp_id]
  have hc : Algebra.TensorProduct.map ε (AlgHom.id R H) (conjugationPullback t a) =
      ε a ⊗ₜ[R] (1 : H) := by
    rw [conjugation_eq]
    exact DFunLike.congr_fun (counit_torusConjugation t) a
  have h := DFunLike.congr_fun he (conjugationPullback t a)
  simp only [hfac, AlgHom.comp_apply, hc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    map_one] at h
  change _ = ε a • (1 : B) at h
  exact h.trans (by rw [Algebra.smul_def, mul_one])

private theorem conjugation_equation_iff (t : A →ₐc[R] H) (χ : X)
    (p : RelativeTangent R A S) (s : H →ₐ[R] B) :
    let g := toConv ((TrivSqZeroExt.inlAlgHom R B B).comp (s.comp t.toAlgHom))
    let q := coefficientExtension (R := R) (S := S) (B := B) |>.comp p.val
    let c := s (MonoidAlgebra.of R X χ)
    let scale := (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))).restrictScalars R
    g * toConv q * g⁻¹ = toConv (scale.comp q) ↔
      ∀ a, conjugateSlope (slope p.val) s (conjugationPullback t a) =
        c * algebraMap S B (p.val a).snd := by
  dsimp only
  have h := torusConjugation_eval t (evaluateConjugation p s)
  have hl : (evaluateConjugation p s).comp Algebra.TensorProduct.includeLeft =
      coefficientExtension.comp p.val := by
    unfold evaluateConjugation
    rw [Algebra.TensorProduct.lift_comp_includeLeft]
  have hr : (evaluateConjugation p s).comp Algebra.TensorProduct.includeRight =
      (TrivSqZeroExt.inlAlgHom R B B).comp s := by
    unfold evaluateConjugation
    rw [Algebra.TensorProduct.lift_comp_includeRight']
  dsimp only at h
  rw [hl, hr, AlgHom.comp_assoc, ← conjugation_eq] at h
  rw [← h]
  let c := s (MonoidAlgebra.of R X χ)
  let scale := (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))).restrictScalars R
  have hfst (a : A) :
      (scale (coefficientExtension (R := R) (p.val a))).fst =
        algebraMap S B (p.val a).fst := by
    change (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))
      (coefficientExtension (R := R) (p.val a))).fst = _
    rw [TrivSqZeroExt.fst_map]
    rfl
  have hsnd (a : A) :
      (scale (coefficientExtension (R := R) (p.val a))).snd =
        c * algebraMap S B (p.val a).snd := by
    change (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))
      (coefficientExtension (R := R) (p.val a))).snd = _
    rw [TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    rfl
  change toConv ((evaluateConjugation p s).comp (conjugationPullback t)) =
      toConv (scale.comp (coefficientExtension.comp p.val)) ↔ _
  constructor
  · intro eq a
    have ea := congrArg (fun e : WithConv (A →ₐ[R] DualNumber B) => (e.ofConv a).snd) eq
    exact (evaluateConjugation_snd p s _).symm.trans (ea.trans (hsnd a))
  · intro hs
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · change (evaluateConjugation p s (conjugationPullback t a)).fst =
        (scale (coefficientExtension (R := R) (p.val a))).fst
      rw [evaluateConjugation_fst, hfst]
      have hp : (p.val a).fst = algebraMap R S (ε a) := DFunLike.congr_fun p.property a
      rw [hp, ← IsScalarTower.algebraMap_apply]
    · change (evaluateConjugation p s (conjugationPullback t a)).snd =
        (scale (coefficientExtension (R := R) (p.val a))).snd
      rw [evaluateConjugation_snd, hsnd]
      exact hs a

private theorem conjugateSlope_coeff (d : A →ₗ[R] S) (χ : X) (z : A ⊗[R] H) :
    (conjugateSlope d (MonoidAlgebra.mapAlgHom X (Algebra.ofId R S)) z).coeff χ =
      d (tensorMonomialCoeff χ z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro a b
    change (algebraMap S (MonoidAlgebra S X) (d a) *
      MonoidAlgebra.mapAlgHom X (Algebra.ofId R S) b).coeff χ = d (b.coeff χ • a)
    rw [← Algebra.smul_def, MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_mapAlgHom,
      map_smul]
    simp only [smul_eq_mul, Algebra.smul_def, Algebra.ofId_apply, mul_comm]
  · intro x y hx hy
    rw [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, map_add, map_add, hx, hy]

private theorem slope_fixed_of_universal (t : A →ₐc[R] H) (χ : X)
    (p : RelativeTangent R A S)
    (h : ∀ a, conjugateSlope (slope p.val) (MonoidAlgebra.mapAlgHom X (Algebra.ofId R S))
      (conjugationPullback t a) =
      (MonoidAlgebra.mapAlgHom X (Algebra.ofId R S) (MonoidAlgebra.of R X χ)) *
        algebraMap S (MonoidAlgebra S X) (p.val a).snd) :
    functional p ∈ WeightSpace t χ S := by
  intro a
  have ha := congrArg (fun b : MonoidAlgebra S X => b.coeff χ) (h a)
  rw [conjugateSlope_coeff] at ha
  have hx : MonoidAlgebra.mapAlgHom X (Algebra.ofId R S) (MonoidAlgebra.of R X χ) =
      MonoidAlgebra.of S X χ := by simp [MonoidAlgebra.of_apply]
  rw [hx, mul_comm, ← Algebra.smul_def, MonoidAlgebra.coeff_smul_apply,
    MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_eq_same, smul_eq_mul, mul_one] at ha
  rw [functional_differential, functional_differential]
  exact ha

private theorem conjugateSlope_of_fixed (t : A →ₐc[R] H) (χ : X)
    (p : RelativeTangent R A S) (h : functional p ∈ WeightSpace t χ S)
    (s : H →ₐ[R] B) (a : A) :
    conjugateSlope (slope p.val) s (conjugationPullback t a) =
      s (MonoidAlgebra.of R X χ) * algebraMap S B (p.val a).snd := by
  have hf (b : A) : slope p.val (characterProjection t χ b) = slope p.val b := by
    have hb := h b
    rw [functional_differential, functional_differential] at hb
    exact hb
  let d := slope p.val
  have hm : (conjugateSlope d s).comp (TensorProduct.map (characterProjection t χ) LinearMap.id)
      = conjugateSlope d s := by
    unfold conjugateSlope
    rw [LinearMap.comp_assoc, ← TensorProduct.map_comp, LinearMap.comp_id]
    have he : (((Algebra.linearMap S B).restrictScalars R).comp d).comp
        (characterProjection t χ) = ((Algebra.linearMap S B).restrictScalars R).comp d :=
      LinearMap.ext fun z => congrArg (algebraMap S B) (hf z)
    rw [he]
  have hp : TensorProduct.map (characterProjection t χ) LinearMap.id (conjugationPullback t a) =
      characterProjection t χ a ⊗ₜ[R] MonoidAlgebra.of R X χ :=
    torusProjection_comul t χ a
  calc
    _ = (conjugateSlope d s)
        (TensorProduct.map (characterProjection t χ) LinearMap.id (conjugationPullback t a)) :=
      (DFunLike.congr_fun hm _).symm
    _ = _ := by
      rw [hp]
      change algebraMap S B (d (characterProjection t χ a)) * s (MonoidAlgebra.of R X χ) = _
      rw [hf, mul_comm]
      rfl

end Conjugation

section IntegralIdentification

variable {R A X : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]

local notation "ε" => Bialgebra.counitAlgHom R A
local notation "H" => MonoidAlgebra R X

private def asRelative (v : Tangent R A) : RelativeTangent R A R :=
  ⟨v.val, by simpa using v.property⟩

private def asTangent (p : RelativeTangent R A R) : Tangent R A :=
  ⟨p.val, by simpa using p.property⟩

private theorem hasWeight_iff_mem (t : A →ₐc[R] H) (χ : X) (v : Tangent R A) :
    HasWeight t χ v ↔ functional (asRelative v) ∈ WeightSpace t χ R := by
  constructor
  · intro h
    apply slope_fixed_of_universal t χ (asRelative v)
    exact (conjugation_equation_iff t χ (asRelative v)
      (MonoidAlgebra.mapAlgHom X (Algebra.ofId R R))).1
      (h (CommAlgCat.of R H) (MonoidAlgebra.mapAlgHom X (Algebra.ofId R R)))
  · intro h B s
    exact (conjugation_equation_iff t χ (asRelative v) s).2
      (conjugateSlope_of_fixed t χ (asRelative v) h s)

end IntegralIdentification

section FibreIdentification

variable {R A X S : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]
  [CommRing S] [Algebra R S]

local notation "H" => MonoidAlgebra R X

private theorem fibreCounit (a : A) :
    Bialgebra.counitAlgHom S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a) =
      algebraMap R S (Bialgebra.counitAlgHom R A a) :=
  DFunLike.congr_fun (Bialgebra.counitAlgHom_comp_includeRight (R := R) (A := S) (B := A)) a

private def restrictTangent (v : Tangent S (S ⊗[R] A)) : RelativeTangent R A S :=
  ⟨restrictPoint v.val, AlgHom.ext fun a => by
    have h := DFunLike.congr_fun v.property ((1 : S) ⊗ₜ[R] a)
    exact h.trans (fibreCounit a)⟩

private def liftTangent (p : RelativeTangent R A S) : Tangent S (S ⊗[R] A) := by
  let e := AlgHom.liftEquiv R S A (DualNumber S)
  let v := e p.val
  refine ⟨v, ?_⟩
  apply (AlgHom.liftEquiv R S A S).symm.injective
  apply AlgHom.ext
  intro a
  have h : v ((1 : S) ⊗ₜ[R] a) = p.val a := DFunLike.congr_fun (e.symm_apply_apply p.val) a
  change (v ((1 : S) ⊗ₜ[R] a)).fst = Bialgebra.counitAlgHom S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a)
  rw [h, fibreCounit]
  exact DFunLike.congr_fun p.property a

private theorem restrict_lift (p : RelativeTangent R A S) :
    restrictTangent (liftTangent p) = p :=
  Subtype.ext ((AlgHom.liftEquiv R S A (DualNumber S)).symm_apply_apply p.val)

private theorem restrictTangent_injective :
    Function.Injective (restrictTangent (R := R) (A := A) (S := S)) :=
  fun _ _ h => Subtype.ext (restrictPoint.injective (congrArg Subtype.val h))

private theorem extendedEquation_iff {B : Type u} [CommRing B] [Algebra S B]
    [Algebra R B] [IsScalarTower R S B] (t : A →ₐc[R] H) (χ : X)
    (v : Tangent S (S ⊗[R] A)) (s : S ⊗[R] H →ₐ[S] B) :
    let tS := Bialgebra.TensorProduct.map (BialgHom.id S S) t
    let g := toConv ((TrivSqZeroExt.inlAlgHom S B B).comp (s.comp tS.toAlgHom))
    let p := (dualCoefficients B).comp v.val
    let c := s ((1 : S) ⊗ₜ[R] MonoidAlgebra.of R X χ)
    let scale := (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))).restrictScalars S
    g * toConv p * g⁻¹ = toConv (scale.comp p) ↔
      ∀ a, conjugateSlope (slope (restrictTangent v).val) (restrictPoint s)
        (conjugationPullback t a) = c * algebraMap S B (v.val ((1 : S) ⊗ₜ[R] a)).snd := by
  dsimp only
  let tS := Bialgebra.TensorProduct.map (BialgHom.id S S) t
  let g := toConv ((TrivSqZeroExt.inlAlgHom S B B).comp (s.comp tS.toAlgHom))
  let p := (dualCoefficients B).comp v.val
  let c := s ((1 : S) ⊗ₜ[R] MonoidAlgebra.of R X χ)
  let scale := (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))).restrictScalars S
  let j : WithConv (S ⊗[R] A →ₐ[S] DualNumber B) →* WithConv (A →ₐ[R] DualNumber B) :=
    { toFun := fun f => toConv (restrictPoint f.ofConv)
      map_mul' := restrictPoint_mul
      map_one' := restrictPoint_one }
  have hj : Function.Injective j := fun f q eq =>
    WithConv.ofConv_injective (restrictPoint.injective (congrArg WithConv.ofConv eq))
  change g * toConv p * g⁻¹ = toConv (scale.comp p) ↔ _
  rw [← hj.eq_iff, map_mul, map_mul, map_inv]
  have hg : j g = toConv ((TrivSqZeroExt.inlAlgHom R B B).comp
      ((restrictPoint s).comp t.toAlgHom)) := by
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (TrivSqZeroExt.inlAlgHom S B B) (s (tS ((1 : S) ⊗ₜ[R] a))) =
      (TrivSqZeroExt.inlAlgHom R B B) (s ((1 : S) ⊗ₜ[R] t a))
    rw [Bialgebra.TensorProduct.map_tmul]
    rfl
  rw [hg]
  exact conjugation_equation_iff t χ (restrictTangent v) (restrictPoint s)

private theorem hasExtendedWeight_iff_mem (t : A →ₐc[R] H) (χ : X)
    (v : Tangent S (S ⊗[R] A)) :
    HasExtendedWeight t χ S v ↔ functional (restrictTangent v) ∈ WeightSpace t χ S := by
  constructor
  · intro h
    let B := MonoidAlgebra S X
    let j : H →ₐ[R] B := MonoidAlgebra.mapAlgHom X (Algebra.ofId R S)
    let e := AlgHom.liftEquiv R S H B
    let s := e j
    have hs : (restrictPoint s : H →ₐ[R] B) = j := e.symm_apply_apply j
    have hc : s ((1 : S) ⊗ₜ[R] MonoidAlgebra.of R X χ) = j (MonoidAlgebra.of R X χ) :=
      DFunLike.congr_fun hs _
    have hw := (extendedEquation_iff t χ v s).mp (h (CommAlgCat.of S B) s)
    rw [hs, hc] at hw
    exact slope_fixed_of_universal t χ (restrictTangent v) hw
  · intro h B s
    letI : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
    letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact (extendedEquation_iff t χ v s).mpr
      (conjugateSlope_of_fixed t χ (restrictTangent v) h (restrictPoint s))

end FibreIdentification

section WeightProjection

variable {R A X : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]

local notation "ε" => Bialgebra.counitAlgHom R A
local notation "I" => RingHom.ker (ε).toRingHom
local notation "C" => IdentityCotangent R A
local notation "H" => MonoidAlgebra R X
local notation "δ" => (identityDifferential (R := R) (A := A))

private theorem cotangent_separated [Module.Free R C] {z : C}
    (h : ∀ f : C →ₗ[R] R, f z = 0) : z = 0 := by
  let b := Module.Free.chooseBasis R C
  apply b.repr.injective
  ext i
  simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using h (b.coord i)

private theorem projected_slope (t : A →ₐc[R] H) (χ : X) (f : C →ₗ[R] R) :
    ∃ w : Tangent R A, ∀ a, (w.val a).snd = f (δ (characterProjection t χ a)) := by
  obtain ⟨w, _, hw⟩ := tangentWeightProjection t (asTangent (ofFunctional f)) χ
  exact ⟨w, hw⟩

private def cotangentProjector [Module.Free R C] (t : A →ₐc[R] H) (χ : X) : C →ₗ[R] C :=
  Ideal.Cotangent.lift
    ((δ).comp ((characterProjection t χ).comp ((I).subtype.restrictScalars R))) fun a b => by
      apply cotangent_separated
      intro f
      obtain ⟨w, hw⟩ := projected_slope t χ f
      change f (δ (characterProjection t χ (a.val * b.val))) = 0
      have ha : (w.val a.val).fst = 0 :=
        (DFunLike.congr_fun w.property a.val).trans (show ε a.val = 0 from a.property)
      have hb : (w.val b.val).fst = 0 :=
        (DFunLike.congr_fun w.property b.val).trans (show ε b.val = 0 from b.property)
      rw [← hw, map_mul, DualNumber.snd_mul, ha, hb, zero_mul, mul_zero, add_zero]

private theorem cotangentProjector_apply [Module.Free R C]
    (t : A →ₐc[R] H) (χ : X) (a : A) :
    cotangentProjector t χ (δ a) = δ (characterProjection t χ a) := by
  have hc : δ (characterProjection t χ (algebraMap R A (ε a))) = 0 := by
    apply cotangent_separated
    intro f
    obtain ⟨w, hw⟩ := projected_slope t χ f
    rw [← hw, AlgHom.commutes]
    rfl
  change δ (characterProjection t χ (augmentationPart (R := R) a : A)) = _
  rw [aug_val, map_sub, map_sub, hc, sub_zero]

variable [Module.Free R (IdentityCotangent R A)]
variable {S : Type u} [CommRing S] [Algebra R S]

private def weightRetraction (t : A →ₐc[R] H) (χ : X) :
    (C →ₗ[R] S) →ₗ[S] WeightSpace t χ S where
  toFun f := ⟨f.comp (cotangentProjector t χ), fun a => by
    simp only [LinearMap.comp_apply, cotangentProjector_apply, projection_idempotent]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem weightRetraction_left (t : A →ₐc[R] H) (χ : X) (f : WeightSpace t χ S) :
    weightRetraction t χ f.val = f := by
  apply Subtype.ext
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := differential_surj z
  change f.val (cotangentProjector t χ (δ a)) = f.val (δ a)
  rw [cotangentProjector_apply]
  exact f.property a

private def allSlopeExtension (S : Type u) [CommRing S] [Algebra R S] :
    (S ⊗[R] (C →ₗ[R] R)) →ₗ[S] (C →ₗ[R] S) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s =>
        { toFun := fun f => s • ((Algebra.linearMap R S).comp f)
          map_add' := fun f g => by ext z; simp [mul_add]
          map_smul' := fun c f => by ext z; simp [Algebra.smul_def]; ring }
      map_add' := fun s s' => by ext f z; simp [add_mul]
      map_smul' := fun c s => by ext f z; simp [mul_assoc] }

omit [Module.Free R (IdentityCotangent R A)] in
private theorem allSlopeExtension_tmul (s : S) (f : C →ₗ[R] R) (z : C) :
    allSlopeExtension (R := R) (A := A) S (s ⊗ₜ[R] f) z = s * algebraMap R S (f z) := rfl

private theorem allSlopeExtension_bijective [Module.Finite R C] :
    Function.Bijective (allSlopeExtension (R := R) (A := A) S) := by
  classical
  let b := Module.Free.chooseBasis R C
  let e := (TensorProduct.comm R S (C →ₗ[R] R)).trans (dualTensorHomEquivOfBasis (N := S) b)
  have he : (allSlopeExtension (R := R) (A := A) S).restrictScalars R = e.toLinearMap := by
    apply TensorProduct.ext'
    intro s f
    ext z
    change allSlopeExtension S (s ⊗ₜ[R] f) z = e (s ⊗ₜ[R] f) z
    rw [allSlopeExtension_tmul]
    simp only [e, LinearEquiv.trans_apply, TensorProduct.comm_tmul, dualTensorHomEquivOfBasis_apply,
      dualTensorHom_apply, Algebra.smul_def, mul_comm]
  have hfun : ⇑(allSlopeExtension (R := R) (A := A) S) = ⇑e :=
    funext (DFunLike.congr_fun he)
  rw [hfun]
  exact e.bijective

private theorem weightScalarExtension [Module.Finite R C] (t : A →ₐc[R] H) (χ : X) :
    ∃ e : (S ⊗[R] WeightSpace t χ R) ≃ₗ[S] WeightSpace t χ S,
      ∀ s f z, (e (s ⊗ₜ[R] f)).val z = s * algebraMap R S (f.val z) := by
  let i := (WeightSpace t χ R).subtype
  let p := weightRetraction (S := R) t χ
  let q := weightRetraction (S := S) t χ
  let e := allSlopeExtension (R := R) (A := A) S
  have he : Function.Bijective e := allSlopeExtension_bijective
  let F := q.comp (e.comp (i.baseChange S))
  have hF (x : S ⊗[R] WeightSpace t χ R) :
      (F x).val = e (i.baseChange S x) := by
    induction x using TensorProduct.inductionOn with
    | tmul s f =>
      apply LinearMap.ext
      intro z
      change e (i.baseChange S (s ⊗ₜ[R] f)) (cotangentProjector t χ z) =
        e (i.baseChange S (s ⊗ₜ[R] f)) z
      rw [LinearMap.baseChange_tmul, allSlopeExtension_tmul, allSlopeExtension_tmul]
      exact congrArg (fun x => s * algebraMap R S x)
        (DFunLike.congr_fun (congrArg Subtype.val (weightRetraction_left t χ f)) z)
    | add x y hx hy =>
      rw [map_add, Submodule.coe_add, hx, hy, map_add, map_add]
  have hpi : p.comp i = LinearMap.id :=
    LinearMap.ext (weightRetraction_left t χ)
  have hil : Function.Injective (i.baseChange S) := by
    apply Function.LeftInverse.injective (g := p.baseChange S)
    intro x
    change (p.baseChange S ∘ₗ i.baseChange S) x = x
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
    rfl
  have hcomm (x : S ⊗[R] (C →ₗ[R] R)) :
      e (i.baseChange S (p.baseChange S x)) = (q (e x)).val := by
    induction x using TensorProduct.inductionOn with
    | tmul s f =>
      apply LinearMap.ext
      intro z
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, allSlopeExtension_tmul]
      change s * algebraMap R S (f (cotangentProjector t χ z)) =
        e (s ⊗ₜ[R] f) (cotangentProjector t χ z)
      rw [allSlopeExtension_tmul]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, map_add, map_add, Submodule.coe_add]
  have hbij : Function.Bijective F := by
    constructor
    · intro x y eq
      apply hil
      apply he.1
      rw [← hF, ← hF, eq]
    · intro f
      obtain ⟨x, hx⟩ := he.2 f.val
      refine ⟨p.baseChange S x, Subtype.ext ?_⟩
      rw [hF, hcomm, hx, weightRetraction_left]
  refine ⟨LinearEquiv.ofBijective F hbij, fun s f z => ?_⟩
  change (F (s ⊗ₜ[R] f)).val z = _
  rw [hF, LinearMap.baseChange_tmul, allSlopeExtension_tmul]
  rfl

end WeightProjection

section Correspondence

variable {R A S : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing S] [Algebra R S]

local notation "C" => IdentityCotangent R A
local notation "δ" => (identityDifferential (R := R) (A := A))

private theorem functional_ext {f g : C →ₗ[R] S} (h : ∀ a, f (δ a) = g (δ a)) : f = g := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ := differential_surj z
  exact h a

private theorem functional_ofFunctional (f : C →ₗ[R] S) :
    functional (ofFunctional f) = f :=
  functional_ext fun a => functional_differential (ofFunctional f) a

end Correspondence

private theorem smoothAlgebra {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
    (h : Smooth (HopfSpectrum R A).X.hom) : Algebra.Smooth R A := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R A))) at h
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp h)

/-- The split tangent weight summands and their dual-number description commute
with extension to any coefficient algebra. -/
theorem weightBaseChange : WeightBaseChange.{u} := by
  intro R A X _ _ _ _ _ _ t χ _ hs _
  letI : Algebra.Smooth R A := smoothAlgebra hs
  letI : Module.Free R (IdentityCotangent R A) := augmentedCotangent_free (Bialgebra.counitAlgHom R A)
  letI : Module.Finite R (IdentityCotangent R A) := augmentedCotangent_finite (Bialgebra.counitAlgHom R A)
  refine ⟨⟨LinearMap.ker (weightRetraction (S := R) t χ),
      LinearMap.isCompl_of_proj (weightRetraction_left t χ)⟩, ?_, ?_, ?_⟩
  · intro v
    rw [hasWeight_iff_mem]
    constructor
    · intro hv
      exact ⟨⟨_, hv⟩, fun a => (functional_differential (asRelative v) a).symm,
        fun f hf => Subtype.ext (functional_ext fun a =>
          (hf a).symm.trans (functional_differential (asRelative v) a).symm)⟩
    · rintro ⟨f, hf, _⟩
      have he : functional (asRelative v) = f.val :=
        functional_ext fun a => (functional_differential (asRelative v) a).trans (hf a)
      rw [he]
      exact f.property
  · intro f
    let p := ofFunctional f.val
    let v := asTangent p
    have hv : HasWeight t χ v := (hasWeight_iff_mem t χ v).mpr (by
      change functional p ∈ WeightSpace t χ R
      rw [functional_ofFunctional]
      exact f.property)
    refine ⟨v, ⟨hv, fun _ => rfl⟩, fun w hw => ?_⟩
    exact congrArg asTangent (relativeTangent_ext (p := asRelative w) (q := p) hw.2)
  · intro S _ _
    refine ⟨weightScalarExtension t χ, ?_, ?_⟩
    · intro v
      rw [hasExtendedWeight_iff_mem]
      constructor
      · intro hv
        exact ⟨⟨_, hv⟩, fun a => (functional_differential (restrictTangent v) a).symm,
          fun f hf => Subtype.ext (functional_ext fun a =>
            (hf a).symm.trans (functional_differential (restrictTangent v) a).symm)⟩
      · rintro ⟨f, hf, _⟩
        have he : functional (restrictTangent v) = f.val :=
          functional_ext fun a => (functional_differential (restrictTangent v) a).trans (hf a)
        rw [he]
        exact f.property
    · intro f
      let p := ofFunctional f.val
      let v := liftTangent p
      have hv : HasExtendedWeight t χ S v := (hasExtendedWeight_iff_mem t χ v).mpr (by
        rw [restrict_lift, functional_ofFunctional]
        exact f.property)
      have hval (a : A) : (v.val ((1 : S) ⊗ₜ[R] a)).snd =
          f.val (identityDifferential a) :=
        congrArg (fun p : RelativeTangent R A S => (p.val a).snd) (restrict_lift p)
      refine ⟨v, ⟨hv, hval⟩, fun w hw => restrictTangent_injective ?_⟩
      exact relativeTangent_ext fun a => (hw.2 a).trans (hval a).symm

private theorem pin_of_rank_one {R A X K : Type u} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]
    [Field K] [Algebra R K]
    (t : A →ₐc[R] MonoidAlgebra R X) (χ : X)
    (hf : Algebra.FinitePresentation R A) (hs : Smooth (HopfSpectrum R A).X.hom)
    (ht : Function.Surjective t) (hk : Module.finrank K (WeightSpace t χ K) = 1) :
    ∃ v : Tangent R A, IsWeightBasis t χ v := by
  letI : Algebra.Smooth R A := smoothAlgebra hs
  letI : Module.Free R (IdentityCotangent R A) := augmentedCotangent_free (Bialgebra.counitAlgHom R A)
  letI : Module.Finite R (IdentityCotangent R A) := augmentedCotangent_finite (Bialgebra.counitAlgHom R A)
  let W := WeightSpace t χ R
  letI : Module.Finite R W := Module.Finite.of_surjective (weightRetraction t χ)
    (fun f => ⟨f.val, weightRetraction_left t χ f⟩)
  letI : Module.IsTorsionFree R W := by
    dsimp [W]
    infer_instance
  letI : Module.Free R W := Module.free_of_finite_type_torsion_free' (R := R) (M := W)
  obtain ⟨_, hto, hfrom, hbase⟩ := weightBaseChange t χ hf hs ht
  obtain ⟨e, _⟩ := (hbase K).1
  have hr : Module.finrank R W = 1 := by
    rw [← Module.finrank_baseChange (R := K), e.finrank_eq, hk]
  obtain ⟨b⟩ := (finrank_eq_one_iff (K := R) (V := W) Unit).mp hr
  let f := b ()
  obtain ⟨v, ⟨hv, hvs⟩, _⟩ := hfrom f
  refine ⟨v, hv, fun w hw => ?_⟩
  obtain ⟨g, hgs, _⟩ := (hto w).mp hw
  let c := b.repr g ()
  have hc : c • f = g := by simpa [c, f] using b.sum_repr g
  refine ⟨c, fun a => ?_, fun d hd => ?_⟩
  · rw [hgs a, hvs a, ← hc]
    rfl
  · have he : d • f = g := by
      apply Subtype.ext
      apply functional_ext
      intro a
      change d * f.val (identityDifferential a) = g.val (identityDifferential a)
      rw [← hvs a, ← hgs a, hd a]
    calc
      d = b.repr (d • f) () := by simp [f]
      _ = c := congrArg (fun w => b.repr w ()) he

/-- Pick one integral tangent basis for each of the given characters. -/
theorem pinChoices : PinChoices.{u} := by
  intro A X J _ _ _ _ t χ hf hs ht K _ _ _ _ hk
  letI : IsDomain IntegralRing.{u} := integralRing_isDomain
  letI : IsPrincipalIdealRing IntegralRing.{u} := integralRing_isPrincipalIdealRing
  choose pin hp using fun j => pin_of_rank_one t (χ j) hf hs ht (hk j)
  exact ⟨pin, hp⟩

/-- Apply the pin construction to the simple roots of the specified based datum. -/
theorem simpleRootPins : SimpleRootPins.{u} := by
  intro D A _ _ t hf hs ht K _ _ _ _ hk
  exact pinChoices t (fun i : ↥D.base.support => Multiplicative.ofAdd (D.datum.root i.val))
    hf hs ht K hk

end

end LinearAlgebraicGroups.Albert.IntegralAlbertRootPins
