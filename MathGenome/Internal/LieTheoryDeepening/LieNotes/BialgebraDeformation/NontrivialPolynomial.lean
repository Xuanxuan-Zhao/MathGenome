import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.BialgebraDeformation.NontrivialPolynomial
import MathGenome.Internal.LieTheoryDeepening.LieNotes.BialgebraDeformation.FirstOrder
import MathGenome.Internal.LieTheoryDeepening.LieNotes.BialgebraDeformation.SkewPrimitiveHopf
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Basic
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open scoped TensorProduct

namespace LieNotes.BialgebraDeformation

open PowerSeries TensorProduct LieNotes.Coboundary

open private primitivePlaneBialgebra from MathGenome.Internal.LieTheoryDeepening.LieNotes.BialgebraDeformation.SkewPrimitiveHopf
open private mem_seriesVariableIdeal_pow from MathGenome.Internal.LieTheoryDeepening.LieNotes.BialgebraDeformation.CompletedPolynomialMaps

noncomputable section

universe u v

variable {k : Type u} [Field k]

private theorem firstOrderSeries_coeffs {A : Type v} [CommRing A] [Algebra k A]
    (p : PowerSeries A) :
    coeff₀ (firstOrderSeries (k := k) p) = constantCoeff p ∧
    coeff₁ (firstOrderSeries (k := k) p) = coeff 1 p := by
  constructor <;> simp [firstOrderSeries]

/-- The two-coefficient map realizes the quotient by the square of the parameter. -/
theorem firstOrderSeries_reduction : Expected.firstOrderSeries := by
  intro k A _ _ _
  let q := firstOrderSeries (k := k) (A := A)
  have hmul (p r : PowerSeries A) : q (p * r) = q p * q r := by
    change firstOrderSeries (p * r) = firstOrderSeries p * firstOrderSeries r
    simp only [firstOrderSeries, map_mul, coeff_one_mul, add_mul, mul_add,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, DualNumber.eps_mul_eps,
      TensorProduct.zero_tmul, add_zero, TensorProduct.tmul_add]
    rw [mul_comm (coeff 1 r) (constantCoeff p), add_assoc]
  refine ⟨?_, ?_, ?_, hmul, ?_, ?_, ?_⟩
  · intro z
    refine ⟨C (coeff₀ z) + C (coeff₁ z) * X, ?_⟩
    calc
      q (C (coeff₀ z) + C (coeff₁ z) * X) =
          (1 : D k) ⊗ₜ[k] coeff₀ z + (DualNumber.eps : D k) ⊗ₜ[k] coeff₁ z := by
        simp [q, firstOrderSeries]
      _ = z := (coefficient_decomposition (k := k) (X := A) z).symm
  · intro p r
    rw [mem_seriesVariableIdeal_pow]
    constructor
    · intro h i hi
      have h0 := congrArg (coeff₀ (k := k) (X := A)) h
      have h1 := congrArg (coeff₁ (k := k) (X := A)) h
      rw [(firstOrderSeries_coeffs p).1, (firstOrderSeries_coeffs r).1] at h0
      rw [(firstOrderSeries_coeffs p).2, (firstOrderSeries_coeffs r).2] at h1
      interval_cases i
      · simp only [map_sub, coeff_zero_eq_constantCoeff_apply, h0, sub_self]
      · simp only [map_sub, h1, sub_self]
    · intro h
      have h0 := h 0 (by decide)
      have h1 := h 1 (by decide)
      simp only [map_sub, sub_eq_zero, coeff_zero_eq_constantCoeff_apply] at h0 h1
      simp only [firstOrderSeries, h0, h1]
  · intro p r
    simp only [firstOrderSeries, map_add, TensorProduct.tmul_add]
    abel
  · simp [firstOrderSeries, Algebra.TensorProduct.one_def]
  · simp [firstOrderSeries, coeff_X]
  · intro p r
    change q (_ * r) = _
    rw [hmul]
    change firstOrderSeries (k := k) (PowerSeries.map (algebraMap k A) p) * q r =
      scalarCoordinates k (firstOrderSeries (k := k) p) • q r
    have hs (a : D k) (z : Extended k A) : a • z = (a ⊗ₜ[k] (1 : A)) * z := by
      induction z using TensorProduct.inductionOn with
      | tmul b x =>
        let : IsScalarTower k (D k) (D k) :=
          ⟨fun c b z =>
            (congrArg (· * z) (Algebra.smul_def c b)).trans
              ((mul_assoc _ _ _).trans (Algebra.smul_def c (b * z)).symm)⟩
        calc
          a • (b ⊗ₜ[k] x) = (a * b) ⊗ₜ[k] x := TensorProduct.smul_tmul' a b x
          _ = (a ⊗ₜ[k] (1 : A)) * (b ⊗ₜ[k] x) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | add z w hz hw =>
        exact (smul_add a z w).trans ((congrArg₂ (· + ·) hz hw).trans (mul_add _ _ _).symm)
    rw [hs]
    congr 1
    simp only [firstOrderSeries, map_add, PowerSeries.coeff_map, ← coeff_zero_eq_constantCoeff_apply,
      AlgebraTensorModule.rid_tmul]
    have h (a : k) : algebraMap k A a = a • (1 : A) := Algebra.algebraMap_eq_smul_one a
    rw [h, h, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]

section Series

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

private def constantPart (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B) : A →ₗ[k] B :=
  ((coeff 0).restrictScalars k).comp (onSeriesConstants F).toLinearMap

private def linearPart (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B) : A →ₗ[k] B :=
  ((coeff 1).restrictScalars k).comp (onSeriesConstants F).toLinearMap

private theorem constantPart_apply (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B) (a : A) :
    constantPart F a = constantCoeff (F (C a)) :=
  coeff_zero_eq_constantCoeff_apply _

private theorem coeff_one_apply (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B)
    (hF : SeriesContinuous F) (p : PowerSeries A) :
    coeff 1 (F p) = linearPart F (constantCoeff p) + constantPart F (coeff 1 p) := by
  have h : F = extendSeries (onSeriesConstants F) :=
    seriesHom_ext _ _ hF (extendSeries_continuous _) (fun a => (extendSeries_C (onSeriesConstants F) a).symm)
  conv_lhs => rw [h, extendSeries_coeff]
  simp only [show (1 : ℕ) + 1 = 2 by decide, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Nat.sub_zero, Nat.sub_self, coeff_zero_eq_constantCoeff_apply]
  rw [constantPart_apply]
  rfl

private theorem firstOrderSeries_map (F : PowerSeries A →ₐ[PowerSeries k] PowerSeries B)
    (hF : SeriesContinuous F) (f : A →ₗ[k] B)
    (hf : ∀ p, constantCoeff (F p) = f (constantCoeff p)) (p : PowerSeries A) :
    firstOrderSeries (F p) = jet f (linearPart F) (firstOrderSeries p) := by
  have h : constantPart F = f := LinearMap.ext fun a => by
    rw [constantPart_apply, hf, constantCoeff_C]
  simp only [firstOrderSeries, hf, coeff_one_apply F hF, h, map_add, jet_tmul,
    mul_one, DualNumber.eps_mul_eps, TensorProduct.zero_tmul, add_zero, TensorProduct.tmul_add]
  abel

private theorem constantCoeff_pair (p : PowerSeries A) (r : PowerSeries B) :
    constantCoeff (seriesTensorPair (k := k) p r) = constantCoeff p ⊗ₜ[k] constantCoeff r := by
  simp only [seriesTensorPair, map_mul, ← coeff_zero_eq_constantCoeff_apply, seriesMap_coeff,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

private theorem coeff_one_pair (p : PowerSeries A) (r : PowerSeries B) :
    coeff 1 (seriesTensorPair (k := k) p r) =
      coeff 1 p ⊗ₜ[k] constantCoeff r + constantCoeff p ⊗ₜ[k] coeff 1 r := by
  simp only [seriesTensorPair, coeff_one_mul, ← coeff_zero_eq_constantCoeff_apply, seriesMap_coeff,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end Series

/-- The reduced completed tensor pairing is the tensor product over the dual numbers. -/
theorem firstOrderSeries_tensor : Expected.firstOrderTensor := by
  intro k A B _ _ _ _ _ p r
  simp only [firstOrderSeries, constantCoeff_pair, coeff_one_pair,
    TensorProduct.add_tmul, TensorProduct.tmul_add, map_add,
    AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul, mul_one,
    DualNumber.eps_mul_eps, zero_tmul, add_zero]
  abel

section Plane

variable [CharZero k]

local notation "P" => Plane k
local notation "Q" => PlaneTensorSquare k
local notation "d" => primitivePlaneComul (k := k)
local notation "c" => primitivePlaneCounit (k := k)
local notation "I" => (LinearMap.id : P →ₗ[k] P)

private theorem coeff_plane_x (H : CompletedPlaneHopf k) : firstOrderPlaneComul H planeX = 0 := by
  change coeff 1 (H.comul (C planeX)) = 0
  rw [H.comul_x, map_add, coeff_one_pair, coeff_one_pair]
  simp

private theorem coeff_plane_y (H : CompletedPlaneHopf k) :
    firstOrderPlaneComul H planeY = planeX ⊗ₜ[k] planeY := by
  change coeff 1 (H.comul (C planeY)) = _
  rw [H.comul_y, map_add, coeff_one_pair, coeff_one_pair]
  simp

omit [CharZero k] in
private theorem completed_counit_eq (H : CompletedPlaneHopf k) : H.counit = seriesMap c := by
  apply seriesPolynomialExt _ _ H.counit_continuous (seriesMap_continuous _)
  rw [Fin.forall_fin_two]
  constructor
  · change H.counit (C planeX) = seriesMap c (C planeX)
    rw [H.counit_x, seriesMap_C]
    simp [primitivePlaneCounit]
  · change H.counit (C planeY) = seriesMap c (C planeY)
    rw [H.counit_y, seriesMap_C]
    simp [primitivePlaneCounit]

private theorem completed_counit_const (H : CompletedPlaneHopf k) (a : P) :
    H.counit (C a) = C (c a) :=
  (AlgHom.congr_fun (completed_counit_eq H) (C a)).trans (seriesMap_C c a)

private theorem completed_counit_firstOrder (H : CompletedPlaneHopf k) (p : PowerSeries P) :
    firstOrderSeries (k := k) (H.counit p) = jet (c).toLinearMap 0 (firstOrderSeries p) := by
  have h : coeff 1 (H.counit p) = c (coeff 1 p) :=
    (congrArg (coeff 1) (AlgHom.congr_fun (completed_counit_eq H) p)).trans
      (seriesMap_coeff c p 1)
  simp only [firstOrderSeries, H.specialize_counit, h, map_add, jet_tmul,
    LinearMap.zero_apply, tmul_zero, add_zero, AlgHom.toLinearMap_apply]

omit [CharZero k] in
private theorem counit_leg_coeff (F : PowerSeries Q →ₐ[PowerSeries k] PowerSeries P)
    (hF : SeriesContinuous F) (φ : Q →ₗ[k] P)
    (h : ∀ a b, F (C (a ⊗ₜ[k] b)) = C (φ (a ⊗ₜ[k] b))) (p : PowerSeries Q) :
    coeff 1 (F p) = φ (coeff 1 p) := by
  have h0 : constantPart F = φ := TensorProduct.ext' fun a b => by
    rw [constantPart_apply, h, constantCoeff_C]
  have h1 : linearPart F = 0 := TensorProduct.ext' fun a b => by
    change coeff 1 (F (C (a ⊗ₜ[k] b))) = 0
    rw [h]
    simp
  rw [coeff_one_apply F hF, h0, h1, LinearMap.zero_apply, zero_add]

private theorem coeff_counit_left (H : CompletedPlaneHopf k) :
    (TensorProduct.map (c).toLinearMap I).comp (firstOrderPlaneComul H) = 0 := by
  obtain ⟨F, hF, hl⟩ := H.left_counit
  let lid := TensorProduct.lid k P
  have h := counit_leg_coeff F hF.1 (lid.toLinearMap.comp (TensorProduct.map (c).toLinearMap I))
    (fun a b => by
      rw [hF.2.2, Algebra.TensorProduct.productMap_apply_tmul]
      change completedPlaneUnit (H.counit (C a)) * C b =
        C ((TensorProduct.lid k P) ((TensorProduct.map (c).toLinearMap I) (a ⊗ₜ[k] b)))
      rw [completed_counit_const, show completedPlaneUnit (C (c a)) = C (algebraMap k P (c a)) from
        seriesMap_C (Algebra.ofId k P) (c a)]
      simp [← map_mul, Algebra.smul_def])
  apply LinearMap.ext
  intro p
  apply lid.injective
  have hp := h (H.comul (C p))
  rw [show F (H.comul (C p)) = C p from AlgHom.congr_fun hl (C p)] at hp
  simpa [firstOrderPlaneComul, linearPart] using hp.symm

private theorem coeff_counit_right (H : CompletedPlaneHopf k) :
    (TensorProduct.map I (c).toLinearMap).comp (firstOrderPlaneComul H) = 0 := by
  obtain ⟨F, hF, hr⟩ := H.right_counit
  let rid := TensorProduct.rid k P
  have h := counit_leg_coeff F hF.1 (rid.toLinearMap.comp (TensorProduct.map I (c).toLinearMap))
    (fun a b => by
      rw [hF.2.2, Algebra.TensorProduct.productMap_apply_tmul]
      change C a * completedPlaneUnit (H.counit (C b)) =
        C ((TensorProduct.rid k P) ((TensorProduct.map I (c).toLinearMap) (a ⊗ₜ[k] b)))
      rw [completed_counit_const, show completedPlaneUnit (C (c b)) = C (algebraMap k P (c b)) from
        seriesMap_C (Algebra.ofId k P) (c b)]
      simp [← map_mul, Algebra.smul_def, mul_comm])
  apply LinearMap.ext
  intro p
  apply rid.injective
  have hp := h (H.comul (C p))
  rw [show F (H.comul (C p)) = C p from AlgHom.congr_fun hr (C p)] at hp
  simpa [firstOrderPlaneComul, linearPart] using hp.symm

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem coeff_coassoc (H : CompletedPlaneHopf k) :
    let g := firstOrderPlaneComul H
    (TensorProduct.assoc k P P P).toLinearMap.comp
      ((TensorProduct.map (d).toLinearMap I).comp g + (TensorProduct.map g I).comp (d).toLinearMap) -
      (TensorProduct.map I (d).toLinearMap).comp g - (TensorProduct.map I g).comp (d).toLinearMap = 0 := by
  let g := firstOrderPlaneComul H
  change (TensorProduct.assoc k P P P).toLinearMap.comp
      ((TensorProduct.map (d).toLinearMap I).comp g + (TensorProduct.map g I).comp (d).toLinearMap) -
      (TensorProduct.map I (d).toLinearMap).comp g - (TensorProduct.map I g).comp (d).toLinearMap = 0
  obtain ⟨L, R, hL, hR, h⟩ := H.coassociative
  have hLa (a b : P) : L (C (a ⊗ₜ[k] b)) = seriesTensorPair (k := k) (H.comul (C a)) (C b) := by
    rw [hL.2.2]
    exact Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have hRa (a b : P) : R (C (a ⊗ₜ[k] b)) = seriesTensorPair (k := k) (C a) (H.comul (C b)) := by
    rw [hR.2.2]
    exact Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have hL0 : constantPart (k := k) (A := Q) (B := PlaneTensorCube k) L = TensorProduct.map (d).toLinearMap I := by
    apply TensorProduct.ext'
    intro a b
    rw [constantPart_apply, hLa, constantCoeff_pair, H.specialize_comul]
    simp
  have hR0 : constantPart (k := k) (A := Q) (B := PlaneTensorCubeRight k) R = TensorProduct.map I (d).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    rw [constantPart_apply, hRa, constantCoeff_pair, H.specialize_comul]
    simp
  have hL1 : linearPart (k := k) (A := Q) (B := PlaneTensorCube k) L = TensorProduct.map g I := by
    apply TensorProduct.ext'
    intro a b
    change coeff 1 (L (C (a ⊗ₜ[k] b))) = _
    rw [hLa, coeff_one_pair]
    simp [g, firstOrderPlaneComul, onSeriesConstants, restrictSeriesMap, seriesConstants]
  have hR1 : linearPart (k := k) (A := Q) (B := PlaneTensorCubeRight k) R = TensorProduct.map I g := by
    apply TensorProduct.ext'
    intro a b
    change coeff 1 (R (C (a ⊗ₜ[k] b))) = _
    rw [hRa, coeff_one_pair]
    simp [g, firstOrderPlaneComul, onSeriesConstants, restrictSeriesMap, seriesConstants]
  apply LinearMap.ext
  intro p
  let e : PlaneTensorCube k →ₐ[k] PlaneTensorCubeRight k :=
    (Algebra.TensorProduct.assoc k k k P P P).toAlgHom
  have hmap := seriesMap_coeff (k := k) (A := PlaneTensorCube k)
    (B := PlaneTensorCubeRight k) e (L (H.comul (C p))) 1
  have hp := congrArg (fun s : PowerSeries (PlaneTensorCubeRight k) => coeff 1 s) (h (C p))
  change coeff 1 (seriesMap e (L (H.comul (C p)))) = coeff 1 (R (H.comul (C p))) at hp
  rw [hmap, coeff_one_apply (k := k) (A := Q) (B := PlaneTensorCube k) L hL.1,
    coeff_one_apply (k := k) (A := Q) (B := PlaneTensorCubeRight k) R hR.1,
    hL0, hR0, hL1, hR1, H.specialize_comul, constantCoeff_C] at hp
  let a := TensorProduct.map g I ((d).toLinearMap p)
  let b := TensorProduct.map (d).toLinearMap I (g p)
  let r := TensorProduct.map I g ((d).toLinearMap p)
  let t := TensorProduct.map I (d).toLinearMap (g p)
  have hp' : (TensorProduct.assoc k P P P) (a + b) = r + t := hp
  change (TensorProduct.assoc k P P P) (b + a) - t - r = 0
  rw [add_comm b a, hp']
  abel


local instance : Bialgebra k P := primitivePlaneBialgebra

local notation "m" => mulTensor k P

omit [CharZero k] in
private theorem square_mul (a b : Q) :
    (TensorProduct.map m m) (middleFlip k P (a ⊗ₜ[k] b)) = a * b := by
  have h : (TensorProduct.map m m).comp (middleFlip k P) =
      TensorProduct.lift (LinearMap.mul k Q) := by
    apply TensorProduct.ext_fourfold'
    intro a₁ a₂ b₁ b₂
    simp [middleFlip, TensorProduct.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
  exact DFunLike.congr_fun h _

private theorem plane_linearized (H : CompletedPlaneHopf k) : Linearized 0 (firstOrderPlaneComul H) := by
  let g := firstOrderPlaneComul H
  refine ⟨by simp, by simp, by simp, ?_, coeff_counit_left H,
    coeff_counit_right H, by simp, coeff_coassoc H, ?_⟩
  · change coeff 1 (H.comul (C (1 : P))) = 0
    simp
  · apply TensorProduct.ext'
    intro a b
    simp only [map_zero, zero_add, LinearMap.add_apply, LinearMap.zero_apply, LinearMap.comp_apply,
      TensorProduct.map_tmul, TensorProduct.map_zero_left, TensorProduct.map_zero_right, map_add]
    change g (a * b) = _
    rw [square_mul, square_mul]
    change coeff 1 (H.comul (C (a * b))) = g a * d b + d a * g b
    rw [map_mul, map_mul, coeff_one_mul, H.specialize_comul, H.specialize_comul,
      constantCoeff_C, constantCoeff_C]
    change g a * d b + g b * d a = _
    rw [mul_comm (g b) (d a)]

omit [CharZero k] in
private theorem trivial_linearized : Linearized (k := k) (B := P) 0 0 := by
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_, by simp⟩
  apply LinearMap.ext
  intro p
  simp

private def planeCoordinate (i : Fin 2) : P →ₗ[k] k :=
  MvPolynomial.lcoeff k (Finsupp.single i 1)

omit [CharZero k] in
private theorem planeCoordinate_X (i j : Fin 2) :
    planeCoordinate (k := k) i (MvPolynomial.X j) = if i = j then 1 else 0 := by
  change (MvPolynomial.X j : P).coeff (Finsupp.single i 1) = _
  rw [MvPolynomial.coeff_X]
  simp [Finsupp.single_eq_single_iff, eq_comm]

private theorem skew_plane_tensor_ne_zero :
    (planeX (k := k) ⊗ₜ[k] planeY (k := k)) - (planeY (k := k) ⊗ₜ[k] planeX (k := k)) ≠ 0 := by
  let L := (TensorProduct.lid k k).toLinearMap.comp
    (TensorProduct.map (planeCoordinate (k := k) 0) (planeCoordinate (k := k) 1))
  intro h
  have hk := congrArg L h
  simp [L, planeCoordinate_X] at hk

omit [CharZero k] in
private theorem flip_tensorDerivative (u : P →ₗ[k] P) :
    (TensorProduct.comm k P P).toLinearMap.comp (tensorDerivative u) =
      (tensorDerivative u).comp (TensorProduct.comm k P P).toLinearMap := by
  apply TensorProduct.ext'
  intro a b
  simp [tensorDerivative, add_comm]

private theorem gauge_not_trivial (H : CompletedPlaneHopf k)
    (deformation trivial : Deformation k P) (hg : deformation.g = firstOrderPlaneComul H)
    (hz : trivial.g = 0) : ¬ Equivalent deformation trivial := by
  intro h
  obtain ⟨u, _, _, hu⟩ := (equivalent_iff deformation trivial).mp h
  rw [hz, hg] at hu
  let T := (TensorProduct.comm k P P).toLinearMap
  have hflip (a : P) : T (d a) = d a :=
    AlgHom.congr_fun H.primitive_cocommutative a
  have hcomm (a : P) : T (tensorDerivative u (d a)) = tensorDerivative u (d a) := by
    change (T.comp (tensorDerivative u)) (d a) = _
    rw [flip_tensorDerivative]
    change tensorDerivative u (T (d a)) = _
    rw [hflip]
  have hy : (planeX : P) ⊗ₜ[k] planeY + d (u planeY) - tensorDerivative u (d planeY) = 0 := by
    have hh := DFunLike.congr_fun hu (planeY : P)
    change 0 = firstOrderPlaneComul H planeY + d (u planeY) - tensorDerivative u (d planeY) at hh
    rw [coeff_plane_y] at hh
    exact hh.symm
  have hTy := congrArg T hy
  rw [map_sub, map_add, map_zero, hflip, hcomm] at hTy
  change (planeY : P) ⊗ₜ[k] planeX + d (u planeY) - tensorDerivative u (d planeY) = 0 at hTy
  apply skew_plane_tensor_ne_zero (k := k)
  linear_combination (norm := abel) hy - hTy

local notation "V" => PrimitiveDegreeOne k
local notation "e" => (primitiveDegreeOneGenerator (k := k))

private def subCoordinate (i : Fin 2) : V →ₗ[k] k :=
  (planeCoordinate i).comp (V).subtype

@[simp] private theorem subCoordinate_generator (i j : Fin 2) :
    subCoordinate (k := k) i (e j) = if i = j then 1 else 0 :=
  planeCoordinate_X i j

private theorem primitive_coordinates (v : V) :
    v = subCoordinate 0 v • e 0 + subCoordinate 1 v • e 1 := by
  obtain ⟨v, hv⟩ := v
  apply Subtype.ext
  change v = planeCoordinate 0 v • planeX + planeCoordinate 1 v • planeY
  induction hv using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    fin_cases i <;> simp [planeCoordinate_X, planeX, planeY]
  | zero => simp
  | add p q _ _ hp hq =>
    simp only [map_add, add_smul]
    nth_rw 1 [hp, hq]
    abel
  | smul a p _ hp =>
    simp only [map_smul, smul_eq_mul, mul_smul, ← smul_add]
    rw [← hp]

private theorem primitive_basis :
    ∃ b : Module.Basis (Fin 2) k V, ∀ i, b i = e i := by
  have hi : LinearIndependent k e := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    have h := congrArg (subCoordinate (k := k) i) hf
    fin_cases i <;> simpa [Fin.sum_univ_two] using h
  have hs : ⊤ ≤ Submodule.span k (Set.range e) := by
    intro p _
    rw [primitive_coordinates p]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  exact ⟨Module.Basis.mk hi hs, Module.Basis.mk_apply _ _⟩

private theorem primitive_span_points (v : V) :
    d (v : P) = (v : P) ⊗ₜ[k] 1 + 1 ⊗ₜ[k] (v : P) := by
  let L : P →ₗ[k] Q := (TensorProduct.mk k P P).flip 1 + TensorProduct.mk k P P 1
  change (d).toLinearMap ((V).subtype v) = L ((V).subtype v)
  rw [primitive_coordinates v]
  simp only [map_add, map_smul]
  have hh (i : Fin 2) : (d).toLinearMap ((V).subtype (e i)) = L ((V).subtype (e i)) :=
    MvPolynomial.aeval_X _ _
  rw [hh 0, hh 1]

private def planeCobracket : V →ₗ[k] ⋀[k]^2 V :=
  (subCoordinate (k := k) 1).smulRight (wedge₂ (e 0) (e 1))

omit [CharZero k] in
private theorem planeCobracket_apply (v : V) :
    planeCobracket v = subCoordinate 1 v • wedge₂ (e 0) (e 1) := rfl

private theorem planeCobracket_lie :
    Specs.LieNotes.Coboundary.isLieBialgebraCobracketValue (planeCobracket (k := k)) := by
  change isLieBialgebraCobracket (planeCobracket (k := k))
  constructor
  · intro x y
    have h (u w : V) : ⁅u,w⁆ = 0 := rfl
    simp [h, planeCobracket_apply, exteriorAdjoint_wedge₂]
  · intro α β γ
    have h (a b : Module.Dual k V) (v : V) :
        dualBracket planeCobracket a b v =
          subCoordinate 1 v * (a (e 0) * b (e 1) - a (e 1) * b (e 0)) := by
      rw [dualBracket_apply, ← wedge₂_apply, planeCobracket_apply, map_smul,
        pairing_wedge₂_wedge₂, smul_eq_mul]
    apply LinearMap.ext
    intro v
    simp only [LinearMap.add_apply, LinearMap.zero_apply, h, subCoordinate_generator]
    simp
    ring

private theorem planeCobracket_skew (H : CompletedPlaneHopf k) (v : V) :
    TensorProduct.map (V).subtype (V).subtype
      (Specs.LieNotes.Coboundary.alternatingTensorValue (planeCobracket v)) =
      firstOrderPlaneComul H (v : P) -
        (TensorProduct.comm k P P) (firstOrderPlaneComul H (v : P)) := by
  let L := (TensorProduct.map (V).subtype (V).subtype).comp
    (alternatingTensor.comp planeCobracket)
  let g := firstOrderPlaneComul H
  let R := (g - (TensorProduct.comm k P P).toLinearMap.comp g).comp (V).subtype
  change L v = R v
  have h0 : L (e 0) = R (e 0) := by
    have hg : g ((e 0 : V) : P) = 0 := coeff_plane_x H
    simp [L, R, planeCobracket_apply, hg]
  have h1 : L (e 1) = R (e 1) := by
    have hx : (V).subtype (e 0) = planeX := rfl
    have hy : (V).subtype (e 1) = planeY := rfl
    have hg : firstOrderPlaneComul H ((e 1 : V) : P) = planeX ⊗ₜ[k] planeY := coeff_plane_y H
    simp [L, R, planeCobracket_apply, hg, hx, hy, g]
  calc
    L v = L (subCoordinate 0 v • e 0 + subCoordinate 1 v • e 1) :=
      congrArg L (primitive_coordinates v)
    _ = R (subCoordinate 0 v • e 0 + subCoordinate 1 v • e 1) := by
      simp only [map_add, map_smul, h0, h1]
    _ = R v := congrArg R (primitive_coordinates v).symm

end Plane

set_option maxHeartbeats 800000 in
/-- The skew-primitive Hopf deformation has nonzero normalized first-order class,
and its skew coproduct on the primitive degree-one space is the stated Lie cobracket. -/
theorem nontrivialPolynomial : Expected.nontrivialPolynomial := by
  intro k _ _
  obtain ⟨H⟩ := completedPlaneHopf k
  refine ⟨H, ?_, completed_counit_firstOrder H, coeff_plane_x H, coeff_plane_y H,
    ?_, primitive_basis, primitive_span_points, ?_⟩
  · intro p
    exact firstOrderSeries_map (k := k) (A := Plane k) (B := PlaneTensorSquare k)
      H.comul H.comul_continuous primitivePlaneComul.toLinearMap H.specialize_comul p
  · letI : Bialgebra k (Plane k) := primitivePlaneBialgebra
    let D₁ : Deformation k (Plane k) :=
      ⟨0, firstOrderPlaneComul H, (laws_iff _ _).mpr (plane_linearized H)⟩
    let D₀ : Deformation k (Plane k) := ⟨0, 0, (laws_iff _ _).mpr trivial_linearized⟩
    exact ⟨primitivePlaneBialgebra, rfl, fun _ => ⟨HEq.rfl, rfl⟩, D₁, D₀,
      rfl, HEq.rfl, rfl, rfl, gauge_not_trivial H D₁ D₀ rfl rfl⟩
  · refine ⟨planeCobracket, ?_, ?_, planeCobracket_lie, planeCobracket_skew H⟩
    · simp [planeCobracket_apply]
    · change planeCobracket (primitiveDegreeOneGenerator 1) =
        wedge₂ (primitiveDegreeOneGenerator 0) (primitiveDegreeOneGenerator 1)
      simp [planeCobracket_apply]

end

end LieNotes.BialgebraDeformation
