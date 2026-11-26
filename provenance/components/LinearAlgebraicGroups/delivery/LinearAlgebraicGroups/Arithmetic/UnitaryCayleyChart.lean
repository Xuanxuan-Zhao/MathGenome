import Specs.LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart
import LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators
import LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate
import MathGenome.Internal.D05.M13.UnitarySpectrum.Cayley
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.Abel
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart

open scoped TensorProduct Polynomial
open SymplecticIsometryDescent (Involution)
open UnitaryNormEquations (SecondKind)

universe u v w

section Chart

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  (s : Involution R A)

private theorem adjoint_eq_inverse (g : s.isometries) :
    s.toLinearMap (g.val : A) = (g.val⁻¹ : Aˣ).val :=
  (Units.mul_left_inj g.val).mp (g.property.trans g.val.inv_val.symm)

private theorem adjoint_inverse (w : Aˣ) :
    s.toLinearMap (w⁻¹ : Aˣ).val * s.toLinearMap (w : A) = 1 := by
  rw [← s.map_mul, w.mul_inv, s.map_one]

private def toParameters (g : CayleyOpen s) : CayleyParameters s := by
  let w := g.property.unit
  have hw : (w : A) = 1 - g.val.val.val := g.property.unit_spec
  refine ⟨w⁻¹, ?_⟩
  have hs : s.toLinearMap (w : A) = -(w : A) * (g.val⁻¹ : Aˣ).val := by
    rw [hw, map_sub, s.map_one, adjoint_eq_inverse, neg_sub, sub_mul, g.val.val.mul_inv, one_mul]
  have hprod : (1 - (w⁻¹ : Aˣ).val) * s.toLinearMap (w : A) = 1 := by
    rw [hs, ← mul_assoc, mul_neg, sub_mul, one_mul, w.inv_mul, hw]
    rw [sub_sub_cancel_left, neg_neg, g.val.val.mul_inv]
  have hi : s.toLinearMap (w⁻¹ : Aˣ).val = 1 - (w⁻¹ : Aˣ).val := by
    calc
      s.toLinearMap (w⁻¹ : Aˣ).val =
          ((1 - (w⁻¹ : Aˣ).val) * s.toLinearMap (w : A)) *
            s.toLinearMap (w⁻¹ : Aˣ).val := by rw [hprod, one_mul]
      _ = 1 - (w⁻¹ : Aˣ).val := by
        rw [mul_assoc, ← s.map_mul, w.inv_mul, s.map_one, mul_one]
  rw [hi]
  abel

private theorem toParameters_inverse (g : CayleyOpen s) :
    ((toParameters s g).val⁻¹).val = 1 - g.val.val.val := by
  change (g.property.unit⁻¹⁻¹ : Aˣ).val = _
  rw [inv_inv]
  exact g.property.unit_spec

private def fromParameters (y : CayleyParameters s) : CayleyOpen s := by
  let w := y.val
  let b := (w⁻¹ : Aˣ).val
  let c := s.toLinearMap b
  have hy : s.toLinearMap (w : A) = 1 - w.val := by
    have h := y.property
    change w.val + s.toLinearMap w.val = 1 at h
    rw [← h]
    abel
  have hcb : c * (1 - w.val) = 1 := by
    rw [← hy]
    exact adjoint_inverse s w
  have hbc : (1 - w.val) * c = 1 := by
    rw [← hy]
    change s.toLinearMap w.val * s.toLinearMap (w⁻¹ : Aˣ).val = 1
    rw [← s.map_mul, w.inv_mul, s.map_one]
  have h₁ : (1 - c) * (1 - b) = 1 := by
    have hc : c - c * w.val = 1 := by simpa only [mul_sub, mul_one] using hcb
    have h : c * w.val * b = c := by
      rw [mul_assoc, show w.val * b = 1 from w.mul_inv, mul_one]
    have hb := congrArg (fun t : A => t * b) hc
    rw [sub_mul, h, one_mul] at hb
    rw [sub_mul, one_mul, mul_sub, mul_one, sub_eq_iff_eq_add.mp hb]
    abel
  have h₂ : (1 - b) * (1 - c) = 1 := by
    have hc : c - w.val * c = 1 := by simpa only [sub_mul, one_mul] using hbc
    have h : b * (w.val * c) = c := by
      rw [← mul_assoc, show b * w.val = 1 from w.inv_mul, one_mul]
    have hb := congrArg (fun t : A => b * t) hc
    rw [mul_sub, h, mul_one] at hb
    rw [mul_sub, mul_one, sub_mul, one_mul, sub_eq_iff_eq_add.mp hb]
    abel
  let g : Aˣ := ⟨1 - b, 1 - c, h₂, h₁⟩
  refine ⟨⟨g, ?_⟩, ?_⟩
  · change s.toLinearMap (1 - b) * (1 - b) = 1
    rw [map_sub, s.map_one]
    exact h₁
  · change IsUnit (1 - (1 - b))
    simpa only [sub_sub_cancel] using (w⁻¹).isUnit

private theorem fromParameters_value (y : CayleyParameters s) :
    (fromParameters s y).val.val.val = 1 - (y.val⁻¹).val := rfl

/-- The change of coordinates on the open isometry functor. -/
def cayleyEquiv : CayleyOpen s ≃ CayleyParameters s where
  toFun := toParameters s
  invFun := fromParameters s
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [fromParameters_value, toParameters_inverse, sub_sub_cancel]
  right_inv y := by
    apply Subtype.ext
    apply inv_injective
    apply Units.ext
    rw [toParameters_inverse, fromParameters_value, sub_sub_cancel]

theorem chart : Spec.Chart.{u} :=
  fun s => ⟨cayleyEquiv s, toParameters_inverse s, fromParameters_value s⟩

theorem naturalChart : Spec.NaturalChart.{u} := by
  intro R S A B _ _ _ _ _ _ s t f hf
  refine ⟨cayleyEquiv s, cayleyEquiv t, toParameters_inverse s, toParameters_inverse t, ?_⟩
  intro g g' h
  have hg : g'.val.val.val = f g.val.val.val :=
    congrArg (fun v : t.isometries => v.val.val) h
  apply inv_injective
  apply Units.ext
  change ((toParameters t g').val⁻¹).val = ((Units.map f.toMonoidHom (toParameters s g).val)⁻¹).val
  rw [← map_inv, Units.coe_map, toParameters_inverse, toParameters_inverse, hg]
  change 1 - f g.val.val.val = f (1 - g.val.val.val)
  rw [map_sub, map_one]

theorem quotient_of_parameter (g : s.isometries) (y : CayleyParameters s)
    (h : IsUnit ((1 - g.val.val) * y.val.val + g.val.val)) :
    ∃ a b : CayleyOpen s, a.val / b.val = g := by
  let b := fromParameters s y
  have hb : b.val.val.val = 1 - (y.val⁻¹).val := fromParameters_value s y
  have hrel : (1 - g.val.val * b.val.val.val) * y.val.val =
      (1 - g.val.val) * y.val.val + g.val.val := by
    rw [hb, mul_sub, mul_one, sub_sub_eq_add_sub, add_sub_right_comm, add_mul, mul_assoc _ ((y.val⁻¹).val),
      y.val.inv_mul, mul_one]
  have hu : IsUnit (1 - (g * b.val).val.val) := by
    have hm := h.mul (y.val⁻¹).isUnit
    rw [← hrel, mul_assoc, y.val.mul_inv, mul_one] at hm
    exact hm
  exact ⟨⟨g * b.val, hu⟩, b, mul_div_cancel_right g _⟩

end Chart

section TraceOne

theorem unitaryTraceOne : Spec.UnitaryTraceOne.{u} := by
  intro F E A _ _ _ _ _ _ _ _ _ _ s
  classical
  have hs : Function.Involutive s.conjugation := by
    intro e
    apply (algebraMap E A).injective
    rw [← s.adjoint_centre, ← s.adjoint_centre, s.adjoint_adjoint]
  obtain ⟨a, ha⟩ : ∃ a : E, s.conjugation a ≠ a := by
    by_contra! h
    exact s.conjugation_ne (AlgEquiv.ext h)
  have hex : ∃ e : E, e + s.conjugation e = 1 := by
    by_cases htwo : (2 : E) = 0
    · let d := a + s.conjugation a
      have hd : d ≠ 0 := by
        intro h
        apply ha
        have hh : a + a = 0 := by simpa only [two_mul, zero_mul] using congrArg (fun r : E => r * a) htwo
        exact add_left_cancel (h.trans hh.symm)
      have hfix : s.conjugation d = d := by
        change s.conjugation (a + s.conjugation a) = _
        rw [map_add, hs, add_comm]
      exact ⟨a / d, by rw [map_div₀, hfix, ← add_div, div_self hd]⟩
    · exact ⟨(2 : E)⁻¹, by rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ htwo]⟩
  obtain ⟨e, he⟩ := hex
  have heu : IsUnit (algebraMap E A e) := by
    apply IsUnit.map
    rw [isUnit_iff_ne_zero]
    intro h
    rw [h, map_zero, add_zero] at he
    exact zero_ne_one he
  refine ⟨heu.unit, ?_⟩
  rw [heu.unit_spec, s.adjoint_centre, ← map_add, he, map_one]

theorem unitaryChartNonempty : Spec.UnitaryChartNonempty.{u} := by
  intro F E A _ _ _ _ _ _ _ _ _ _ s
  obtain ⟨z, hz⟩ := unitaryTraceOne s
  exact ⟨fromParameters (groundInvolution s) ⟨z, hz⟩⟩

end TraceOne

section Polynomial

variable {F A L : Type u} [Field F] [Ring A] [Algebra F A]
  [Field L] [Algebra F L]

private abbrev traceKernel (s : Involution F A) :=
  LinearMap.ker (LinearMap.id + s.toLinearMap)

private theorem traceKernel_contains {s : Involution F A} {z : A}
    (hz : z + s.toLinearMap z = 1) (c : traceKernel s) :
    (z + c.val) + s.toLinearMap (z + c.val) = 1 := by
  have hc : c.val + s.toLinearMap c.val = 0 := c.property
  rw [map_add, add_add_add_comm, hz, hc, add_zero]

private theorem traceKernel_baseChange {R : Type u} [CommRing R] [Algebra F R]
    (s : Involution F A) (z : A)
    (hz : z + s.toLinearMap z = 1) (y : R ⊗[F] A)
    (hy : y + (s.baseChange R).toLinearMap y = 1) :
    ∃ a : R ⊗[F] traceKernel s,
      y = 1 ⊗ₜ[F] z + (traceKernel s).subtype.baseChange R a := by
  let d : A →ₗ[F] A := LinearMap.id + s.toLinearMap
  have he : Function.Exact (LinearMap.ker d).subtype d := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have hmap : d.baseChange R = LinearMap.id + (s.baseChange R).toLinearMap := by
    ext r
    simp [d, Involution.baseChange_tmul]
  have hx : d.lTensor R (y - 1 ⊗ₜ[F] z) = 0 := by
    change d.baseChange R _ = 0
    rw [map_sub, LinearMap.baseChange_tmul, hmap]
    change y + (s.baseChange R).toLinearMap y - (1 : R) ⊗ₜ[F] (z + s.toLinearMap z) = 0
    rw [hy, hz, ← Algebra.TensorProduct.one_def, sub_self]
  obtain ⟨a, ha⟩ := (Module.Flat.lTensor_exact R he _).mp hx
  refine ⟨a, ?_⟩
  change (traceKernel s).subtype.baseChange R a = _ at ha
  rw [ha]
  abel

private theorem leftMulMatrix_isUnit {R B ι : Type*} [CommRing R] [Ring B]
    [Algebra R B] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R B) (a : B) :
    IsUnit (Algebra.leftMulMatrix b a) ↔ IsUnit a := by
  change IsUnit (LinearMap.toMatrixAlgEquiv b (Algebra.lmul R B a)) ↔ _
  exact (isUnit_map_iff (LinearMap.toMatrixAlgEquiv b) _).trans Algebra.lmul_isUnit_iff

set_option maxHeartbeats 800000 in
theorem affineParameterSpace : Spec.AffineParameterSpace.{u} := by
  intro F A _ _ _ _ s z hz R _ _ V b
  let f := V.subtype.baseChange R
  let d : A →ₗ[F] A := LinearMap.id + s.toLinearMap
  have hd : d.baseChange R = LinearMap.id + (s.baseChange R).toLinearMap := by
    ext x
    simp [d, Involution.baseChange_tmul]
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap V.subtype Subtype.val_injective
  have he (x : R ⊗[F] V) :
      (1 : R) ⊗ₜ[F] z + f x + (s.baseChange R).toLinearMap ((1 : R) ⊗ₜ[F] z + f x) = 1 := by
    have hzero : d.baseChange R (f x) = 0 := by
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
        change d.baseChange R (V.subtype.baseChange R (r ⊗ₜ[F] a)) = 0
        simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
          show d a.val = 0 from a.property, TensorProduct.tmul_zero]
      | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    rw [hd] at hzero
    change f x + (s.baseChange R).toLinearMap (f x) = 0 at hzero
    rw [map_add, add_add_add_comm, hzero, add_zero,
      Involution.baseChange_tmul, ← TensorProduct.tmul_add, hz, ← Algebra.TensorProduct.one_def]
  let g : (R ⊗[F] V) → {y : R ⊗[F] A // y + (s.baseChange R).toLinearMap y = 1} :=
    fun x => ⟨(1 : R) ⊗ₜ[F] z + f x, he x⟩
  let e := Equiv.ofBijective g ⟨fun x y h => hf (add_left_cancel (congrArg Subtype.val h)),
    fun y => by
      obtain ⟨x, hx⟩ := traceKernel_baseChange s z hz y.val y.property
      exact ⟨x, Subtype.ext hx.symm⟩⟩
  refine ⟨e, fun _ => rfl, fun x => ?_⟩
  exact (leftMulMatrix_isUnit b (e x).val).symm.trans (Matrix.isUnit_iff_isUnit_det _)

private theorem leftMulMatrix_tmul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F A) (a : A) :
    Algebra.leftMulMatrix (b.baseChange L) ((1 : L) ⊗ₜ[F] a) =
      (Algebra.leftMulMatrix b a).map (algebraMap F L) := by
  ext i j
  simp only [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply,
    Algebra.TensorProduct.tmul_mul_tmul, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one]

private theorem leftMulMatrix_map {R S ι : Type*} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F A) (f : R →ₐ[F] S) (x : R ⊗[F] A) :
    (Algebra.leftMulMatrix (b.baseChange R) x).map f =
      Algebra.leftMulMatrix (b.baseChange S) (Algebra.TensorProduct.map f (AlgHom.id F A) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    ext i j
    simp only [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.baseChange_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, Module.Basis.baseChange_repr_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.smul_def, map_mul, f.commutes]
  | add x y hx hy =>
    change f.toRingHom.mapMatrix (Algebra.leftMulMatrix (b.baseChange R) (x + y)) = _
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

private theorem traceKernel_coordinates {ι : Type*} [Fintype ι]
    (s : Involution F A) (c : Module.Basis ι F (traceKernel s))
    (z : A) (hz : z + s.toLinearMap z = 1) (y : L ⊗[F] A)
    (hy : y + (s.baseChange L).toLinearMap y = 1) :
    ∃ x : ι → L, (1 : L) ⊗ₜ[F] z + ∑ i, x i ⊗ₜ[F] (c i).val = y := by
  classical
  obtain ⟨a, ha⟩ := traceKernel_baseChange s z hz y hy
  refine ⟨fun i => (c.baseChange L).repr a i, ?_⟩
  conv_rhs => rw [ha]
  congr 1
  have h := congrArg ((traceKernel s).subtype.baseChange L) ((c.baseChange L).sum_repr a)
  simpa only [map_sum, map_smul, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Submodule.subtype_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

variable [Module.Finite F A]

private theorem exists_rational_parameter (s : Involution F A) [Infinite F]
    (z : A) (hz : z + s.toLinearMap z = 1) (u : A)
    (y : L ⊗[F] A) (hy : y + (s.baseChange L).toLinearMap y = 1)
    (hyu : IsUnit y) (huy : IsUnit ((1 - (1 : L) ⊗ₜ[F] u) * y + 1 ⊗ₜ[F] u)) :
    ∃ y : CayleyParameters s, IsUnit ((1 - u) * y.val.val + u) := by
  classical
  let b := Module.finBasis F A
  let I := Fin (Module.finrank F (traceKernel s))
  let c := Module.finBasis F (traceKernel s)
  let param (R : Type u) [CommRing R] [Algebra F R] (x : I → R) : R ⊗[F] A :=
    (1 : R) ⊗ₜ[F] z + ∑ i, x i ⊗ₜ[F] (c i).val
  let test (R : Type u) [CommRing R] [Algebra F R] (x : I → R) : R :=
    let Y := param R x
    let U := (1 : R) ⊗ₜ[F] u
    (Algebra.leftMulMatrix (b.baseChange R) Y).det *
      (Algebra.leftMulMatrix (b.baseChange R) ((1 - U) * Y + U)).det
  let P := test (MvPolynomial I F) MvPolynomial.X
  have hEval (R : Type u) [CommRing R] [Algebra F R] (x : I → R) :
      MvPolynomial.aeval x P = test R x := by
    let f : MvPolynomial I F →ₐ[F] R := MvPolynomial.aeval x
    let e := Algebra.TensorProduct.map f (AlgHom.id F A)
    have hU : e ((1 : MvPolynomial I F) ⊗ₜ[F] u) = (1 : R) ⊗ₜ[F] u := by
      simp [e]
    have hY : e (param (MvPolynomial I F) MvPolynomial.X) = param R x := by
      simp [e, f, param]
    change f (test (MvPolynomial I F) MvPolynomial.X) = _
    dsimp only [test]
    rw [map_mul, AlgHom.map_det, AlgHom.map_det]
    change ((Algebra.leftMulMatrix _ _).map f).det *
      ((Algebra.leftMulMatrix _ _).map f).det = _
    rw [leftMulMatrix_map, leftMulMatrix_map]
    change (Algebra.leftMulMatrix _ (e _)).det * (Algebra.leftMulMatrix _ (e _)).det = _
    simp only [map_add e, map_mul e, map_sub e, map_one e, hU, hY]
  have hreg {R : Type u} [Field R] [Algebra F R] (a : R ⊗[F] A) :
      (Algebra.leftMulMatrix (b.baseChange R) a).det ≠ 0 ↔ IsUnit a :=
    isUnit_iff_ne_zero.symm.trans ((Matrix.isUnit_iff_isUnit_det _).symm.trans
      (leftMulMatrix_isUnit _ a))
  have hP : P ≠ 0 := by
    obtain ⟨x, hx⟩ := traceKernel_coordinates s c z hz y hy
    have he := hEval L x
    have hY : param L x = y := hx
    dsimp only [test] at he
    rw [hY] at he
    intro hzero
    rw [hzero, map_zero] at he
    exact mul_ne_zero ((hreg y).mpr hyu) ((hreg _).mpr huy) he.symm
  obtain ⟨x, hx⟩ : ∃ x : I → F, MvPolynomial.eval x P ≠ 0 := by
    by_contra! h
    exact hP (MvPolynomial.funext (fun x => (h x).trans (map_zero (MvPolynomial.eval x)).symm))
  let a : traceKernel s := ∑ i, x i • c i
  let y₀ : A := z + a.val
  let e := Algebra.TensorProduct.lid F A
  have hY : e (param F x) = y₀ := by
    simp [param, e, y₀, a]
  have hU : e ((1 : F) ⊗ₜ[F] u) = u := by simp [e]
  have he := hEval F x
  change MvPolynomial.eval x P = test F x at he
  rw [he, show test F x = _ from rfl, mul_ne_zero_iff] at hx
  have hy₀ : IsUnit y₀ := hY ▸ ((hreg _).mp hx.1).map e.toMonoidHom
  refine ⟨⟨hy₀.unit, ?_⟩, ?_⟩
  · rw [hy₀.unit_spec]
    exact traceKernel_contains hz a
  · rw [hy₀.unit_spec]
    have hm := ((hreg _).mp hx.2).map e.toMonoidHom
    change IsUnit (e ((1 - (1 : F) ⊗ₜ[F] u) * param F x + 1 ⊗ₜ[F] u)) at hm
    simpa only [map_add, map_mul, map_sub, map_one, hY, hU] using hm

theorem quotientsFromExtension : Spec.QuotientsFromExtension.{u} := by
  intro F L A _ _ _ _ _ _ _ s z hz g f h
  obtain ⟨y, hy⟩ := h
  obtain ⟨p, hp⟩ := exists_rational_parameter s z hz g.val.val y.val.val y.property y.val.isUnit hy
  exact quotient_of_parameter s g p hp

end Polynomial

theorem principalOpenRationalDensity : Spec.PrincipalOpenRationalDensity.{u,v,w} := by
  classical
  intro F L ι _ _ _ _ p hp
  let f := algebraMap F L
  let q := MvPolynomial.map f p
  let point (x : {a : ι → F // MvPolynomial.eval a p ≠ 0}) :=
    PrimeSpectrum.comap (MvPolynomial.eval (f ∘ x.val)) (⟨⊥, inferInstance⟩ : PrimeSpectrum L)
  have hq : q ≠ 0 := fun h => hp ((MvPolynomial.map_injective f f.injective)
    (h.trans (map_zero (MvPolynomial.map f)).symm))
  have hI : PrimeSpectrum.vanishingIdeal (Set.range point) = ⊥ := by
    apply le_antisymm _ bot_le
    intro g hg
    rw [Ideal.mem_bot]
    have hg' (a : ι → F) (ha : MvPolynomial.eval a p ≠ 0) :
        MvPolynomial.eval (f ∘ a) g = 0 := by
      have h := (PrimeSpectrum.mem_vanishingIdeal _ _).mp hg (point ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
      exact Ideal.mem_bot.mp h
    have hprod : q * g = 0 := by
      apply MvPolynomial.funext_set (fun _ => Set.range f)
        (fun _ => Set.infinite_range_of_injective f.injective)
      intro x hx
      choose a ha using fun i => hx i (Set.mem_univ i)
      have hxa : f ∘ a = x := funext ha
      rw [← hxa, map_mul, map_zero]
      by_cases he : MvPolynomial.eval a p = 0
      · rw [show MvPolynomial.eval (f ∘ a) q = f (MvPolynomial.eval a p) by
          rw [MvPolynomial.eval_map, MvPolynomial.eval₂_comp], he, map_zero, zero_mul]
      · rw [hg' a he, mul_zero]
    exact (mul_eq_zero.mp hprod).resolve_left hq
  change DenseRange point
  rw [DenseRange, dense_iff_closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    hI, PrimeSpectrum.zeroLocus_bot]

section SplitSymplectic

open scoped Matrix
open LinearAlgebraicGroups.Specs.SymplecticMatrixStructure
open LinearAlgebraicGroups.Specs.SymplecticDatumAdjointDescent (adjoint MatrixAlgebra)
open private Parameters parameterPoint parameterPoint_surjective parameters_isDomain
  from LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure

variable {L I : Type u} [Field L] [Fintype I] [DecidableEq I]

private def scalarBlocks (r t : L) : MatrixAlgebra I L :=
  Matrix.fromBlocks (r • 1) 0 0 (t • 1)

private theorem scalarBlocks_mul (r s t q : L) :
    scalarBlocks (I := I) r s * scalarBlocks t q = scalarBlocks (r * t) (s * q) := by
  simp [scalarBlocks, Matrix.fromBlocks_multiply, smul_smul, mul_comm]

private theorem scalarBlocks_adjoint (r t : L) :
    adjoint (scalarBlocks (I := I) r t) = scalarBlocks t r := by
  simp [scalarBlocks, adjoint, Matrix.J, Matrix.fromBlocks_neg, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]

omit [Fintype I] in
private theorem scalarBlocks_one : scalarBlocks (I := I) (1 : L) 1 = 1 := by
  simp [scalarBlocks]

private theorem scalarBlocks_unit {r t : L} (hr : r ≠ 0) (ht : t ≠ 0) :
    IsUnit (scalarBlocks (I := I) r t) :=
  ⟨⟨scalarBlocks r t, scalarBlocks r⁻¹ t⁻¹,
    by rw [scalarBlocks_mul, mul_inv_cancel₀ hr, mul_inv_cancel₀ ht, scalarBlocks_one],
    by rw [scalarBlocks_mul, inv_mul_cancel₀ hr, inv_mul_cancel₀ ht, scalarBlocks_one]⟩, rfl⟩

private theorem split_symplectic_chart [Infinite L] :
    ∃ c : PointGroup I L, IsUnit (1 - c.val) := by
  classical
  obtain ⟨r, hr⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset L)
  have hr₀ : r ≠ 0 := fun h => hr (by simp [h])
  have hr₁ : r ≠ 1 := fun h => hr (by simp [h])
  let c := scalarBlocks (I := I) r r⁻¹
  have hc : c ∈ Matrix.symplecticGroup I L := by
    apply ((LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent.adjointIdentities I L).2.2.2.1 c).mpr
    rw [show adjoint c = scalarBlocks r⁻¹ r from scalarBlocks_adjoint r r⁻¹]
    change scalarBlocks r⁻¹ r * scalarBlocks r r⁻¹ = 1
    rw [scalarBlocks_mul, inv_mul_cancel₀ hr₀, mul_inv_cancel₀ hr₀, scalarBlocks_one]
  refine ⟨⟨c, hc⟩, ?_⟩
  have hdiff : 1 - c = scalarBlocks (I := I) (1 - r) (1 - r⁻¹) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [c, scalarBlocks, Matrix.one_apply] <;> split <;> simp_all
  rw [hdiff]
  exact scalarBlocks_unit (sub_ne_zero.mpr hr₁.symm) (sub_ne_zero.mpr (Ne.symm (by simpa using hr₁)))

/-- The two opens meet in the generic split symplectic point. The polynomial
parametrization by shears and the Levi block allows separate evaluations to
show that each determinant is nonzero. -/
private theorem split_symplectic_overlap [Infinite L] :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra L M),
      ∀ g : PointGroup I L, ∃ v : PointGroup I M,
        IsUnit (1 - v.val) ∧ IsUnit (1 - (g.val.map (algebraMap L M)) * v.val) := by
  classical
  let P := Parameters L I
  let : IsDomain P := parameters_isDomain
  let M := FractionRing P
  let v : PointGroup I P := parameterPoint
  obtain ⟨c, hc⟩ := split_symplectic_chart (I := I) (L := L)
  have hne (g : PointGroup I L) : (1 - g.val.map (algebraMap L P) * v.val).det ≠ 0 := by
    obtain ⟨e, he⟩ := parameterPoint_surjective (k := L) (ι := I) (g⁻¹ * c)
    have hh : v.val.map e = (g⁻¹ * c).val := congrArg Subtype.val he
    have h : e ((1 - g.val.map (algebraMap L P) * v.val).det) = (1 - c.val).det := by
      rw [AlgHom.map_det]
      change (e.toRingHom.mapMatrix (1 - g.val.map (algebraMap L P) * v.val)).det = _
      rw [map_sub, map_one, map_mul]
      change (1 - (g.val.map (algebraMap L P)).map e * v.val.map e).det = _
      have hg : (g.val.map (algebraMap L P)).map e = g.val := by
        ext i j
        exact e.commutes (g.val i j)
      rw [hh, hg]
      change (1 - (g * (g⁻¹ * c)).val).det = _
      rw [mul_inv_cancel_left]
    intro hzero
    rw [hzero, map_zero] at h
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hc).ne_zero h.symm
  refine ⟨M, inferInstance, inferInstance, fun g => ⟨mapSymplecticPoint (algebraMap P M) v, ?_, ?_⟩⟩
  · have h := hne (1 : PointGroup I L)
    have hd : (1 - v.val).det ≠ 0 := by
      simpa [Matrix.map_one _ (map_zero _) (map_one _)] using h
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [isUnit_iff_ne_zero]
    change (1 - (algebraMap P M).mapMatrix v.val).det ≠ 0
    rw [← map_one ((algebraMap P M).mapMatrix), ← map_sub ((algebraMap P M).mapMatrix),
      ← RingHom.map_det]
    exact fun h => hd ((IsFractionRing.injective P M) (h.trans (map_zero _).symm))
  · apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [isUnit_iff_ne_zero]
    change (1 - g.val.map (algebraMap L M) * v.val.map (algebraMap P M)).det ≠ 0
    have hg : g.val.map (algebraMap L M) = (g.val.map (algebraMap L P)).map (algebraMap P M) := by
      ext i j
      exact IsScalarTower.algebraMap_apply L P M (g.val i j)
    rw [hg]
    change (1 - (algebraMap P M).mapMatrix (g.val.map (algebraMap L P)) *
      (algebraMap P M).mapMatrix v.val).det ≠ 0
    rw [← map_mul, ← map_one ((algebraMap P M).mapMatrix), ← map_sub ((algebraMap P M).mapMatrix),
      ← RingHom.map_det]
    exact fun h => hne g ((IsFractionRing.injective P M) (h.trans (map_zero _).symm))

end SplitSymplectic

section SplitCentre

open MulOpposite
open UnitaryNormEquations (adjointAt)

variable {R F C B : Type u} [CommRing R] [Ring C] [Algebra R C] [Ring B]

private def firstProjection (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution R C) :
    s.isometries →* Bˣ :=
  (Units.map (((RingHom.fst B Bᵐᵒᵖ).comp e.toRingHom).toMonoidHom)).comp s.isometries.subtype

private theorem firstProjection_pair (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution R C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1))
    (g : s.isometries) :
    e g.val.val = ((firstProjection e s g).val, op ((firstProjection e s g)⁻¹).val) := by
  have hh := congrArg Prod.fst (he g.val.val)
  rw [adjoint_eq_inverse] at hh
  exact Prod.ext rfl ((congrArg op hh).trans (op_unop _)).symm

private def splitCentreIsometry (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution R C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1)) (b : Bˣ) :
    s.isometries := by
  let w : (B × Bᵐᵒᵖ)ˣ := ⟨(b.val, op (b⁻¹).val), ((b⁻¹).val, op b.val),
    Prod.ext b.mul_inv (congrArg op b.mul_inv),
    Prod.ext b.inv_mul (congrArg op b.inv_mul)⟩
  let v := Units.map e.symm.toMonoidHom w
  have hv : e v.val = (b.val, op (b⁻¹).val) := e.apply_symm_apply _
  refine ⟨v, ?_⟩
  change s.toLinearMap v.val * v.val = 1
  apply e.injective
  rw [map_mul, map_one, he, hv, unop_op]
  exact Prod.ext b.inv_mul (congrArg op b.inv_mul)

private theorem firstProjection_surjective (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution R C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1)) :
    Function.Surjective (firstProjection e s) := by
  intro b
  refine ⟨splitCentreIsometry e s he b, Units.ext ?_⟩
  exact congrArg Prod.fst (e.apply_symm_apply (b.val, op (b⁻¹).val))

private theorem firstProjection_isUnit_sub (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution R C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1))
    (g : s.isometries) (hu : IsUnit (1 - (firstProjection e s g).val)) :
    IsUnit (1 - g.val.val) := by
  apply (isUnit_map_iff e _).mp
  rw [map_sub, map_one, firstProjection_pair e s he]
  let w := firstProjection e s g
  change IsUnit ((1 - w.val, 1 - op (w⁻¹).val) : B × Bᵐᵒᵖ)
  have hw : 1 - (w⁻¹).val = -(1 - w.val) * (w⁻¹).val := by
    rw [neg_sub, sub_mul, w.mul_inv, one_mul]
  exact Prod.isUnit_iff.mpr ⟨hu, (show IsUnit (1 - (w⁻¹).val) by
    rw [hw]
    exact hu.neg.mul (w⁻¹).isUnit).op⟩

private theorem scalar_avoids_unit_roots {L : Type u} [Field L] [Infinite L]
    [Algebra L B] [Module.Finite L B] (a : B) :
    ∃ r : L, r ≠ 0 ∧ r ≠ 1 ∧ IsUnit (1 - r • a) := by
  classical
  let b := Module.finBasis L B
  let m := Algebra.leftMulMatrix b
  let X : L[X] := Polynomial.X
  let q := (1 - X • (m a).map Polynomial.C).det
  have hEval (r : L) : q.eval r = (m (1 - r • a)).det := by
    let f := Polynomial.evalRingHom r
    change f ((1 - X • (m a).map Polynomial.C).det) = _
    rw [RingHom.map_det]
    congr 1
    rw [map_sub m, map_one m, map_smul m]
    ext i j
    simp [f, X, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
    rw [mul_comm (m a i j) r]
    congr 1
    split <;> simp
  have hq : q ≠ 0 := by
    have h := hEval 0
    simp only [zero_smul, sub_zero, map_one, Matrix.det_one] at h
    intro hzero
    simp [hzero] at h
  have hp : X * (X - 1) * q ≠ 0 :=
    mul_ne_zero (mul_ne_zero Polynomial.X_ne_zero
      (by simpa using Polynomial.X_sub_C_ne_zero (1 : L))) hq
  obtain ⟨r, hr⟩ : ∃ r, (X * (X - 1) * q).eval r ≠ 0 := by
    by_contra! h
    exact hp (Polynomial.funext (fun r => by simpa using h r))
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, X, Polynomial.eval_X,
    Polynomial.eval_one, mul_ne_zero_iff] at hr
  refine ⟨r, hr.1.1, sub_ne_zero.mp hr.1.2, (leftMulMatrix_isUnit b (1 - r • a)).mp ?_⟩
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero, ← hEval]
  exact hr.2

private theorem splitCentre_overlap [Field F] [Infinite F] [Algebra F B] [Module.Finite F B]
    (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution R C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1))
    (g : s.isometries) :
    ∃ v : s.isometries, IsUnit (1 - v.val.val) ∧ IsUnit (1 - (g * v).val.val) := by
  let π := firstProjection e s
  obtain ⟨r, hr₀, hr₁, hr⟩ := scalar_avoids_unit_roots (L := F) (π g).val
  let w := Units.map (algebraMap F B).toMonoidHom (Units.mk0 r hr₀)
  obtain ⟨v, hv⟩ := firstProjection_surjective e s he w
  change π v = w at hv
  refine ⟨v, firstProjection_isUnit_sub e s he v ?_, firstProjection_isUnit_sub e s he (g*v) ?_⟩
  · change IsUnit (1 - (π v).val)
    rw [hv]
    change IsUnit (1 - algebraMap F B r)
    rw [← map_one (algebraMap F B), ← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hr₁.symm)).map (algebraMap F B)
  · change IsUnit (1 - (π (g*v)).val)
    rw [map_mul, hv, Units.val_mul]
    change IsUnit (1 - (π g).val * algebraMap F B r)
    rwa [Algebra.smul_def, Algebra.commutes] at hr

private theorem groundInvolution_baseChange {k E A L : Type u} [Field k] [Field E] [Algebra k E]
    [Ring A] [Algebra k A] [Algebra E A] [CommRing L] [Algebra k L]
    (s : SecondKind k E A) (x : L ⊗[k] A) :
    ((groundInvolution s).baseChange L).toLinearMap x = adjointAt s x := by
  induction x using TensorProduct.inductionOn with
  | tmul r a => rfl
  | add x y hx hy =>
    unfold adjointAt at *
    simp only [map_add, MulOpposite.unop_add, hx, hy]

end SplitCentre

section Models

open MulOpposite
open UnitaryNormEquations (factorPair)
open private cancelTensorBaseChange cancelBaseChange_involution
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (SplitComparison standardAdjoint)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels.DivisionForms
  (toDivisionInvolution unliftHyperbolicMatrix)
open LinearAlgebraicGroups.Specs.SymplecticDatumTorusAndBorel (HyperbolicIndex)
open LinearAlgebraicGroups.Specs.SymplecticMatrixStructure (PointGroup Indices)
open LinearAlgebraicGroups.Specs.SymplecticDatumAdjointDescent (adjoint)
open _root_.Specs.RM03.CSA (isCentralSimple)
open private involutionTraceOne splitComparisonBaseChange extendAnti_involution
  unliftHyperbolicMatrix_J unliftHyperbolicMatrix_transpose
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
open private extendSplit split_comparison_all tensorTower_pure extendEquiv_tmul scalarMatrixBaseChange_tmul
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

private theorem parameter_of_overlap {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
    (s : Involution R A) (g v : s.isometries)
    (hv : IsUnit (1 - v.val.val)) (hgv : IsUnit (1 - (g * v).val.val)) :
    ∃ y : CayleyParameters s, IsUnit ((1 - g.val.val) * y.val.val + g.val.val) := by
  let w := hv.unit
  let y := toParameters s ⟨v, hv⟩
  have hw : (w : A) = 1 - v.val.val := hv.unit_spec
  have hy : (y.val : A) = (w⁻¹).val := rfl
  have hrel : (1 - g.val.val * v.val.val) * y.val.val =
      (1 - g.val.val) * y.val.val + g.val.val := by
    rw [← sub_sub_cancel 1 v.val.val, ← hw, mul_sub, mul_one, sub_sub_eq_add_sub,
      add_sub_right_comm, add_mul, hy, mul_assoc, w.mul_inv, mul_one]
  exact ⟨y, hrel ▸ hgv.mul y.val.isUnit⟩

private theorem split_adjoint {F L A : Type u} [Field F] [Field L] [Algebra F L]
    [Ring A] [Algebra F A] (s : Involution F A) {n : ℕ}
    (c : SplitComparison (toDivisionInvolution s) L n) (x : L ⊗[F] A) :
    c.equiv ((s.baseChange L).toLinearMap x) = standardAdjoint n (c.equiv x) := by
  have h := split_comparison_all c x
  rwa [extendAnti_involution] at h

private theorem unlift_adjoint (n : ℕ) (L : Type u) [Field L]
    (x : Matrix (Indices (HyperbolicIndex.{u} n)) (Indices (HyperbolicIndex.{u} n)) L) :
    unliftHyperbolicMatrix n L (adjoint x) = standardAdjoint n (unliftHyperbolicMatrix n L x) := by
  rw [adjoint, standardAdjoint, map_mul, map_mul, map_neg, unliftHyperbolicMatrix_J,
    unliftHyperbolicMatrix_transpose]

private def pointsToSplitting {F L A : Type u} [Field F] [Field L] [Algebra F L]
    [Ring A] [Algebra F A] (s : Involution F A) {n : ℕ}
    (c : SplitComparison (toDivisionInvolution s) L n)
    (g : (s.baseChange L).isometries) :
    PointGroup (HyperbolicIndex.{u} n) L := by
  let q := unliftHyperbolicMatrix n L
  refine ⟨q.symm (c.equiv g.val.val), ?_⟩
  apply ((LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent.adjointIdentities _ _).2.2.2.1 _).mpr
  apply q.injective
  rw [map_mul, unlift_adjoint, q.apply_symm_apply, map_one, ← split_adjoint s c, ← map_mul]
  exact (congrArg c.equiv g.property).trans c.equiv.map_one

private def pointsFromSplitting {F L A : Type u} [Field F] [Field L] [Algebra F L]
    [Ring A] [Algebra F A] (s : Involution F A) {n : ℕ}
    (c : SplitComparison (toDivisionInvolution s) L n)
    (g : PointGroup (HyperbolicIndex.{u} n) L) :
    (s.baseChange L).isometries := by
  let q := unliftHyperbolicMatrix n L
  let e := q.trans c.equiv.symm
  let u := Units.map e.toMonoidHom (show (Matrix _ _ L)ˣ from
    ⟨g.val, g⁻¹.val, by exact congrArg Subtype.val (mul_inv_cancel g),
      by exact congrArg Subtype.val (inv_mul_cancel g)⟩)
  refine ⟨u, ?_⟩
  change (s.baseChange L).toLinearMap (c.equiv.symm (q g.val)) *
    (c.equiv.symm (q g.val)) = 1
  apply c.equiv.injective
  rw [map_mul, split_adjoint, c.equiv.apply_symm_apply, map_one, ← unlift_adjoint, ← map_mul]
  rw [((LinearAlgebraicGroups.RootData.SymplecticDatumAdjointDescent.adjointIdentities _ _).2.2.2.1 _).mp
    g.property, map_one]

theorem symplecticQuotients : Spec.SymplecticQuotients.{u} := by
  intro F L A _ _ _ _ _ _ _ s n c
  classical
  let : Infinite L := Infinite.of_injective (algebraMap F L) (algebraMap F L).injective
  obtain ⟨z, hz⟩ := involutionTraceOne s c
  let I := HyperbolicIndex.{u} n
  obtain ⟨M, fM, algM, hov⟩ := split_symplectic_overlap (I := I) (L := L)
  let : Algebra F M := ((algebraMap L M).comp (algebraMap F L)).toAlgebra
  let : IsScalarTower F L M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let cM : SplitComparison (toDivisionInvolution s) M n := extendSplit c
  intro g
  let gL := pointsToSplitting s c (isometryExtension (F := L) s g)
  obtain ⟨vM, hvM, hgvM⟩ := hov gL
  let v := pointsFromSplitting s cM vM
  let gM := isometryExtension (F := M) s g
  let q := unliftHyperbolicMatrix n M
  have hV : cM.equiv v.val.val = q vM.val := cM.equiv.apply_symm_apply _
  have hG : cM.equiv gM.val.val = q (gL.val.map (algebraMap L M)) := by
    change cM.equiv (1 ⊗ₜ[F] g.val.val) =
      q (((unliftHyperbolicMatrix n L).symm (c.equiv (1 ⊗ₜ[F] g.val.val))).map (algebraMap L M))
    simp only [cM, extendSplit, AlgEquiv.trans_apply, tensorTower_pure, extendEquiv_tmul,
      scalarMatrixBaseChange_tmul, one_smul]
    rw [show q (((unliftHyperbolicMatrix n L).symm (c.equiv (1 ⊗ₜ[F] g.val.val))).map
      (algebraMap L M)) =
        (unliftHyperbolicMatrix n L ((unliftHyperbolicMatrix n L).symm
          (c.equiv (1 ⊗ₜ[F] g.val.val)))).map (algebraMap L M) from rfl,
      AlgEquiv.apply_symm_apply]
  have hv : IsUnit (1 - v.val.val) := by
    apply (isUnit_map_iff cM.equiv _).mp
    rw [map_sub, map_one, hV, ← map_one q, ← map_sub q]
    exact hvM.map q
  have hg : IsUnit (1 - (gM * v).val.val) := by
    apply (isUnit_map_iff cM.equiv _).mp
    change IsUnit (cM.equiv (1 - gM.val.val * v.val.val))
    rw [map_sub, map_one, map_mul, hG, hV, ← map_mul q, ← map_one q, ← map_sub q]
    exact hgvM.map q
  exact quotientsFromExtension (L := M) s z hz g (parameter_of_overlap _ gM v hv hg)

theorem unitaryQuotients : Spec.UnitaryQuotients.{u} := by
  intro k E A F _ _ _ _ _ _ _ _ _ _ _ _ hA s
  classical
  let : Module.Finite E A := hA.2.2
  let : Module.Finite k A := Module.Finite.trans E A
  let : IsSimpleRing A := hA.1
  let B := F ⊗[k] A
  let t := groundInvolution s
  let tF := t.baseChange F
  let L := AlgebraicClosure F
  let j : E →ₐ[k] L := IsAlgClosed.lift
  let : Algebra E L := j.toRingHom.toAlgebra
  let : IsScalarTower k E L := IsScalarTower.of_algHom j
  let P := L ⊗[E] A
  let b := (Module.finBasis E A).reindex
    (Equiv.ulift.symm : Fin (Module.finrank E A) ≃ ULift.{u} (Fin (Module.finrank E A)))
  obtain ⟨hpair, hswap, _⟩ := UnitaryNormEquations.splitCentreComparison (R := L) hA b s
  let e := (AlgEquiv.ofBijective (factorPair (R := L) s) hpair).toRingEquiv
  let f := cancelTensorBaseChange (k := k) (F := F) (A := A) L
  let d : (L ⊗[F] B) ≃+* P × Pᵐᵒᵖ := f.toRingEquiv.trans e
  have hd (x : L ⊗[F] B) : d ((tF.baseChange L).toLinearMap x) =
      (unop (d x).2, op (d x).1) := by
    change e (f ((tF.baseChange L).toLinearMap x)) = (unop (e (f x)).2, op (e (f x)).1)
    rw [cancelBaseChange_involution, groundInvolution_baseChange]
    exact hswap (f x)
  obtain ⟨z, hz⟩ := unitaryTraceOne s
  have hzF : (1 : F) ⊗ₜ[k] z.val + tF.toLinearMap (1 ⊗ₜ[k] z.val) = 1 := by
    rw [Involution.baseChange_tmul, ← TensorProduct.tmul_add]
    change (1 : F) ⊗ₜ[k] (z.val + unop (s.adjoint z.val)) = 1
    rw [hz, ← Algebra.TensorProduct.one_def]
  intro g
  let gL := isometryExtension (F := L) tF g
  obtain ⟨v, hv, huv⟩ := splitCentre_overlap (F := L) d (tF.baseChange L) hd gL
  exact quotientsFromExtension (L := L) tF (1 ⊗ₜ[k] z.val) hzF g
    (parameter_of_overlap _ gL v hv huv)

theorem symplecticChartNonempty : Spec.SymplecticChartNonempty.{u} := by
  intro F L A _ _ _ _ _ _ _ s n c
  obtain ⟨x, hx⟩ := split_symplectic_chart (I := HyperbolicIndex.{u} n) (L := L)
  let g := pointsFromSplitting s c x
  have hg : IsUnit (1 - g.val.val) := by
    let q := unliftHyperbolicMatrix n L
    apply (isUnit_map_iff c.equiv _).mp
    rw [map_sub, map_one, show c.equiv g.val.val = q x.val from c.equiv.apply_symm_apply _,
      ← map_one q, ← map_sub q]
    exact hx.map q
  refine ⟨⟨⟨g, hg⟩⟩, ?_⟩
  intro h
  let : Infinite F := h
  obtain ⟨a, _, _⟩ := symplecticQuotients s n c 1
  exact ⟨a⟩

end Models

section WeakApproximation

open Topology LocalNormOneCommutators.Spec
open private dense_scalar_diagonal completionDivisionRing completionT1 continuousMul_coordinates
  units_open_embedding from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

private theorem fromParameters_continuous {F A : Type u} {ι : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalDivisionRing F] [T1Space F] [Ring A] [Algebra F A] [Fintype ι]
    (s : Involution F A) (b : Module.Basis ι F A) :
    let := coordinateTopology b
    Continuous (fun y : CayleyParameters s => (fromParameters s y).val) := by
  let := coordinateTopology b
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply (units_open_embedding b).isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_induced_rng.mpr
  have hv : Continuous (fun y : CayleyParameters s => (y.val⁻¹).val) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  apply continuous_pi
  intro i
  have hb : Continuous (fun (x : A) j => b.repr x j) := continuous_induced_dom
  have hc : Continuous (fun y : CayleyParameters s => b.repr ((y.val⁻¹).val) i) :=
    (continuous_apply i).comp (hb.comp hv)
  change Continuous (fun y : CayleyParameters s => b.repr ((fromParameters s y).val.val.val) i)
  simp only [fromParameters_value, map_sub, Finsupp.sub_apply]
  exact continuous_const.sub hc

variable {K A : Type u} [Field K] [Ring A] [Algebra K A] [Module.Finite K A]
  (D : GlobalFieldData.{u,v} K) (T : Finset D.Place) (s : Involution K A)

local instance completionAlgebra (p : T) : Algebra K (D.Completion p.1) :=
  (D.embedding p.1).toAlgebra

private abbrev CompletedAlgebra (p : T) := D.Completion p.1 ⊗[K] A

private abbrev CompletedBasis (p : T) :=
  Module.Basis (Fin (Module.finrank (D.Completion p.1) (CompletedAlgebra (A := A) D T p)))
    (D.Completion p.1) (CompletedAlgebra (A := A) D T p)

private theorem includeRight_reflects_units {F : Type u} [Field F] [Algebra K F]
    {a : A} (ha : IsUnit ((1 : F) ⊗ₜ[K] a)) : IsUnit a := by
  classical
  let b := Module.finBasis K A
  apply (leftMulMatrix_isUnit b a).mp
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [isUnit_iff_ne_zero]
  have hn := ((Matrix.isUnit_iff_isUnit_det _).mp ((leftMulMatrix_isUnit (b.baseChange F) _).mpr ha)).ne_zero
  rw [leftMulMatrix_tmul] at hn
  change ((algebraMap K F).mapMatrix (Algebra.leftMulMatrix b a)).det ≠ 0 at hn
  rw [← RingHom.map_det] at hn
  intro he
  exact hn (by rw [he, map_zero])

set_option maxHeartbeats 650000 in
private theorem dense_chart_points
    (z : A) (hz : z + s.toLinearMap z = 1) (hT : T.Nonempty)
    (b : ∀ p : T, CompletedBasis (A := A) D T p) :
    let (p : T) := coordinateTopology (b p)
    ∀ (O : Set (∀ p : T, (s.baseChange (D.Completion p.1)).isometries)),
      IsOpen O →
      (∃ y : ∀ p : T, CayleyParameters (s.baseChange (D.Completion p.1)),
        (fun p => (fromParameters _ (y p)).val) ∈ O) →
      ∃ g : s.isometries, (fun p : T => isometryExtension (F := D.Completion p.1) s g) ∈ O := by
  classical
  intro _ O hO hOn
  let (p : T) := coordinateTopology (b p)
  let (p : T) := completionDivisionRing D p.1
  let (p : T) := completionT1 D p.1
  obtain ⟨y, hy⟩ := hOn
  let V := ∀ p : T, CayleyParameters (s.baseChange (D.Completion p.1))
  let W := ∀ p : T, CompletedAlgebra (A := A) D T p
  let j : V → W := Pi.map fun _ y => y.val.val
  let G (y : V) := fun p => (fromParameters _ (y p)).val
  have hj : IsInducing j := IsInducing.piMap fun p =>
    (units_open_embedding (b p)).isEmbedding.isInducing.comp IsInducing.subtypeVal
  have hG : Continuous G := by
    apply continuous_pi
    intro p
    have hp := fromParameters_continuous (s.baseChange (D.Completion p.1)) (b p)
    have heval : Continuous (fun x : V => x p) := continuous_apply p
    exact hp.comp heval
  obtain ⟨O', hO', he⟩ := hj.isOpen_iff.mp (hG.isOpen_preimage _ hO)
  let OU : Set W := Set.pi Set.univ (fun _ => {a | IsUnit a})
  have hOU : IsOpen OU := isOpen_set_pi Set.finite_univ fun p _ => by
    have hr : {a : CompletedAlgebra (A := A) D T p | IsUnit a} =
        Set.range (Units.val : (CompletedAlgebra (A := A) D T p)ˣ → _) := by
      ext a
      exact ⟨fun h => ⟨h.unit, h.unit_spec⟩, fun ⟨w, hw⟩ => hw ▸ w.isUnit⟩
    rw [hr]
    exact (units_open_embedding (b p)).isOpen_range
  let I := Fin (Module.finrank K (traceKernel s))
  let c := Module.finBasis K (traceKernel s)
  let Φ (x : I → ∀ p : T, D.Completion p.1) : W :=
    fun p => (1 : D.Completion p.1) ⊗ₜ[K] z +
      ∑ i, x i p • ((1 : D.Completion p.1) ⊗ₜ[K] (c i).val)
  have hΦ : Continuous Φ := by
    apply continuous_pi
    intro p
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro j
    change Continuous (fun x => (b p).coord j (Φ x p))
    simp only [Φ, map_add, map_sum, map_smul, smul_eq_mul]
    refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
    have h := (continuous_apply p).comp (continuous_apply (A := fun _ : I =>
      ∀ p : T, D.Completion p.1) i)
    exact h.mul continuous_const
  have hex : ∃ x, Φ x = j y := by
    have hl (p : T) := traceKernel_coordinates s c z hz (y p).val.val (y p).property
    choose a ha using hl
    refine ⟨fun i p => a p i, funext fun p => ?_⟩
    change Φ (fun i p => a p i) p = (y p).val.val
    simpa only [Φ, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using ha p
  obtain ⟨x, hx⟩ := hex
  have hy' : j y ∈ O' := by rw [← Set.mem_preimage, he]; exact hy
  have hyu : j y ∈ OU := fun p _ => (y p).val.isUnit
  obtain ⟨a, ha⟩ := (DenseRange.piMap (fun _ : I => dense_scalar_diagonal D T)).exists_mem_open
    (hΦ.isOpen_preimage (O' ∩ OU) (hO'.inter hOU)) ⟨x, by rw [Set.mem_preimage, hx]; exact ⟨hy', hyu⟩⟩
  let w : A := z + (∑ i : I, a i • c i : traceKernel s).val
  have hw (p : T) : (1 : D.Completion p.1) ⊗ₜ[K] w =
      Φ (Pi.map (fun (_ : I) (r : K) (p : T) => D.embedding p.1 r) a) p := by
    change (1 : D.Completion p.1) ⊗ₜ[K] w =
      (1 : D.Completion p.1) ⊗ₜ[K] z +
        ∑ i, D.embedding p.1 (a i) • ((1 : D.Completion p.1) ⊗ₜ[K] (c i).val)
    rw [show w = z + ∑ i, a i • (c i).val by simp [w]]
    rw [TensorProduct.tmul_add, TensorProduct.tmul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      smul_eq_mul, mul_one]
    rfl
  obtain ⟨p, hp⟩ := hT
  have hau : ∀ p : T, IsUnit ((1 : D.Completion p.1) ⊗ₜ[K] w) := by
    intro p
    rw [hw]
    exact ha.2 p (Set.mem_univ p)
  let q : T := ⟨p, hp⟩
  let : Algebra K (D.Completion q.1) := (D.embedding q.1).toAlgebra
  have hu : IsUnit w := includeRight_reflects_units (F := D.Completion q.1) (hau q)
  let y₀ : CayleyParameters s := ⟨hu.unit, by
    rw [hu.unit_spec]
    exact traceKernel_contains hz _⟩
  let y' : V := fun p => ⟨Units.map (Algebra.TensorProduct.includeRight (R := K)
      (A := D.Completion p.1)).toMonoidHom y₀.val, by
    change (1 : D.Completion p.1) ⊗ₜ[K] y₀.val.val +
      (s.baseChange (D.Completion p.1)).toLinearMap (1 ⊗ₜ[K] y₀.val.val) = 1
    rw [Involution.baseChange_tmul, ← TensorProduct.tmul_add, y₀.property,
      ← Algebra.TensorProduct.one_def]⟩
  have hjy : j y' = Φ (Pi.map (fun (_ : I) (r : K) (p : T) => D.embedding p.1 r) a) := by
    funext p
    change (1 : D.Completion p.1) ⊗ₜ[K] hu.unit.val = _
    rw [hu.unit_spec, hw]
  have hmem : G y' ∈ O := by
    change y' ∈ G ⁻¹' O
    rw [← he, Set.mem_preimage, hjy]
    exact ha.1
  refine ⟨(fromParameters s y₀).val, ?_⟩
  have hsame : (fun p : T => isometryExtension (F := D.Completion p.1) s (fromParameters s y₀).val) = G y' := by
    funext p
    apply Subtype.ext
    apply Units.ext
    let f : A →ₐ[K] CompletedAlgebra (A := A) D T p := Algebra.TensorProduct.includeRight
    change f ((fromParameters s y₀).val.val.val) = (fromParameters _ (y' p)).val.val.val
    rw [fromParameters_value, fromParameters_value, map_sub, map_one]
    congr 1
  rw [hsame]
  exact hmem

theorem weakApproximationFromChart : Spec.WeakApproximationFromChart.{u,v} := by
  classical
  intro K A _ D _ _ _ s z hz T _ b
  let (p : T) := coordinateTopology (b p)
  let (p : T) := completionDivisionRing D p.1
  let (p : T) := completionT1 D p.1
  let (p : T) := continuousMul_coordinates (b p)
  intro hquot
  by_cases hT : T.Nonempty
  · let U := ∀ p : T, (s.baseChange (D.Completion p.1)).isometries
    let quot (a : U × U) : U := fun p => a.1 p / a.2 p
    have hcont : Continuous quot := by
      apply continuous_pi
      intro p
      exact ((continuous_apply p).comp continuous_fst).mul
        (((continuous_apply p).comp continuous_snd).inv)
    rw [DenseRange, dense_iff_inter_open]
    intro O hO hOn
    obtain ⟨x, hx⟩ := hOn
    choose a b' hab using fun p : T => hquot p (x p)
    let a₀ : U := fun p => (a p).val
    let b₀ : U := fun p => (b' p).val
    have he : quot (a₀, b₀) = x := funext hab
    have hf : IsOpen (quot ⁻¹' O) := hcont.isOpen_preimage _ hO
    obtain ⟨V, W, hV, hW, ha, hb, hsub⟩ := isOpen_prod_iff.mp hf a₀ b₀ (by
      change quot (a₀, b₀) ∈ O
      rwa [he])
    obtain ⟨g, hg⟩ := dense_chart_points D T s z hz hT b V hV
      ⟨fun p => toParameters _ (a p), by
        have hh (p : T) : fromParameters _ (toParameters _ (a p)) = a p :=
          (cayleyEquiv _).left_inv (a p)
        simpa only [hh] using ha⟩
    obtain ⟨g', hg'⟩ := dense_chart_points D T s z hz hT b W hW
      ⟨fun p => toParameters _ (b' p), by
        have hh (p : T) : fromParameters _ (toParameters _ (b' p)) = b' p :=
          (cayleyEquiv _).left_inv (b' p)
        simpa only [hh] using hb⟩
    refine ⟨_, ?_, g / g', rfl⟩
    have hm := hsub (show ((fun p : T => isometryExtension (F := D.Completion p.1) s g),
      (fun p : T => isometryExtension (F := D.Completion p.1) s g')) ∈ V ×ˢ W from ⟨hg, hg'⟩)
    change quot ((fun p : T => isometryExtension (F := D.Completion p.1) s g),
      (fun p : T => isometryExtension (F := D.Completion p.1) s g')) ∈ O at hm
    simpa [quot, map_div] using hm
  · rw [DenseRange, dense_iff_inter_open]
    rintro O hO ⟨x, hx⟩
    refine ⟨x, hx, 1, funext fun p => ?_⟩
    exact (hT ⟨p.val, p.property⟩).elim

end WeakApproximation

section ModelApproximation

open _root_.Specs.RM03.CSA (isCentralSimple)
open LinearAlgebraicGroups.Specs.SymplecticDivisionForms (SplitComparison)
open LinearAlgebraicGroups.Specs.SymplecticInvolutionModels.DivisionForms (toDivisionInvolution)
open private involutionTraceOne splitComparisonBaseChange
  from LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels

private theorem globalField_infinite {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K) :
    Infinite K := by
  cases D with
  | number h =>
    let := h
    exact CharZero.infinite K
  | function F t => exact t.transcendental.infinite

theorem symplecticWeakApproximation : Spec.SymplecticWeakApproximation.{u,v} := by
  intro K A L _ D _ _ _ _ _ _ s n c
  obtain ⟨z, hz⟩ := involutionTraceOne s c
  intro T Ap b
  apply weakApproximationFromChart D s z hz T b
  intro p
  let : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra
  let : Infinite K := globalField_infinite D
  let : Infinite (D.Completion p.1) := Infinite.of_injective (D.embedding p.1) (D.embedding p.1).injective
  exact symplecticQuotients (s.baseChange (D.Completion p.1)) n
    (splitComparisonBaseChange (F := D.Completion p.1) s c)

theorem unitaryWeakApproximation : Spec.UnitaryWeakApproximation.{u,v} := by
  intro K E A _ D _ _ _ _ _ _ _ _ hA s
  let : IsSimpleRing A := hA.1
  let : Module.Finite E A := hA.2.2
  let : Module.Finite K A := Module.Finite.trans E A
  obtain ⟨z, hz⟩ := unitaryTraceOne s
  intro T Ap b
  apply weakApproximationFromChart D (groundInvolution s) z.val hz T b
  intro p
  let : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra
  let : Infinite K := globalField_infinite D
  let : Infinite (D.Completion p.1) := Infinite.of_injective (D.embedding p.1) (D.embedding p.1).injective
  exact unitaryQuotients hA s

end ModelApproximation

section FiniteCommutators

open Topology MulOpposite
open UnitaryNormEquations (factorPair factorProjection adjointAt unitaryNorm)
open _root_.Specs.RM03.CSA (isCentralSimple reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)
open LocalNormOneCommutators.Spec
open private continuous_linear_coordinate units_open_embedding from
  LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

variable {F B C : Type u} [Field F] [Ring B] [Ring C] [Algebra F B] [Algebra F C]

private def splitCentreGroupEquiv (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution F C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1)) :
    s.isometries ≃* Bˣ :=
  MulEquiv.ofBijective (firstProjection e s)
    ⟨fun x y h => by
      apply Subtype.ext
      apply Units.ext
      apply e.injective
      rw [firstProjection_pair e s he, firstProjection_pair e s he, h],
      firstProjection_surjective e s he⟩

omit [Algebra F B] in
private theorem splitCentreGroupEquiv_symm_val (e : C ≃+* B × Bᵐᵒᵖ) (s : Involution F C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1)) (w : Bˣ) :
    ((splitCentreGroupEquiv e s he).symm w).val.val = e.symm (w.val, op (w⁻¹).val) := by
  apply e.injective
  rw [e.apply_symm_apply, firstProjection_pair e s he]
  change ((splitCentreGroupEquiv e s he ((splitCentreGroupEquiv e s he).symm w)).val,
    op ((splitCentreGroupEquiv e s he ((splitCentreGroupEquiv e s he).symm w))⁻¹).val) = _
  rw [MulEquiv.apply_symm_apply]

private theorem splitCentre_symm_continuous [TopologicalSpace F] [IsTopologicalDivisionRing F]
    [T1Space F] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis ι F B) (c : Module.Basis κ F C)
    (e : C ≃ₐ[F] B × Bᵐᵒᵖ) (s : Involution F C)
    (he : ∀ x, e (s.toLinearMap x) = (unop (e x).2, op (e x).1)) :
    letI := coordinateTopology b
    letI := coordinateTopology c
    Continuous (splitCentreGroupEquiv e.toRingEquiv s he).symm := by
  let : TopologicalSpace B := coordinateTopology b
  let : TopologicalSpace C := coordinateTopology c
  apply IsInducing.subtypeVal.continuous_iff.mpr
  apply (units_open_embedding c).isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro j
  let p := (c.coord j).comp e.symm.toLinearMap
  let l : B →ₗ[F] F := p.comp (LinearMap.inl F B Bᵐᵒᵖ)
  let r : B →ₗ[F] F := p.comp ((LinearMap.inr F B Bᵐᵒᵖ).comp (opLinearEquiv F).toLinearMap)
  have hf : (fun w : Bˣ => c.repr (((splitCentreGroupEquiv e.toRingEquiv s he).symm w).val.val) j)
      = fun w => l w.val + r (w⁻¹).val := by
    funext w
    rw [splitCentreGroupEquiv_symm_val]
    change p (w.val, op (w⁻¹).val) = _
    rw [show (w.val, op (w⁻¹).val) = (w.val, 0) + (0, op (w⁻¹).val) by simp,
      map_add]
    rfl
  change Continuous (fun w : Bˣ => c.repr (((splitCentreGroupEquiv e.toRingEquiv s he).symm w).val.val) j)
  rw [hf]
  exact ((continuous_linear_coordinate b l).comp Units.continuous_val).add
    ((continuous_linear_coordinate b r).comp Units.continuous_coe_inv)

private theorem normAt_field {k A L ι : Type*} [Field k] [Ring A] [Algebra k A]
    [Field L] [Algebra k L] [Fintype ι] (hA : isCentralSimple k A)
    (b : Module.Basis ι k A) (hL : isCentralSimple L (L ⊗[k] A)) (x : L ⊗[k] A) :
    normAt hA b x = reducedNorm hL x := by
  change _root_.RM03.CSA.NormOneGroup.normAt hA b x = _root_.RM03.CSA.reducedNorm hL x
  rw [← _root_.RM03.CSA.reducedNorm_basis_eval hL (b.baseChange L) x,
    _root_.RM03.CSA.reducedNorm_basis_baseChange hA b hL]
  change MvPolynomial.eval₂ _ _ _ = MvPolynomial.eval _ _
  exact MvPolynomial.eval₂_eq_eval_map _ _ _

set_option maxHeartbeats 700000 in
theorem finiteSplitCentreCommutators : Spec.FiniteSplitCentreCommutators.{u} := by
  intro k E A F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA ι _ b s C c
  let t := (groundInvolution s).baseChange F
  let B := F ⊗[E] A
  have hB : isCentralSimple F B := _root_.RM03.CSA.isCentralSimple_baseChange hA
  let : Module.Finite F B := hB.2.2
  let bB := Module.finBasis F B
  let : TopologicalSpace B := coordinateTopology bB
  let : TopologicalSpace C := coordinateTopology c
  obtain ⟨hpair, hswap, _⟩ := UnitaryNormEquations.splitCentreComparison (R := F) hA b s
  let p : C →ₐ[F] B × Bᵐᵒᵖ := {
    __ := (factorPair (R := F) s).toRingHom
    commutes' r := by
      change factorPair s (r ⊗ₜ[k] (1 : A)) = (r ⊗ₜ[E] (1 : A), op (r ⊗ₜ[E] (1 : A)))
      change (factorProjection _, op (factorProjection (adjointAt s _))) = _
      simp [UnitaryNormEquations.adjointAt_tmul] }
  let e : C ≃ₐ[F] B × Bᵐᵒᵖ := AlgEquiv.ofBijective p hpair
  have he (x : C) : e (t.toLinearMap x) = (unop (e x).2, op (e x).1) := by
    change factorPair s (((groundInvolution s).baseChange F).toLinearMap x) = _
    rw [groundInvolution_baseChange]
    exact hswap x
  let q := splitCentreGroupEquiv e.toRingEquiv t he
  have hq := splitCentre_symm_continuous bB c e t he
  intro U g hg
  have hnorm : q g ∈ normOne hB := by
    change reducedNorm hB (factorProjection g.val.val) = 1
    rw [← normAt_field hA b hB]
    change _root_.RM03.CSA.NormOneGroup.normAt hA b (factorProjection g.val.val) = 1
    exact (UnitaryNormEquations.factorProjection_norm (F := k) hA b g.val.val).trans (by
      rw [hg.2, map_one])
  have hc := LocalNormOneCommutators.localAlgebras.1 hB bB hnorm
  have hm := image_closure_subset_closure_image hq ⟨q g, hc, q.symm_apply_apply g⟩
  apply closure_mono _ hm
  rintro _ ⟨w, hw, rfl⟩
  have hn := Subgroup.mem_map_of_mem q.symm.toMonoidHom hw
  rw [map_commutator_of_surjective (f := q.symm.toMonoidHom) q.symm.surjective] at hn
  exact hn

end FiniteCommutators

section CompactReal

open scoped Matrix commutatorElement
open Matrix

private theorem cyclic_ratios {G : Type*} [CommGroup G] (n : ℕ)
    (eigenvalues : Fin (n + 1) → G) (h : ∏ i, eigenvalues i = 1) :
    ∃ η : Fin (n + 1) → G, ∀ i, η (finRotate _ i) = eigenvalues i * η i := by
  let earlier (i : Fin (n + 1)) := Finset.univ.filter (fun j => j < i)
  let η (i : Fin (n + 1)) := ∏ j ∈ earlier i, eigenvalues j
  refine ⟨η, fun i => ?_⟩
  by_cases hi : i = Fin.last n
  · subst i
    have hr : insert (Fin.last n) (earlier (Fin.last n)) = Finset.univ := by
      ext j
      simp [earlier]
      exact (le_or_gt j (Fin.last n)).elim (fun hj => hj.eq_or_lt) (fun hj =>
        False.elim (not_lt_of_ge (Fin.le_last j) hj))
    rw [finRotate_last]
    have hz : earlier 0 = ∅ := by ext j; simp [earlier]
    change (∏ j ∈ earlier 0, eigenvalues j) = _
    rw [hz, Finset.prod_empty, ← Finset.prod_insert (by simp [earlier]), hr, h]
  · have hr : earlier (finRotate _ i) = insert i (earlier i) := by
      ext j
      simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      change j.val < (finRotate (n + 1) i).val ↔ j = i ∨ j.val < i.val
      rw [coe_finRotate_of_ne_last hi, Nat.lt_succ_iff, le_iff_eq_or_lt]
      simp only [Fin.val_eq_val]
    change (∏ j ∈ earlier (finRotate _ i), eigenvalues j) = _
    rw [hr, Finset.prod_insert (by simp [earlier])]

private def unitaryDiagonal {n : ℕ} (η : Fin n → unitary ℂ) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨Matrix.diagonal (fun i => (η i).val),
    Matrix.diagonal_mem_unitary.mpr (Pi.mem_unitary_iff.mpr fun i => (η i).property)⟩

private def unitaryPermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨σ.permMatrix ℂ, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      mul_inv_cancel, Matrix.permMatrix_one]⟩

private theorem diagonal_commutator {n : ℕ} (ζ : Fin n → unitary ℂ)
    (hζ : ∏ i, ζ i = 1) :
    ∃ a b : Matrix.unitaryGroup (Fin n) ℂ, ⁅a, b⁆ = unitaryDiagonal ζ := by
  cases n with
  | zero =>
    refine ⟨1, 1, Subtype.ext ?_⟩
    exact Subsingleton.elim _ _
  | succ n =>
    obtain ⟨η, hη⟩ := cyclic_ratios n ζ hζ
    let σ := finRotate (n + 1)
    let P := unitaryPermutation σ
    let D := unitaryDiagonal η
    let H := unitaryDiagonal ζ
    have h : P * D = H * D * P := by
      apply Subtype.ext
      change σ.permMatrix ℂ * Matrix.diagonal (fun i => (η i).val) =
        Matrix.diagonal (fun i => (ζ i).val) * Matrix.diagonal (fun i => (η i).val) * σ.permMatrix ℂ
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hh : j = σ i
      · subst j
        simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some, ite_true, one_mul, mul_one]
        exact congrArg (fun z : unitary ℂ => z.val) (hη i)
      · simp [PEquiv.toMatrix_apply, Ne.symm hh]
    refine ⟨P, D, ?_⟩
    change P * D * P⁻¹ * D⁻¹ = H
    rw [h, mul_inv_cancel_right, mul_inv_cancel_right]

private theorem unitary_eigenbasis_matrix {n : ℕ} (g : Matrix.unitaryGroup (Fin n) ℂ)
    (hg : g.val.det = 1) :
    ∃ (Q : Matrix.unitaryGroup (Fin n) ℂ) (ζ : Fin n → unitary ℂ),
      (∏ i, ζ i) = 1 ∧ g = Q * unitaryDiagonal ζ * Q⁻¹ := by
  let b₀ := EuclideanSpace.basisFun (Fin n) ℂ
  let T := (Matrix.toLin b₀.toBasis b₀.toBasis) g.val
  have ht : D05.IsUnitaryMap T := by
    apply (D05.M13.Unitary.unitary_iff_adjoint_identities T).mpr
    have h := Unitary.mem_iff.mp g.property
    have ha : LinearMap.adjoint T =
        (Matrix.toLin b₀.toBasis b₀.toBasis) (star g.val) :=
      (Matrix.toLin_conjTranspose b₀ b₀ g.val).symm
    constructor
    · rw [ha, ← Matrix.toLin_mul b₀.toBasis b₀.toBasis b₀.toBasis, h.1]
      exact Matrix.toLin_one b₀.toBasis
    · rw [ha, ← Matrix.toLin_mul b₀.toBasis b₀.toBasis b₀.toBasis, h.2]
      exact Matrix.toLin_one b₀.toBasis
  obtain ⟨b, z, hz, hzn⟩ := D05.M13.UnitarySpectrum.Cayley.unitary_eigenbasis T ht
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = n := by
    simp [Module.finrank_eq_card_basis b₀.toBasis]
  let e := finCongr hn
  let b' := b.reindex e
  have hb (i : Fin n) : T (b' i) = z (e.symm i) • b' i := by
    simp [b', hz]
  let ζ (i : Fin n) : unitary ℂ := ⟨z (e.symm i), by
    have hnorm := hzn (e.symm i)
    apply Unitary.mem_iff.mpr
    have h : z (e.symm i) * star (z (e.symm i)) = 1 := by
      rw [Complex.star_def, Complex.mul_conj', hnorm]
      norm_num
    exact ⟨by simpa [mul_comm] using h, h⟩⟩
  let Q₀ : Matrix (Fin n) (Fin n) ℂ := (LinearMap.toMatrix b'.toBasis b₀.toBasis) LinearMap.id
  have hQ : Q₀ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Q₀ᴴ * Q₀ = 1
    have hA : Q₀ᴴ = (LinearMap.toMatrix b₀.toBasis b'.toBasis) LinearMap.id := by
      rw [← LinearMap.toMatrix_adjoint b' b₀, LinearMap.adjoint_id]
    rw [hA]
    simp only [Q₀, LinearMap.toMatrix_eq_basisToMatrix, LinearMap.id_coe, Function.id_comp]
    exact Module.Basis.toMatrix_mul_toMatrix_flip b'.toBasis b₀.toBasis
  let Q : Matrix.unitaryGroup (Fin n) ℂ := ⟨Q₀, hQ⟩
  let D := unitaryDiagonal ζ
  have hdiag : (LinearMap.toMatrix b'.toBasis b'.toBasis) T = D.val := by
    ext i j
    change (LinearMap.toMatrix b'.toBasis b'.toBasis) T i j =
      Matrix.diagonal (fun i => (ζ i).val) i j
    rw [LinearMap.toMatrix_apply]
    change b'.toBasis.repr (T (b' j)) i = _
    rw [hb, map_smul, Finsupp.smul_apply]
    change z (e.symm j) • (b'.toBasis.repr (b'.toBasis j)) i = _
    rw [Module.Basis.repr_self]
    by_cases hij : i = j <;> simp [hij, ζ]
  have hprod : g * Q = Q * D := by
    apply Subtype.ext
    change g.val * Q₀ = Q₀ * D.val
    apply (Matrix.toLin b'.toBasis b₀.toBasis).injective
    rw [Matrix.toLin_mul b'.toBasis b₀.toBasis b₀.toBasis,
      Matrix.toLin_mul b'.toBasis b'.toBasis b₀.toBasis, ← hdiag]
    simp only [Q₀, Matrix.toLin_toMatrix, LinearMap.comp_id, LinearMap.id_comp, T]
  have hconj : g = Q * D * Q⁻¹ := by rw [← hprod, mul_inv_cancel_right]
  refine ⟨Q, ζ, ?_, hconj⟩
  have hD : D.val.det = 1 := by
    rw [hconj] at hg
    let q : (Matrix (Fin n) (Fin n) ℂ)ˣ := Unitary.toUnits Q
    exact (Matrix.det_units_conj q D.val).symm.trans hg
  apply Subtype.ext
  have hp := map_prod (unitary ℂ).subtype ζ Finset.univ
  change (↑(∏ i, ζ i) : ℂ) = 1
  rw [show (↑(∏ i, ζ i) : ℂ) = ∏ i, (ζ i).val from hp]
  rwa [show D.val = Matrix.diagonal (fun i => (ζ i).val) from rfl, Matrix.det_diagonal] at hD

theorem compactRealCommutators : Spec.CompactRealCommutators := by
  intro n g hg
  obtain ⟨Q, ζ, hζ, hQ⟩ := unitary_eigenbasis_matrix g hg
  obtain ⟨a, b, hab⟩ := diagonal_commutator ζ hζ
  refine ⟨MulAut.conj Q a, MulAut.conj Q b, ?_⟩
  rw [← map_commutatorElement, hab, hQ]
  rfl

theorem compactRealCommutatorClosure : Spec.CompactRealCommutatorClosure.{u} := by
  intro U _ _ n e g hg
  obtain ⟨a, b, hab⟩ := compactRealCommutators n (e g) hg
  have h : ⁅e.symm a, e.symm b⁆ = g := by
    apply e.injective
    simpa only [map_commutatorElement, MulEquiv.apply_symm_apply] using hab
  apply subset_closure
  rw [← h]
  exact Subgroup.commutator_mem_commutator (by trivial) (by trivial)

end CompactReal

section ProductsOfCommutators

open Topology LocalNormOneCommutators.Spec
open private completionDivisionRing continuousMul_coordinates commutator_mem_closure_of_denseRange
  from LinearAlgebraicGroups.Arithmetic.LocalNormOneCommutators

theorem simultaneousNormOneApproximation : Spec.SimultaneousNormOneApproximation.{u,v} := by
  classical
  intro K E A _ D _ _ _ _ _ _ _ _ hA s T Ap Up b
  let (p : T) : Algebra K (D.Completion p.1) := (D.embedding p.1).toAlgebra
  let s₀ := groundInvolution s
  let (p : T) := coordinateTopology (b p)
  let (p : T) := completionDivisionRing D p.1
  let (p : T) := continuousMul_coordinates (b p)
  intro x hx
  let H := ∀ p : T, Up p
  let φ : s₀.isometries →* H :=
    MonoidHom.pi fun p => isometryExtension (F := D.Completion p.1) s₀
  have hφ : DenseRange φ := unitaryWeakApproximation D hA s T b
  have hcomm := commutator_mem_closure_of_denseRange φ hφ
  have hC : x ∈ closure (commutator H : Set H) := by
    rw [commutator_def, ← Subgroup.pi_top Set.univ (f := fun p => ↥(Up p)), Subgroup.commutator_pi_pi_of_finite]
    change x ∈ closure (Set.pi Set.univ (fun p => (commutator ↥(Up p) : Set ↥(Up p))))
    exact mem_closure_pi.mpr fun p _ => hx p
  apply closure_mono _ (closure_minimal hcomm (Subgroup.isClosed_topologicalClosure _) hC)
  rintro y ⟨g, hg, rfl⟩
  have hng : g.val ∈ commutator Aˣ := by
    have h := Subgroup.mem_map_of_mem s₀.isometries.subtype hg
    rw [Subgroup.map_subtype_commutator] at h
    exact (Subgroup.commutator_mono le_top le_top) h
  exact ⟨⟨g, LocalNormOneCommutators.commutator_norm_one hA hng⟩, rfl⟩

end ProductsOfCommutators

end LinearAlgebraicGroups.Arithmetic.UnitaryCayleyChart
