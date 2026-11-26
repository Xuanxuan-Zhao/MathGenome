import Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Arithmetic.QuaternionSpinScaleCover
import LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
import LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators
import LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.CentralizerDimension
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.ReducedNorm
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.NormOneGroup
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.AlgebraicGeometry.EffectiveEpi
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.NoncommRing

namespace LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic

open Specs.Arithmetic.QuaternionSpinOddCharacteristic
open Specs.SymplecticDivisionForms (antiValue dagger)
open scoped Matrix

universe u

section BlockWords

variable {F B : Type u} [CommRing F] [Ring B] [Algebra F B]
  (σ : B ≃ₐ[F] Bᵐᵒᵖ)

@[local simp] private theorem bar_zero : antiValue σ 0 = 0 := by simp [antiValue]
@[local simp] private theorem bar_one : antiValue σ 1 = 1 := by simp [antiValue]
@[local simp] private theorem bar_neg (x : B) : antiValue σ (-x) = -antiValue σ x := by
  simp [antiValue]
@[local simp] private theorem bar_mul (x y : B) :
    antiValue σ (x * y) = antiValue σ y * antiValue σ x := by
  simp [antiValue]

private theorem bar_inv_mul (b : Bˣ) :
    antiValue σ (↑b⁻¹) * antiValue σ ↑b = 1 := by
  rw [← bar_mul, b.mul_inv, bar_one]

private theorem bar_mul_inv (b : Bˣ) :
    antiValue σ ↑b * antiValue σ (↑b⁻¹) = 1 := by
  rw [← bar_mul, b.inv_mul, bar_one]

private theorem bar_inv_pure (q : Bˣ) (hq : antiValue σ (q : B) = -(q : B)) :
    antiValue σ (↑q⁻¹) = -(↑q⁻¹ : B) := by
  have h := bar_inv_mul σ q
  rw [hq, mul_neg, neg_eq_iff_eq_neg] at h
  calc
    antiValue σ (↑q⁻¹) = (antiValue σ (↑q⁻¹) * (q : B)) * (↑q⁻¹ : B) := by simp [mul_assoc]
    _ = _ := by rw [h, neg_one_mul]

private theorem shear_isometries : ShearIsometries.{u} := by
  intro F B _ _ _ σ hσ q hq a b hab
  have hbar : antiValue σ (↑q⁻¹) = -(↑q⁻¹ : B) := bar_inv_pure σ q hq
  have htop : a * ↑q⁻¹ * antiValue σ a = antiValue σ b - b := by
    rw [← neg_inj, neg_sub, neg_neg] at hab
    exact hab.symm
  constructor
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dagger, upperShear, lowerShear, lineGram, Matrix.mul_apply, Fin.sum_univ_three,
        hσ a, hbar, ← mul_assoc, htop]
    all_goals abel

private theorem opposite_shear_word : OppositeShearWord.{u} := by
  intro F B _ _ _ σ hσ q hq a b hab
  dsimp only
  let A := antiValue σ a
  let p : B := ↑q⁻¹
  let x : B := ↑b
  let y := antiValue σ x
  let v : B := ↑b⁻¹
  let w := antiValue σ v
  have hxv : x * v = 1 := b.mul_inv
  have hvx : v * x = 1 := b.inv_mul
  have hyw : y * w = 1 := bar_mul_inv σ b
  have hwy : w * y = 1 := bar_inv_mul σ b
  have h : a * p * A = y - x := by
    change (b : B) - antiValue σ ↑b = -(a * p * A) at hab
    rw [← neg_inj, neg_sub, neg_neg] at hab
    exact hab.symm
  have hw : antiValue σ w = v := hσ v
  have hra : antiValue σ (v * a) = A * w := bar_mul σ v a
  have hla : antiValue σ (-(w * a)) = -(A * v) := by
    simp only [bar_neg, bar_mul, hw, A]
  change (w - antiValue σ w = -((-(w * a)) * p * antiValue σ (-(w * a)))) ∧
    (w - antiValue σ w = -((v * a) * p * antiValue σ (v * a))) ∧
    lowerShear σ q (-(w * a)) w * upperShear σ q a x * lowerShear σ q (v * a) w =
      interchange b (1 + p * A * v * a) σ
  have hadm₁ : w - v = -(w * (a * p * A) * v) := by
    rw [h, mul_sub, sub_mul, hwy, mul_assoc w x v, hxv, one_mul, mul_one, neg_sub]
  have hadm₂ : w - v = -(v * (a * p * A) * w) := by
    rw [h, mul_sub, sub_mul, mul_assoc v y w, hyw, hvx,
      one_mul, mul_one, neg_sub]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw, hla, hadm₁]
    noncomm_ring
  · rw [hw, hra, hadm₂]
    noncomm_ring
  have htop₁ : 1 + a * -(p * (A * w)) + x * -w = 0 := by
    rw [mul_neg, ← mul_assoc p A w, ← mul_assoc a (p * A) w, ← mul_assoc a p A, h,
      sub_mul, hyw]
    simp
  have htop₂ : a + x * -(v * a) = 0 := by rw [mul_neg, ← mul_assoc, hxv, one_mul, add_neg_cancel]
  have hmiddle : -(p * (A * w)) + -(p * A) * -w = 0 := by
    rw [← mul_assoc p A w, neg_mul_neg, neg_add_cancel]
  have hright : upperShear σ q a x * lowerShear σ q (v * a) w =
      !![0, 0, x; 0, 1 + p * A * v * a, -(p * A); -w, -(v * a), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperShear, lowerShear, Matrix.mul_apply, Fin.sum_univ_three, hra]
    all_goals first | rfl | simpa only [mul_neg] using htop₁ |
      simpa only [mul_neg] using htop₂ | simpa only [neg_mul_neg, ← mul_assoc] using hmiddle | (simp only [← mul_assoc]; rfl)
  have hbot₂ : w * a * (1 + p * A * v * a) - v * a = 0 := by
    rw [mul_add, mul_one, ← mul_assoc (w * a) (p * A * v) a,
      ← mul_assoc (w * a) (p * A) v, mul_assoc w a (p * A), ← mul_assoc a p A, h,
      mul_sub, sub_mul, hwy, one_mul, mul_assoc w x v, hxv, mul_one, sub_mul]
    abel
  have hbot₃ : -w * x + w * a * -(p * A) + 1 = 0 := by
    rw [neg_mul, mul_neg, mul_assoc w a (p * A), ← mul_assoc a p A, h,
      mul_sub, hwy]
    abel
  rw [mul_assoc, hright]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, interchange, Matrix.mul_apply, Fin.sum_univ_three, hla,
      ← mul_assoc, mul_one]
  all_goals first | rfl | (simpa only [← mul_assoc, neg_mul, mul_neg] using hbot₃) |
    (change (p * A) * v * x + -(p * A) = 0; rw [mul_assoc, hvx, mul_one, add_neg_cancel]) |
    simpa only [sub_eq_add_neg] using hbot₂

end BlockWords

open Specs.SymplecticDivisionForms (Involution)
open Specs.SymplecticInvolutionModels (quaternionConjugate)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open MulOpposite

section Conjugation

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
  (σ : Involution F B)

private theorem conjugate_mul (x y : B) :
    antiValue σ.anti (x * y) = antiValue σ.anti y * antiValue σ.anti x := by simp [antiValue]

private theorem bar_scalar (t : F) : antiValue σ.anti (algebraMap F B t) = algebraMap F B t := by
  simp [antiValue, AlgEquiv.commutes]

private theorem bar_add (x y : B) :
    antiValue σ.anti (x + y) = antiValue σ.anti x + antiValue σ.anti y := by simp [antiValue]

private theorem trace_scalar (hB : isCentralSimple F B)
    (hσ : ∀ x, antiValue σ.anti x = quaternionConjugate hB x) (x : B) :
    x + antiValue σ.anti x ∈ Set.range (algebraMap F B) := by
  unfold quaternionConjugate at hσ
  rw [hσ, add_sub_cancel]
  exact Set.mem_range_self _

private theorem scalar_of_bar_fixed (hB : isCentralSimple F B)
    (hσ : ∀ x, antiValue σ.anti x = quaternionConjugate hB x) (h2 : (2 : F) ≠ 0)
    {x : B} (hx : antiValue σ.anti x = x) : x ∈ Set.range (algebraMap F B) := by
  obtain ⟨t, ht⟩ := trace_scalar σ hB hσ x
  rw [hx, ← two_mul, ← map_ofNat (algebraMap F B)] at ht
  refine ⟨(2 : F)⁻¹ * t, ?_⟩
  rw [map_mul, ht, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h2, map_one, one_mul]

end Conjugation

section QuadraticLine

open QuadraticAlgebra

private theorem quadraticAlgebra_norm {F : Type u} [Field F] {a b : F}
    (z : QuadraticAlgebra F a b) : Algebra.norm F z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  congr 1

private theorem fixed_line_parameters : FixedLineParameters.{u} := by
  intro F B _ _ _ h2 hB hd σ hσ q hq
  classical
  let _ : FiniteDimensional F B := hB.2.2
  have hq_ne : (q : B) ≠ 0 := q.ne_zero
  have hq_ns : (q : B) ∉ Set.range (algebraMap F B) := by
    rintro ⟨c, hc⟩
    have he : (q : B) = -(q : B) := by simpa [← hc, bar_scalar] using hq
    have ht : algebraMap F B (2 : F) * (q : B) = 0 := by
      rw [map_ofNat, two_mul]
      exact add_eq_zero_iff_eq_neg.mpr he
    have hmap2 : algebraMap F B (2 : F) ≠ 0 := by
      simpa only [map_zero] using (algebraMap F B).injective.ne h2
    exact (mul_ne_zero hmap2 hq_ne) ht
  have hq_sq_fixed : antiValue σ.anti ((q : B) * q) = (q : B) * q := by
    rw [conjugate_mul, hq, neg_mul_neg]
  obtain ⟨a, ha⟩ := scalar_of_bar_fixed σ hB hσ h2 hq_sq_fixed
  have ha_ne : a ≠ 0 := by
    intro hz
    rw [hz, map_zero] at ha
    exact mul_ne_zero hq_ne hq_ne ha.symm
  have ha_nsq : ∀ t : F, t ^ 2 ≠ a + 0 * t := by
    intro t ht
    have hprod : ((q : B) - algebraMap F B t) * ((q : B) + algebraMap F B t) = 0 := by
      have ht' : t * t = a := by simpa [pow_two] using ht
      rw [sub_mul, mul_add, mul_add, Algebra.commutes, ← ha, ← map_mul, ht', add_comm (algebraMap F B a), sub_self]
    rcases mul_eq_zero.mp hprod with hn | hp
    · exact hq_ns ⟨t, (sub_eq_zero.mp hn).symm⟩
    · exact hq_ns ⟨-t, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left hp).symm⟩
  let _ : Fact (∀ t : F, t ^ 2 ≠ a + 0 * t) := ⟨ha_nsq⟩
  let E := QuadraticAlgebra F a 0
  let root : E := QuadraticAlgebra.omega
  let j : E →ₐ[F] B := QuadraticAlgebra.lift ⟨(q : B), by
    rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, ha]⟩
  have hjroot : j root = (q : B) := by
    change (0 : F) • (1 : B) + (1 : F) • (q : B) = _
    simp
  have hroot_ne : root ≠ 0 := fun hz => hq_ne (hjroot.symm.trans (hz ▸ j.map_zero))
  let qe : Eˣ := Units.mk0 root hroot_ne
  have hroot_sq : root ^ 2 = algebraMap F E a := by
    simpa [root, ← Algebra.algebraMap_eq_smul_one] using
      (omega_pow_two_eq_add (R := F) (a := a) (b := 0))
  have hroot_star : star root = -root := by
    apply QuadraticAlgebra.ext
    · change (0 : F) + 0 * 1 = -0
      simp
    · rfl
  have hexpand (z : E) : z = algebraMap F E z.re + algebraMap F E z.im * root := by
    rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def]
    exact (re_smul_add_im_smul z).symm
  have hseproot : IsSeparable F root :=
    (Polynomial.separable_X_pow_sub_C a (n := 2) (by simpa using h2) ha_ne).of_dvd
      (minpoly.dvd F root (by simp [hroot_sq]))
  let _ : Algebra.IsSeparable F E :=
    ⟨fun z => by
      conv => arg 2; rw [hexpand z]
      exact Field.isSeparable_add (isSeparable_algebraMap _) (Field.isSeparable_mul
        (isSeparable_algebraMap _) hseproot)⟩
  have hjexpand (z : E) : j z = algebraMap F B z.re + algebraMap F B z.im * (q : B) := by
    conv_lhs => rw [hexpand z]
    simp only [map_add, map_mul, AlgHom.commutes, hjroot]
  have hbarj (z : E) : antiValue σ.anti (j z) = j (star z) := by
    have hre : (star z).re = z.re := by
      change z.re + 0 * z.im = z.re
      simp
    have him : (star z).im = -z.im := rfl
    rw [hjexpand z, hjexpand (star z), hre, him]
    simp only [bar_add, conjugate_mul, bar_scalar, hq, map_neg, neg_mul, mul_neg,
      Algebra.commutes (R := F) (A := B) z.im (q : B)]
  refine ⟨E, inferInstance, inferInstance, inferInstance, j, qe, hjroot, finrank_eq_two a 0,
    ?_, fun z => ⟨z.re, z.im, hexpand z⟩, ?_, ?_, ?_⟩
  · let C := Subalgebra.centralizer F (j.range : Set B)
    have hJC : j.range ≤ C := by
      rintro _ ⟨z, rfl⟩
      exact (Subalgebra.mem_centralizer_iff F).mpr fun _ ⟨w, hw⟩ =>
        hw ▸ ((Commute.all w z).map j).eq
    have hJ : IsSimpleRing j.range :=
      IsSimpleRing.of_ringEquiv (AlgEquiv.ofInjective j j.injective).toRingEquiv inferInstance
    have hr : Module.finrank F j.range = 2 :=
      (AlgEquiv.ofInjective j j.injective).toLinearEquiv.finrank_eq.symm.trans (finrank_eq_two a 0)
    have hdim := (RM03.CSA.centralizer_simple_and_finrank hB j.range hJ).2
    change Module.finrank F j.range * Module.finrank F C = Module.finrank F B at hdim
    have hd' : RM03.CSA.degree F B = 2 := hd
    rw [hr, RM03.CSA.finrank_eq_degree_sq hB, hd'] at hdim
    have hCJ : j.range = C := Subalgebra.eq_of_le_of_finrank_le hJC (by omega)
    intro x
    constructor
    · intro hx
      change x ∈ j.range
      rw [hCJ]
      refine (Subalgebra.mem_centralizer_iff F).mpr ?_
      rintro _ ⟨z, rfl⟩
      change j z * x = x * j z
      rw [hjexpand z]
      exact (Commute.add_left (Algebra.commutes _ x)
        (Commute.mul_left (Algebra.commutes _ x) hx.symm)).eq
    · rintro ⟨z, rfl⟩
      rw [← hjroot]
      exact (Commute.all z root).map j
  · intro z
    rw [hbarj, ← map_mul, mul_comm (star z), ← algebraMap_norm_eq_mul_star, j.commutes,
      quadraticAlgebra_norm]
  · intro r hr hr1
    have hr0 : (r : E) - 1 ≠ 0 := fun hz => hr1 (Units.ext (sub_eq_zero.mp hz))
    let b₀ : E := ((r : E) - 1)⁻¹ * root⁻¹
    have hb0 : b₀ ≠ 0 := mul_ne_zero (inv_ne_zero hr0) (inv_ne_zero hroot_ne)
    have hbr : b₀ * ((r : E) - 1) = root⁻¹ := by
      dsimp [b₀]
      rw [mul_comm (((r : E) - 1)⁻¹), mul_assoc, inv_mul_cancel₀ hr0, mul_one]
    have hrbar : star (r : E) * r = 1 := by
      rw [mul_comm, ← algebraMap_norm_eq_mul_star, ← quadraticAlgebra_norm, hr, map_one]
    have hbarbr : star b₀ * ((r : E) - 1) = root⁻¹ * r := by
      have he : (star (r : E) - 1) * star b₀ = -root⁻¹ := by
        rw [← star_one, ← star_sub, ← star_mul, hbr, star_inv₀, hroot_star, inv_neg]
      have he' := congrArg (fun x : E => (r : E) * x) he
      change (r : E) * ((star (r : E) - 1) * star b₀) = (r : E) * -root⁻¹ at he'
      rw [← mul_assoc, mul_sub, mul_comm (r : E) (star (r : E)), hrbar, mul_one, ← neg_sub,
        neg_mul, mul_neg, neg_inj] at he'
      simpa only [mul_comm] using he'
    have hbbar : star b₀ = b₀ * r := by
      apply mul_right_cancel₀ hr0
      rw [hbarbr, mul_right_comm b₀, hbr]
    have hdiff : b₀ - star b₀ = -root⁻¹ := by
      rw [hbbar, ← hbr, mul_sub, mul_one, neg_sub]
    have hmiddle : 1 + root⁻¹ * b₀⁻¹ = (r : E) := by
      rw [← hbr, mul_comm b₀, mul_assoc, mul_inv_cancel₀ hb0, mul_one,
        add_comm, sub_add_cancel]
    refine ⟨Units.mk0 b₀ hb0, ?_, ?_, ?_⟩
    · rfl
    · change j b₀ - antiValue σ.anti (j b₀) = -((q : B)⁻¹)
      rw [hbarj, ← map_sub, hdiff, map_neg, map_inv₀, hjroot]
    · change 1 + (q : B)⁻¹ * (j b₀)⁻¹ = j (r : E)
      simpa only [map_add, map_mul, map_inv₀, map_one, hjroot] using congrArg j hmiddle
  · intro d hdsc
    have hd_im : (d : E).im ≠ 0 := by
      intro hz
      exact hdsc ⟨(d : E).re, by simpa [hz] using (hexpand (d : E)).symm⟩
    let c : F := -((2 * (d : E).im) * a)⁻¹
    have hc : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (mul_ne_zero h2 hd_im) ha_ne))
    have hstar_scalar (z : F) : star (algebraMap F E z) = algebraMap F E z := by
      apply QuadraticAlgebra.ext
      · change z + 0 * 0 = z
        simp
      · change -(0 : F) = 0
        simp
    have hh : algebraMap F E c * (d : E) - star (algebraMap F E c * (d : E)) = -root⁻¹ := by
      rw [star_mul, hstar_scalar, mul_comm (star (d : E)), ← mul_sub, sub_star]
      change algebraMap F E c * ((d : E).im • (root - star root)) = -root⁻¹
      rw [hroot_star, sub_neg_eq_add, ← two_mul, Algebra.smul_def]
      have ht : (2 : E) = algebraMap F E (2 : F) := (map_ofNat _ _).symm
      rw [ht, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul]
      apply mul_right_cancel₀ hroot_ne
      rw [mul_assoc, ← pow_two, hroot_sq, ← map_mul, neg_mul root⁻¹, inv_mul_cancel₀ hroot_ne]
      have hcprod : c * (d : E).im * 2 * a = -1 := by
        rw [mul_assoc c, mul_comm (d : E).im 2, mul_assoc, show c = -((2 * (d : E).im) * a)⁻¹ from rfl,
          neg_mul, inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero h2 hd_im) ha_ne)]
      rw [hcprod, map_neg, map_one]
    refine ⟨Units.mk0 c hc, ?_⟩
    change j (algebraMap F E c * (d : E)) - antiValue σ.anti (j (algebraMap F E c * (d : E))) =
      -((q : B)⁻¹)
    rw [hbarj, ← map_sub, hh, map_neg, map_inv₀, hjroot]

end QuadraticLine

section RightPairing

open Specs.Arithmetic.NontrialitarianSpinModels (SkewHermitianPairing)

variable {F B V : Type u} [Field F] [DivisionRing B] [Algebra F B]
  [AddCommGroup V] [Module Bᵐᵒᵖ V]
  {σ : Involution F B} (h : SkewHermitianPairing (V := V) σ)

local notation "bar" => antiValue σ.anti
local notation "⟪" x ", " y "⟫" => h.value x y

private theorem pairing_zero_right (x : V) : ⟪x, 0⟫ = 0 := by
  simpa using h.smul_right x x 0

private theorem pairing_zero_left (y : V) : ⟪0, y⟫ = 0 := by
  rw [h.skew y 0, pairing_zero_right]
  simp [antiValue]

private theorem pairing_add_left (x y z : V) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  rw [h.skew z (x + y), h.add_right, bar_add, neg_add, ← h.skew z x, ← h.skew z y]

private theorem pairing_smul_left (x y : V) (a : B) :
    ⟪op a • x, y⟫ = bar a * ⟪x, y⟫ := by
  rw [h.skew y (op a • x), h.smul_right, conjugate_mul, ← mul_neg, ← h.skew y x]

private theorem pairing_neg_right (x y : V) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  simpa using h.smul_right x y (-1)

private theorem pairing_neg_left (x y : V) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  simpa [antiValue] using pairing_smul_left h x y (-1)

private theorem pairing_sub_right (x y z : V) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp only [sub_eq_add_neg, h.add_right, pairing_neg_right]

private theorem pairing_sub_left (x y z : V) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp only [sub_eq_add_neg, pairing_add_left, pairing_neg_left]

private theorem scalar_two_ne_zero (h2 : (2 : F) ≠ 0) : (2 : B) ≠ 0 := by
  intro hz
  apply h2
  apply (algebraMap F B).injective
  simpa only [map_ofNat, map_zero] using hz

private theorem exists_nonzero_self_pairing (h2 : (2 : F) ≠ 0) (hB : isCentralSimple F B)
    (hd : degree F B = 2) (hσ : ∀ x, bar x = quaternionConjugate hB x)
    (hv : ∃ v : V, v ≠ 0) : ∃ w, ⟪w, w⟫ ≠ 0 := by
  obtain ⟨v, hv⟩ := hv
  obtain ⟨w, hvw⟩ := h.nondegenerate v hv
  by_contra! hzero
  have hfixed (x y : V) : bar ⟪x, y⟫ = ⟪x, y⟫ := by
    have hz := hzero (x + y)
    rw [pairing_add_left, h.add_right, h.add_right, hzero, hzero, zero_add, add_zero,
      h.skew x y, ← sub_eq_add_neg] at hz
    exact (sub_eq_zero.mp hz).symm
  have hnonscalar : ∃ b : B, b ∉ Set.range (algebraMap F B) := by
    by_contra! hall
    let e := AlgEquiv.ofBijective (Algebra.ofId F B) ⟨(algebraMap F B).injective, hall⟩
    have he := e.toLinearEquiv.finrank_eq
    have hd' : RM03.CSA.degree F B = 2 := hd
    rw [Module.finrank_self, RM03.CSA.finrank_eq_degree_sq hB, hd'] at he
    norm_num at he
  obtain ⟨b, hb⟩ := hnonscalar
  obtain ⟨t, ht⟩ := scalar_of_bar_fixed σ hB hσ h2 (hfixed v w)
  obtain ⟨s, hs⟩ := scalar_of_bar_fixed σ hB hσ h2 (hfixed v (op b • w))
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hvw (by simpa using ht.symm)
  apply hb
  refine ⟨t⁻¹ * s, ?_⟩
  rw [map_mul, hs, h.smul_right, ← ht, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ ht0, map_one, one_mul]

private def lineCoefficients (w : V) : V →ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun x := op (⟪w, w⟫⁻¹ * ⟪w, x⟫)
  map_add' x y := by
    change op (⟪w, w⟫⁻¹ * ⟪w, x + y⟫) = op (_ * ⟪w, x⟫) + op (_ * ⟪w, y⟫)
    rw [h.add_right, mul_add, op_add]
  map_smul' a x := by
    change op (⟪w, w⟫⁻¹ * ⟪w, op a.unop • x⟫) = a * op (_ * ⟪w, x⟫)
    rw [h.smul_right, ← mul_assoc, op_mul, op_unop]

private abbrev lineInclusion (w : V) : Bᵐᵒᵖ →ₗ[Bᵐᵒᵖ] V :=
  LinearMap.toSpanSingleton Bᵐᵒᵖ V w

private theorem lineCoefficients_inclusion (w : V) (hw : ⟪w, w⟫ ≠ 0) (a : Bᵐᵒᵖ) :
    lineCoefficients h w (lineInclusion w a) = a := by
  change op (⟪w, w⟫⁻¹ * ⟪w, op a.unop • w⟫) = a
  rw [h.smul_right, ← mul_assoc, inv_mul_cancel₀ hw, one_mul, op_unop]

private def complementProjection (w : V) (hw : ⟪w, w⟫ ≠ 0) :
    V →ₗ[Bᵐᵒᵖ] (lineCoefficients h w).ker :=
  (LinearMap.id - (lineInclusion w).comp (lineCoefficients h w)).codRestrict _
    (fun x => LinearMap.mem_ker.mpr (by
      change lineCoefficients h w (x - lineInclusion w (lineCoefficients h w x)) = 0
      rw [map_sub, lineCoefficients_inclusion h w hw, sub_self]))

private theorem complementProjection_apply (w : V) (hw : ⟪w, w⟫ ≠ 0) (x : V) :
    ((complementProjection h w hw x : (lineCoefficients h w).ker) : V) =
      x - lineCoefficients h w x • w := rfl

private def splitLine (w : V) (hw : ⟪w, w⟫ ≠ 0) :
    V ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ × (lineCoefficients h w).ker :=
  let f := (lineCoefficients h w).prod (complementProjection h w hw)
  { toFun := f
    map_add' := f.map_add
    map_smul' := f.map_smul
    invFun := fun p => p.1 • w + p.2.val
    left_inv := by
      intro x
      change lineCoefficients h w x • w + (x - lineCoefficients h w x • w) = x
      abel
    right_inv := by
      rintro ⟨a, x⟩
      have hx : lineCoefficients h w (x : V) = 0 := x.property
      have he : lineCoefficients h w (a • w + (x : V)) = a := by
        change lineCoefficients h w (lineInclusion w a + (x : V)) = a
        rw [map_add, lineCoefficients_inclusion h w hw a, hx, add_zero]
      apply Prod.ext
      · exact he
      · apply Subtype.ext
        change (a • w + (x : V)) - lineCoefficients h w (a • w + (x : V)) • w = x
        rw [he]
        abel }

private theorem splitLine_symm_apply (w : V) (hw : ⟪w, w⟫ ≠ 0)
    (a : Bᵐᵒᵖ) (x : (lineCoefficients h w).ker) :
    (splitLine h w hw).symm (a, x) = a • w + (x : V) := rfl

private theorem pairing_of_mem_complement (w : V) (hw : ⟪w, w⟫ ≠ 0)
    (x : (lineCoefficients h w).ker) : ⟪w, x⟫ = 0 := by
  have hx : op (⟪w, w⟫⁻¹ * ⟪w, x⟫) = 0 := x.property
  exact (mul_eq_zero.mp (op_injective hx)).resolve_left (inv_ne_zero hw)

private theorem pairing_of_mem_complement_left (w : V) (hw : ⟪w, w⟫ ≠ 0)
    (x : (lineCoefficients h w).ker) : ⟪x, w⟫ = 0 := by
  rw [h.skew w x, pairing_of_mem_complement h w hw x]
  simp [antiValue]

private theorem conjugate_neg (a : B) : bar (-a) = -bar a := by simp [antiValue]
private theorem conjugate_one : bar (1 : B) = 1 := by simp [antiValue]
private theorem bar_sub (a b : B) : bar (a - b) = bar a - bar b := by simp [antiValue]

private theorem isometry_of_lineRotation {g : V ≃ₗ[Bᵐᵒᵖ] V}
    (hg : IsLineRotation h g) : ∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫ := by
  obtain ⟨w, r, hw, hcomm, hnorm, hformula⟩ := hg
  intro x y
  let q := ⟪w, w⟫
  let cx := q⁻¹ * ⟪w, x⟫
  let cy := q⁻¹ * ⟪w, y⟫
  let k := (r.val - 1) * cx
  let l := (r.val - 1) * cy
  have hx : ⟪w, x⟫ = q * cx := by dsimp [cx]; rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
  have hy : ⟪w, y⟫ = q * cy := by dsimp [cy]; rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
  have hqx : bar q = -q := by simpa [q] using (congrArg Neg.neg (h.skew w w)).symm
  have hx' : ⟪x, w⟫ = bar cx * q := by rw [h.skew w x, hx, conjugate_mul, hqx, mul_neg, neg_neg]
  have hbar : bar (r.val - 1) = bar r.val - 1 := by rw [bar_sub, conjugate_one]
  have hnr : bar r.val * q * r.val = q := by
    rw [mul_assoc, ← hcomm.eq, ← mul_assoc, hnorm, one_mul]
  rw [hformula x, hformula y]
  simp only [mul_assoc]
  change ⟪x + op k • w, y + op l • w⟫ = ⟪x, y⟫
  simp only [pairing_add_left, h.add_right, pairing_smul_left, h.smul_right, hx', hy, add_mul]
  change ⟪x, y⟫ + bar k * (q * cy) + (bar cx * q * l + bar k * q * l) = ⟪x, y⟫
  have hzero : bar k * (q * cy) + (bar cx * q * l + bar k * q * l) =
      bar cx * (bar r.val * q * r.val - q) * cy := by
    simp only [k, l, conjugate_mul σ, hbar]
    noncomm_ring
  rw [add_assoc, hzero, hnr, sub_self, mul_zero, zero_mul, add_zero]

private def rotation (w : V) (hw : ⟪w, w⟫ ≠ 0) (r : Bˣ) : V ≃ₗ[Bᵐᵒᵖ] V :=
  let e := splitLine h w hw
  (e.trans (((Units.opEquiv.symm (op r)).mulRightLinearEquiv Bᵐᵒᵖ).prodCongr
    (LinearEquiv.refl _ _))).trans e.symm

private theorem rotation_apply (w : V) (hw : ⟪w, w⟫ ≠ 0) (r : Bˣ) (x : V) :
    rotation h w hw r x = x + op ((r.val - 1) * ⟪w, w⟫⁻¹ * ⟪w, x⟫) • w := by
  let a := ⟪w, w⟫⁻¹ * ⟪w, x⟫
  change (op a * op r.val) • w + (x - op a • w) = x + op ((r.val - 1) * _ * _) • w
  rw [mul_assoc, sub_mul, one_mul, op_sub, ← op_mul, sub_smul]
  abel

private theorem rotation_isLineRotation (w : V) (hw : ⟪w, w⟫ ≠ 0) (r : Bˣ)
    (hr : Commute r.val ⟪w, w⟫) (hn : bar r.val * r.val = 1) :
    IsLineRotation h (rotation h w hw r) :=
  ⟨w, r, hw, hr, hn, rotation_apply h w hw r⟩

private theorem commute_bar (hB : isCentralSimple F B)
    (hσ : ∀ x, bar x = quaternionConjugate hB x) (x : B) :
    Commute x (bar x) := by
  obtain ⟨z, hz⟩ := trace_scalar σ hB hσ x
  rw [show bar x = algebraMap F B z - x from eq_sub_of_add_eq (by rw [add_comm, hz])]
  exact Commute.sub_right (Algebra.commutes z x).symm (Commute.refl x)

private theorem bar_inv (a : B) : bar a⁻¹ = (bar a)⁻¹ := by simp [antiValue, map_inv₀]

private def rotationGroup : Subgroup (V ≃ₗ[Bᵐᵒᵖ] V) :=
  Subgroup.closure {g | IsLineRotation h g}

private def isometryGroup : Subgroup (V ≃ₗ[Bᵐᵒᵖ] V) where
  carrier := {g | ∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro g k hg hk x y
    exact (hg (k x) (k y)).trans (hk x y)
  inv_mem' := by
    intro g hg x y
    simpa using (hg (g.symm x) (g.symm y)).symm

private theorem rotationGroup_le_isometryGroup : rotationGroup h ≤ isometryGroup h :=
  (Subgroup.closure_le (isometryGroup h)).mpr (fun _ hg => isometry_of_lineRotation h hg)

private theorem rotation_to_equal_norm (hB : isCentralSimple F B)
    (hσ : ∀ x, bar x = quaternionConjugate hB x) (u v : V)
    (huv : ⟪u, u⟫ = ⟪v, v⟫) (hz : ⟪u - v, u - v⟫ ≠ 0) :
    ∃ g ∈ rotationGroup h, g u = v := by
  let z := u - v
  let c := ⟪z, u⟫
  have hcv : ⟪z, v⟫ = bar c := by
    have huu : bar ⟪u, u⟫ = -⟪u, u⟫ := by
      simpa using (congrArg Neg.neg (h.skew u u)).symm
    rw [show z = u - v from rfl, pairing_sub_left]
    change ⟪u, v⟫ - ⟪v, v⟫ = bar ⟪u - v, u⟫
    rw [pairing_sub_left, bar_sub, huu, ← neg_eq_iff_eq_neg.mpr (h.skew v u), ← huv]
    abel
  have hzq : ⟪z, z⟫ = c - bar c := by
    change ⟪z, u - v⟫ = _
    rw [pairing_sub_right, hcv]
  have hc : c ≠ 0 := by
    intro hc
    apply hz
    rw [hzq, hc]
    simp [antiValue]
  have hbc : bar c ≠ 0 := by
    intro hc0
    apply hc
    rw [← σ.square c, hc0]
    simp [antiValue]
  let r := c⁻¹ * bar c
  let ur := Units.mk0 r (mul_ne_zero (inv_ne_zero hc) hbc)
  have hcomm : Commute c (bar c) := commute_bar (σ := σ) hB hσ c
  have hinv : Commute (bar c)⁻¹ c⁻¹ := hcomm.symm.inv_left₀.inv_right₀
  have hrcomm : Commute r ⟪z, z⟫ := by
    rw [hzq]
    exact ((Commute.refl c).sub_right hcomm).inv_left₀.mul_left
      (hcomm.symm.sub_right (Commute.refl (bar c)))
  have hrnorm : bar r * r = 1 := by
    simp only [r, conjugate_mul, bar_inv]
    rw [σ.square c, mul_assoc c, ← mul_assoc (bar c)⁻¹ c⁻¹,
      hinv.eq, ← mul_assoc c, ← mul_assoc c,
      mul_inv_cancel₀ hc, one_mul, inv_mul_cancel₀ hbc]
  refine ⟨rotation h z hz ur, Subgroup.subset_closure
    (rotation_isLineRotation h z hz ur hrcomm hrnorm), ?_⟩
  rw [rotation_apply]
  change u + op ((r - 1) * ⟪z, z⟫⁻¹ * c) • z = v
  have hrsub : r - 1 = -(c⁻¹ * ⟪z, z⟫) := by
    rw [hzq, mul_sub, inv_mul_cancel₀ hc, neg_sub]
  rw [hrsub, neg_mul, mul_assoc c⁻¹, mul_inv_cancel₀ hz, mul_one, neg_mul,
    inv_mul_cancel₀ hc, op_neg, op_one, neg_smul, one_smul]
  dsimp [z]
  abel

private theorem rotation_word_to_equal_norm (h2 : (2 : F) ≠ 0) (hB : isCentralSimple F B)
    (hσ : ∀ x, bar x = quaternionConjugate hB x) (u v : V)
    (huv : ⟪u, u⟫ = ⟪v, v⟫) (hu : ⟪u, u⟫ ≠ 0) :
    ∃ g ∈ rotationGroup h, g u = v := by
  by_cases hm : ⟪u - v, u - v⟫ ≠ 0
  · exact rotation_to_equal_norm h hB hσ u v huv hm
  have hp : ⟪u + v, u + v⟫ ≠ 0 := by
    have he : ⟪u - v, u - v⟫ + ⟪u + v, u + v⟫ = (2 : B) * (2 * ⟪u, u⟫) := by
      simp only [pairing_sub_left, pairing_sub_right, pairing_add_left, h.add_right, ← huv, two_mul]
      abel
    intro hp0
    rw [not_ne_iff.mp hm, hp0, add_zero] at he
    have h2B := scalar_two_ne_zero (B := B) h2
    exact mul_ne_zero h2B (mul_ne_zero h2B hu) he.symm
  have hneg : ⟪-v, -v⟫ = ⟪v, v⟫ := by rw [pairing_neg_left, pairing_neg_right, neg_neg]
  obtain ⟨g, hg, hgu⟩ := rotation_to_equal_norm h hB hσ u (-v) (huv.trans hneg.symm)
    (by simpa only [sub_neg_eq_add] using hp)
  have hv : ⟪v, v⟫ ≠ 0 := huv ▸ hu
  let r : Bˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  have hr : Commute r.val ⟪v, v⟫ := (Commute.one_left _).neg_left
  have hn : bar r.val * r.val = 1 := by
    change bar (-1) * -1 = 1
    simp only [conjugate_neg, conjugate_one, neg_mul_neg, one_mul]
  let k := rotation h v hv r
  have hkv : k (-v) = v := by
    rw [show k (-v) = rotation h v hv r (-v) from rfl, rotation_apply, pairing_neg_right]
    change -v + op (((-1 : B) - 1) * ⟪v, v⟫⁻¹ * -⟪v, v⟫) • v = v
    rw [mul_assoc, mul_neg, inv_mul_cancel₀ hv, mul_neg_one, neg_sub, sub_neg_eq_add,
      op_add, op_one, add_smul, one_smul]
    abel
  exact ⟨k * g, (rotationGroup h).mul_mem (Subgroup.subset_closure
    (rotation_isLineRotation h v hv r hr hn)) hg, by rw [LinearEquiv.mul_apply, hgu, hkv]⟩

private def complementPairing (w : V) (hw : ⟪w, w⟫ ≠ 0) :
    SkewHermitianPairing (V := (lineCoefficients h w).ker) σ where
  value x y := ⟪x, y⟫
  add_right x y z := h.add_right x y z
  smul_right x y a := h.smul_right x y a
  skew x y := h.skew x y
  nondegenerate := by
    intro x hx
    have hx0 : (x : V) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    obtain ⟨y, hxy⟩ := h.nondegenerate x hx0
    refine ⟨complementProjection h w hw y, ?_⟩
    rw [complementProjection_apply, pairing_sub_right, ← op_unop (lineCoefficients h w y),
      h.smul_right, pairing_of_mem_complement_left h w hw x, zero_mul, sub_zero]
    exact hxy

private def extendComplement (w : V) (hw : ⟪w, w⟫ ≠ 0) :
    ((lineCoefficients h w).ker ≃ₗ[Bᵐᵒᵖ] (lineCoefficients h w).ker) →*
      (V ≃ₗ[Bᵐᵒᵖ] V) where
  toFun g :=
    let e := splitLine h w hw
    (e.trans ((LinearEquiv.refl Bᵐᵒᵖ Bᵐᵒᵖ).prodCongr g)).trans e.symm
  map_one' := by ext1 x; simp
  map_mul' g k := by ext1 x; simp

private theorem extendComplement_apply (w : V) (hw : ⟪w, w⟫ ≠ 0)
    (g : (lineCoefficients h w).ker ≃ₗ[Bᵐᵒᵖ] (lineCoefficients h w).ker) (x : V) :
    extendComplement h w hw g x =
      lineCoefficients h w x • w + (g (complementProjection h w hw x) : V) := rfl

private theorem extendComplement_mem_rotationGroup (w : V) (hw : ⟪w, w⟫ ≠ 0)
    (g : (lineCoefficients h w).ker ≃ₗ[Bᵐᵒᵖ] (lineCoefficients h w).ker)
    (hg : g ∈ rotationGroup (complementPairing h w hw)) :
    extendComplement h w hw g ∈ rotationGroup h := by
  have hle : rotationGroup (complementPairing h w hw) ≤
      (rotationGroup h).comap (extendComplement h w hw) := by
    apply (Subgroup.closure_le _).mpr
    rintro k ⟨z, r, hz, hr, hn, hk⟩
    apply Subgroup.subset_closure
    refine ⟨z.val, r, hz, hr, hn, fun x => ?_⟩
    rw [extendComplement_apply, hk]
    change lineCoefficients h w x • w + ((complementProjection h w hw x : V) +
      op ((r.val - 1) * ⟪z, z⟫⁻¹ * ⟪z, (complementProjection h w hw x : V)⟫) • (z : V)) = _
    rw [complementProjection_apply, pairing_sub_right, ← op_unop (lineCoefficients h w x),
      h.smul_right, pairing_of_mem_complement_left h w hw z, zero_mul, sub_zero]
    abel
  exact hle hg

private theorem fixedLine_isometry_mem_rotationGroup (w : V) (hw : ⟪w, w⟫ ≠ 0)
    (g : V ≃ₗ[Bᵐᵒᵖ] V) (hg : g ∈ isometryGroup h) (hgw : g w = w)
    (ih : ∀ k, k ∈ isometryGroup (complementPairing h w hw) →
      k ∈ rotationGroup (complementPairing h w hw)) :
    g ∈ rotationGroup h := by
  have hg' : ∀ x y, ⟪g x, g y⟫ = ⟪x, y⟫ := hg
  have hcoeff (x : V) : lineCoefficients h w (g x) = lineCoefficients h w x := by
    have he := hg' w x
    rw [hgw] at he
    change op (⟪w, w⟫⁻¹ * ⟪w, g x⟫) = op (⟪w, w⟫⁻¹ * ⟪w, x⟫)
    rw [he]
  let C := (lineCoefficients h w).ker
  let k : C ≃ₗ[Bᵐᵒᵖ] C :=
    { g.toLinearMap.restrict (fun x hx => LinearMap.mem_ker.mpr
        ((hcoeff x).trans (LinearMap.mem_ker.mp hx))) with
      invFun := fun x => ⟨g.symm x, LinearMap.mem_ker.mpr
        ((hcoeff (g.symm x)).symm.trans (by simp [LinearMap.mem_ker.mp x.property]))⟩
      left_inv := fun x => Subtype.ext (g.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (g.apply_symm_apply x) }
  have hk : k ∈ isometryGroup (complementPairing h w hw) := fun x y => hg' x y
  have hkg : extendComplement h w hw k = g := by
    ext1 x
    rw [extendComplement_apply]
    change lineCoefficients h w x • w + g (complementProjection h w hw x : V) = g x
    rw [complementProjection_apply, map_sub, map_smul, hgw]
    abel
  rw [← hkg]
  exact extendComplement_mem_rotationGroup h w hw k (ih k hk)

private theorem isometry_mem_rotationGroup (h2 : (2 : F) ≠ 0) (hB : isCentralSimple F B)
    (hd : degree F B = 2) (hσ : ∀ x, bar x = quaternionConjugate hB x) (n : ℕ) :
    ∀ {M : Type u} [AddCommGroup M] [Module Bᵐᵒᵖ M] [Module.Finite Bᵐᵒᵖ M]
      (p : SkewHermitianPairing (V := M) σ), Module.finrank Bᵐᵒᵖ M = n →
      ∀ g, g ∈ isometryGroup p → g ∈ rotationGroup p := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro M _ _ _ p hn g hg
    by_cases hnz : ∃ v : M, v ≠ 0
    · obtain ⟨w, hw⟩ := exists_nonzero_self_pairing p h2 hB hd hσ hnz
      have hg' : ∀ x y, p.value (g x) (g y) = p.value x y := hg
      obtain ⟨j, hj, hjw⟩ := rotation_word_to_equal_norm p h2 hB hσ (g w) w (hg' w w)
        (by rwa [hg' w w])
      have hlt : Module.finrank Bᵐᵒᵖ (lineCoefficients p w).ker < n := by
        rw [← hn]
        apply Submodule.finrank_lt
        intro he
        have hzero : lineCoefficients p w w = 0 := LinearMap.mem_ker.mp (by rw [he]; trivial)
        have hone := lineCoefficients_inclusion p w hw 1
        rw [LinearMap.toSpanSingleton_apply, one_smul, hzero] at hone
        exact zero_ne_one hone
      have hjg := fixedLine_isometry_mem_rotationGroup p w hw (j * g)
        ((isometryGroup p).mul_mem (rotationGroup_le_isometryGroup p hj) hg) hjw
        (ih _ hlt (complementPairing p w hw) rfl)
      simpa only [inv_mul_cancel_left] using (rotationGroup p).mul_mem
        ((rotationGroup p).inv_mem hj) hjg
    · simp only [not_exists, not_not] at hnz
      have hg1 : g = 1 := LinearEquiv.ext fun x => (hnz (g x)).trans (hnz x).symm
      exact hg1 ▸ (rotationGroup p).one_mem

private theorem perpendicular_rotation_generation : PerpendicularRotationGeneration.{u} := by
  intro F B V _ _ _ _ _ _ h2 hB hd σ hσ h
  refine ⟨exists_nonzero_self_pairing h h2 hB hd hσ, fun g => ?_⟩
  change g ∈ isometryGroup h ↔ g ∈ rotationGroup h
  exact ⟨isometry_mem_rotationGroup h2 hB hd hσ _ h rfl g, fun hg => rotationGroup_le_isometryGroup h hg⟩

end RightPairing


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MulOpposite
open scoped Matrix TensorProduct CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel SkewHermitianPairing QuaternionSpinIsotropy)
open Specs.Arithmetic.QuaternionSpinScaleCover
  (QuaternionHyperbolicPresentation quaternionHyperbolicGram QuaternionPairIndex)
open Specs.SymplecticDivisionForms (hermitianValue)
open Specs.CharacterDescent (Cocharacter)
open Specs.Arithmetic.OppositeRadicals (IsNoncentral)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

open private matrixBaseChange matrixBaseChange_tmul extendEquiv extendEquiv_tmul
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

section AdaptedBasis

variable {F B V : Type u} [Field F] [DivisionRing B] [Algebra F B]
  [AddCommGroup V] [Module Bᵐᵒᵖ V] {σ : Involution F B}
  (h : SkewHermitianPairing (V := V) σ)

private def pairingRightLinear (w : V) : V →ₗ[Bᵐᵒᵖ] B where
  toFun := h.value w
  map_add' := h.add_right w
  map_smul' a x := by
    change h.value w (op a.unop • x) = h.value w x * a.unop
    exact h.smul_right w x a.unop

private def planeCoefficients (e f : V) : V →ₗ[Bᵐᵒᵖ] (Fin 2 → B) :=
  LinearMap.pi ![-pairingRightLinear h f, pairingRightLinear h e]

private def planeEmbedding (e f : V) : (Fin 2 → B) →ₗ[Bᵐᵒᵖ] V where
  toFun x := op (x 0) • e + op (x 1) • f
  map_add' x y := by
    change op (x 0 + y 0) • e + op (x 1 + y 1) • f =
      (op (x 0) • e + op (x 1) • f) + (op (y 0) • e + op (y 1) • f)
    have h0 : op (x 0 + y 0) = op (x 0) + op (y 0) := MulOpposite.op_add _ _
    have h1 : op (x 1 + y 1) = op (x 1) + op (y 1) := MulOpposite.op_add _ _
    rw [h0, h1, add_smul, add_smul]
    abel
  map_smul' a x := by
    change op (x 0 * a.unop) • e + op (x 1 * a.unop) • f =
      a • (op (x 0) • e + op (x 1) • f)
    simp only [smul_add, op_mul, op_unop, mul_smul]

private theorem planeCoefficients_section (e f : V)
    (hee : h.value e e = 0) (hef : h.value e f = 1)
    (hfe : h.value f e = -1) (hff : h.value f f = 0) (a : Fin 2 → B) :
    planeCoefficients h e f (planeEmbedding e f a) = a := by
  ext i
  fin_cases i
  · change -h.value f (op (a 0) • e + op (a 1) • f) = a 0
    rw [h.add_right, h.smul_right, h.smul_right, hfe, hff]
    simp
  · change h.value e (op (a 0) • e + op (a 1) • f) = a 1
    rw [h.add_right, h.smul_right, h.smul_right, hee, hef]
    simp

private def splitLinearSection {R M N : Type u} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : Function.RightInverse s f) :
    M ≃ₗ[R] N × f.ker :=
  let p := (LinearMap.id - s.comp f).codRestrict f.ker
    (fun x => LinearMap.mem_ker.mpr (by
      change f (x - s (f x)) = 0
      rw [map_sub, hs (f x), sub_self]))
  let l := f.prod p
  { toFun := l
    map_add' := l.map_add
    map_smul' := l.map_smul
    invFun := fun x => s x.1 + x.2.val
    left_inv := by
      intro x
      change s (f x) + (x - s (f x)) = x
      abel
    right_inv := by
      rintro ⟨a, x⟩
      have hx : f (x : M) = 0 := x.property
      have hf : f (s a + x) = a := by rw [map_add, hs a, hx, add_zero]
      apply Prod.ext
      · exact hf
      · apply Subtype.ext
        change (s a + (x : M)) - s (f (s a + x)) = x
        rw [hf]
        abel }

private theorem planeCoefficients_orthogonal (e f : V) (x : (planeCoefficients h e f).ker) :
    h.value e x = 0 ∧ h.value f x = 0 := by
  have hx : planeCoefficients h e f x.val = 0 := x.property
  constructor
  · exact congrFun hx 1
  · exact neg_eq_zero.mp (congrFun hx 0)

end AdaptedBasis

section Matrices

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

private def columnMatrix (f : (n → B) →ₗ[Bᵐᵒᵖ] (m → B)) : Matrix m n B :=
  Matrix.of fun i j => f (Pi.single j 1) i

omit [Fintype m] [DecidableEq m] in
private theorem columnMatrix_mulVec (f : (n → B) →ₗ[Bᵐᵒᵖ] (m → B)) (x : n → B) :
    columnMatrix f *ᵥ x = f x := by
  have hx : ∑ j : n, op (x j) • (Pi.single j 1 : n → B) = x := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [Pi.smul_apply]
    · intro j _ hj
      simp [Pi.smul_apply, Pi.single_eq_of_ne hj.symm]
    · simp
  ext i
  conv_rhs => rw [← hx, map_sum]
  simp [columnMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, map_smul]

private theorem rectangular_left_inverse
    (e : (n → B) ≃ₗ[Bᵐᵒᵖ] (m → B)) :
    columnMatrix e.symm.toLinearMap * columnMatrix e.toLinearMap = 1 := by
  apply Matrix.mulVec_injective
  funext x
  simp only [← Matrix.mulVec_mulVec, columnMatrix_mulVec, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Matrix.one_mulVec]

private def changeMatrixCoordinates (p : Matrix n m B) (q : Matrix m n B)
    (hpq : p * q = 1) (hqp : q * p = 1) : Matrix m m B ≃ₐ[F] Matrix n n B where
  toFun x := p * x * q
  invFun x := q * x * p
  left_inv x := by
    calc
      q * (p * x * q) * p = (q * p) * x * (q * p) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hqp, Matrix.one_mul, Matrix.mul_one]
  right_inv x := by
    calc
      p * (q * x * p) * q = (p * q) * x * (p * q) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hpq, Matrix.one_mul, Matrix.mul_one]
  map_mul' x y := by
    change p * (x * y) * q = (p * x * q) * (p * y * q)
    conv_rhs =>
      rw [show (p * x * q) * (p * y * q) = p * x * (q * p) * y * q by
        simp only [Matrix.mul_assoc]]
    rw [hqp, Matrix.mul_one, Matrix.mul_assoc p x y]
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' t := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hpq]

end Matrices

section GroupComparison

private theorem cocharacter_ne_zero_of_noncentral {F : Type u} [Field F]
    {G : Specs.GroupScheme F} (c : Cocharacter G) (hc : IsNoncentral c) : c ≠ 0 := by
  rintro rfl
  obtain ⟨X, g, hg⟩ := hc
  apply hg
  have h : CategoryTheory.CartesianMonoidalCategory.fst
      ((specGroup
        (Specs.DiagonalizableGroups.groupAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)).X) X ≫
      (0 : Cocharacter G).hom.hom = 1 := by
    rw [Grp.zero_hom, Mon.zero_hom]
    simp
    rfl
  simp only [Centralizes, conjugateFamily, h, mul_one, mul_inv_cancel]

private noncomputable def selfGroupBaseChange (F : Type u) [Field F] :
    groupBaseChange F F ≅ 𝟭 _ := by
  have hb : fieldSpecMap F F = 𝟙 _ := Spec.map_id _
  let P (b : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F)) := Over.pullback b
  let e : baseChange F F ≅ 𝟭 _ := eqToIso (congrArg P hb) ≪≫ Over.pullbackId
  exact Functor.mapGrpNatIso e ≪≫ Functor.mapGrpIdIso

end GroupComparison

section HyperbolicMatrices

open LinearAlgebraicGroups.QuaternionHermitianCocharacters (adjoint adjoint_mul adjoint_one)

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
  {σ : Involution F B}

private def rightCoordinates : B ≃ₗ[Bᵐᵒᵖ] Bᵐᵒᵖ where
  toFun := op
  invFun := unop
  map_add' := op_add
  map_smul' a b := by
    change op (b * a.unop) = a * op b
    rw [op_mul, op_unop]
  left_inv := unop_op
  right_inv := op_unop

private theorem finrank_right_columns (J : Type*) [Fintype J] :
    Module.finrank Bᵐᵒᵖ (J → B) = Fintype.card J := by
  rw [← show Module.finrank Bᵐᵒᵖ (J → Bᵐᵒᵖ) = Fintype.card J by
    simp]
  exact (LinearEquiv.piCongrRight fun _ : J => rightCoordinates (B := B)).finrank_eq

private theorem gram_matrix_apply {m n : Type*} [Fintype m]
    (H : Matrix m m B) (q : Matrix m n B) (i j : n) :
    (adjoint σ.anti.toAlgHom q * H * q) i j =
      hermitianValue σ.anti H (fun k => q k i) (fun k => q k j) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hermitianValue, adjoint, antiValue]

private theorem block_complement_unit {d : ℕ} (W : Matrix (Fin d) (Fin d) B)
    (H : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ)
    (hH : H.val = quaternionHyperbolicGram W) :
    ∃ w : (Matrix (Fin d) (Fin d) B)ˣ, w.val = W := by
  have h₁ := H.val_inv
  have h₂ := H.inv_val
  let X := H.inv
  change H.val * X = 1 at h₁
  change X * H.val = 1 at h₂
  have hX := Matrix.fromBlocks_toBlocks X
  rw [hH, ← hX, quaternionHyperbolicGram, Matrix.fromBlocks_multiply] at h₁ h₂
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at h₁ h₂
  refine ⟨⟨W, X.toBlocks₂₂, ?_, ?_⟩, rfl⟩
  · simpa only [Matrix.toBlocks_fromBlocks₂₂, ← Matrix.fromBlocks_one] using
      congrArg Matrix.toBlocks₂₂ h₁
  · simpa only [Matrix.toBlocks_fromBlocks₂₂, ← Matrix.fromBlocks_one] using
      congrArg Matrix.toBlocks₂₂ h₂

private theorem adapted_quaternion_matrices {r : ℕ}
    (H : (Matrix (Fin r) (Fin r) B)ˣ)
    (h : SkewHermitianPairing (V := Fin r → B) σ)
    (hvalue : h.value = hermitianValue σ.anti H.val) (x y : Fin r → B)
    (hxx : h.value x x = 0) (hxy : h.value x y = 1)
    (hyx : h.value y x = -1) (hyy : h.value y y = 0) :
    ∃ (d : ℕ) (p : Matrix (QuaternionPairIndex d) (Fin r) B)
      (q : Matrix (Fin r) (QuaternionPairIndex d) B) (W : (Matrix (Fin d) (Fin d) B)ˣ),
      r = d + 2 ∧ p * q = 1 ∧ q * p = 1 ∧
      adjoint σ.anti.toAlgHom q * H.val * q = quaternionHyperbolicGram W.val := by
  classical
  let _ : Module.Finite Bᵐᵒᵖ B :=
    Module.Finite.of_surjective (rightCoordinates (B := B)).symm.toLinearMap
      (rightCoordinates (B := B)).symm.surjective
  let f := planeCoefficients h x y
  let s : (Fin 2 → B) →ₗ[Bᵐᵒᵖ] (Fin r → B) := planeEmbedding x y
  let b := splitLinearSection f s (planeCoefficients_section h x y hxx hxy hyx hyy)
  let d := Module.finrank Bᵐᵒᵖ f.ker
  let ec : f.ker ≃ₗ[Bᵐᵒᵖ] (Fin d → B) := (Module.finBasis Bᵐᵒᵖ f.ker).equivFun.trans
    (LinearEquiv.piCongrRight fun _ => rightCoordinates.symm)
  let e : (Fin r → B) ≃ₗ[Bᵐᵒᵖ] (QuaternionPairIndex d → B) :=
    (b.trans ((LinearEquiv.refl _ _).prodCongr ec)).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin d) Bᵐᵒᵖ B).symm
  let p := columnMatrix e.toLinearMap
  let q := columnMatrix e.symm.toLinearMap
  have hpq : p * q = 1 := rectangular_left_inverse e.symm
  have hqp : q * p = 1 := rectangular_left_inverse e
  have hd : r = d + 2 := by
    have he := e.finrank_eq
    rw [finrank_right_columns, finrank_right_columns, Fintype.card_fin,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, add_comm] at he
    exact he
  let M := adjoint σ.anti.toAlgHom q * H.val * q
  let W := M.toBlocks₂₂
  have hInv (z : QuaternionPairIndex d → B) :
      e.symm z = planeEmbedding x y (fun i => z (Sum.inl i)) +
        (ec.symm (fun j => z (Sum.inr j)) : Fin r → B) := rfl
  have hleft (i : Fin 2) :
      (fun k => q k (Sum.inl i)) = ![x, y] i := by
    change e.symm (Pi.single (Sum.inl i) 1) = _
    rw [hInv]
    have hl : (fun j : Fin 2 => (Pi.single (Sum.inl i) (1 : B) : QuaternionPairIndex d → B)
          (Sum.inl j)) = Pi.single i 1 := by
      ext j
      simp [Pi.single_apply]
    have hr : (fun j : Fin d => (Pi.single (Sum.inl i) (1 : B) : QuaternionPairIndex d → B)
          (Sum.inr j)) = 0 := by
      ext j
      simp
    rw [hl, hr, map_zero, Submodule.coe_zero, add_zero]
    fin_cases i
    · change op ((Pi.single (0 : Fin 2) (1 : B) : Fin 2 → B) 0) • x +
        op ((Pi.single (0 : Fin 2) (1 : B) : Fin 2 → B) 1) • y = x
      simp
    · change op ((Pi.single (1 : Fin 2) (1 : B) : Fin 2 → B) 0) • x +
        op ((Pi.single (1 : Fin 2) (1 : B) : Fin 2 → B) 1) • y = y
      simp
  have hright (j : Fin d) :
      ∃ z : f.ker, (fun k => q k (Sum.inr j)) = z.val := by
    change ∃ z : f.ker, e.symm (Pi.single (Sum.inr j) 1) = z.val
    let v : Fin d → B := fun i =>
      (Pi.single (Sum.inr j) (1 : B) : QuaternionPairIndex d → B) (Sum.inr i)
    refine ⟨ec.symm v, ?_⟩
    rw [hInv]
    have hl : (fun i : Fin 2 =>
        (Pi.single (Sum.inr j) (1 : B) : QuaternionPairIndex d → B) (Sum.inl i)) = 0 := by
      ext i
      simp
    rw [hl, map_zero, zero_add]
  have hM : M = quaternionHyperbolicGram W := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · change M (Sum.inl i) (Sum.inl j) = !![0, 1; -1, 0] i j
      rw [show M = adjoint σ.anti.toAlgHom q * H.val * q from rfl, gram_matrix_apply,
        hleft, hleft, ← hvalue]
      fin_cases i <;> fin_cases j
      · exact hxx
      · exact hxy
      · exact hyx
      · exact hyy
    · obtain ⟨z, hz⟩ := hright j
      rcases planeCoefficients_orthogonal h x y z with ⟨hx, hy⟩
      change M (Sum.inl i) (Sum.inr j) = 0
      rw [show M = adjoint σ.anti.toAlgHom q * H.val * q from rfl, gram_matrix_apply,
        hleft, hz, ← hvalue]
      fin_cases i
      · exact hx
      · exact hy
    · obtain ⟨z, hz⟩ := hright i
      rcases planeCoefficients_orthogonal h x y z with ⟨hx, hy⟩
      change M (Sum.inr i) (Sum.inl j) = 0
      rw [show M = adjoint σ.anti.toAlgHom q * H.val * q from rfl, gram_matrix_apply,
        hz, hleft, ← hvalue, h.skew]
      fin_cases j
      · simp [hx, antiValue]
      · simp [hy, antiValue]
    · rfl
  let N := p * H.inv * adjoint σ.anti.toAlgHom p
  have hapq : adjoint σ.anti.toAlgHom q * adjoint σ.anti.toAlgHom p = 1 := by
    rw [← adjoint_mul, hpq, adjoint_one]
  have haqp : adjoint σ.anti.toAlgHom p * adjoint σ.anti.toAlgHom q = 1 := by
    rw [← adjoint_mul, hqp, adjoint_one]
  have hMN : M * N = 1 := calc
    _ = adjoint σ.anti.toAlgHom q * (H.val * (q * p) * H.inv) *
        adjoint σ.anti.toAlgHom p := by simp only [M, N, Matrix.mul_assoc]
    _ = 1 := by rw [hqp, Matrix.mul_one, H.val_inv, Matrix.mul_one, hapq]
  have hNM : N * M = 1 := calc
    _ = p * (H.inv * (adjoint σ.anti.toAlgHom p * adjoint σ.anti.toAlgHom q) * H.val) * q := by
      simp only [M, N, Matrix.mul_assoc]
    _ = 1 := by rw [haqp, Matrix.mul_one, H.inv_val, Matrix.mul_one, hpq]
  let Munit : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ :=
    ⟨M, N, hMN, hNM⟩
  obtain ⟨Wunit, hWunit⟩ := block_complement_unit W Munit hM
  exact ⟨d, p, q, Wunit, hd, hpq, hqp, hWunit.symm ▸ hM⟩

end HyperbolicMatrices

section Presentation

open LinearAlgebraicGroups.QuaternionHermitianCocharacters (adjoint adjoint_mul adjoint_one)

private theorem quaternion_presentation_at_isotropy
    (isotropy : QuaternionSpinIsotropy.{u}) : QuaternionPresentationAtIsotropy.{u} := by
  intro F K I B _ _ _ _ _ _ _ _ _ ρ G D P hI h2 hB hd hmat hnc
  classical
  obtain ⟨r, ⟨e⟩⟩ := hmat
  let _ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hr : 0 < r := by
    by_contra! hr
    have hr0 : r = 0 := by omega
    subst r
    apply (zero_ne_one : (0 : ρ.fixedSubalgebra) ≠ 1)
    exact e.injective (Subsingleton.elim (e 0) (e 1))
  have hdegree := RM03.CSA.degree_matrix_division D.centralSimple ⟨hB.2.1, hB.2.2⟩ hr e
  have hdB : RM03.CSA.degree F B = 2 := hd
  have hdA : RM03.CSA.degree F ρ.fixedSubalgebra = 2 * Fintype.card I := D.degree
  rw [hdB, hdA, mul_comm r 2] at hdegree
  have hrI : r = Fintype.card I := by omega
  obtain ⟨c, hc⟩ := hnc
  let b := (selfGroupBaseChange F).app G.val
  have hc' : ∃ c' : Cocharacter ((groupBaseChange F F).obj G.val), c' ≠ 0 := by
    refine ⟨c ≫ b.inv, ?_⟩
    intro hz
    apply cocharacter_ne_zero_of_noncentral c hc
    have he := congrArg (fun k => k ≫ b.hom) hz
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using he
  let eF := (Algebra.TensorProduct.lid F ρ.fixedSubalgebra).trans e
  obtain ⟨σ, H, h, x, y, hcan, _, hadj, hval, _, hxx, hxy, hyx, hyy⟩ :=
    isotropy G D P F h2 B hB hd r eF hc'
  obtain ⟨d, p, q, W, hdr, hpq, hqp, hGram⟩ :=
    adapted_quaternion_matrices H h hval x y hxx hxy hyx hyy
  let m := e.trans (changeMatrixCoordinates (F := F) p q hpq hqp)
  let mR (R : TestAlgebra F) :=
    (extendEquiv (R := R) m).trans
      (matrixBaseChange (F := F) (R := R) (D := B) (QuaternionPairIndex d))
  refine ⟨d, by omega, ⟨σ, hcan, W, m, mR, ?_, ?_, fun hz => (h2 hz).elim⟩⟩
  · intro R t v
    simp only [mR, AlgEquiv.trans_apply, extendEquiv_tmul, matrixBaseChange_tmul]
  · intro z
    have hZ : e (D.involution.toLinearMap z) = H.inv * dagger σ.anti (e z) * H.val := by
      have he := hadj ((1 : F) ⊗ₜ[F] z)
      change eF ((1 : F) ⊗ₜ[F] D.involution.toLinearMap z) =
        H.inv * dagger σ.anti (eF ((1 : F) ⊗ₜ[F] z)) * H.val at he
      simpa only [eF, AlgEquiv.trans_apply, Algebra.TensorProduct.lid_tmul, one_smul] using he
    have hH :
        H.val * e (D.involution.toLinearMap z) = adjoint σ.anti.toAlgHom (e z) * H.val := by
      rw [hZ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, H.val_inv, Matrix.one_mul]
      rfl
    have ha : adjoint σ.anti.toAlgHom p * adjoint σ.anti.toAlgHom q = 1 := by
      rw [← adjoint_mul, hqp, adjoint_one]
    rw [← hGram]
    change _ * (p * e (D.involution.toLinearMap z) * q) =
      adjoint σ.anti.toAlgHom (p * e z * q) * _
    calc
      _ = adjoint σ.anti.toAlgHom q * (H.val * (q * p) * e (D.involution.toLinearMap z)) * q := by
        simp only [Matrix.mul_assoc]
      _ = adjoint σ.anti.toAlgHom q * (adjoint σ.anti.toAlgHom (e z) * H.val) * q := by
        rw [hqp, Matrix.mul_one, hH]
      _ = _ := by
        rw [adjoint_mul, adjoint_mul]
        symm
        calc
          _ = adjoint σ.anti.toAlgHom q * (adjoint σ.anti.toAlgHom (e z) *
            ((adjoint σ.anti.toAlgHom p * adjoint σ.anti.toAlgHom q) * H.val)) * q := by
            simp only [Matrix.mul_assoc]
          _ = _ := by rw [ha, Matrix.one_mul]

end Presentation

open LinearAlgebraicGroups.QuaternionHermitianCocharacters (adjoint adjoint_mul)
open Specs.SymplecticDivisionForms (intoTensor)
open private extendAnti_tmul extendAnti_square hermitianValue_rev from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

section MatrixEmbedding

variable {C : Type u} [Ring C] {d : ℕ}

private def lineEmbedding (w : Fin d → C) : Matrix (QuaternionPairIndex d) (Fin 3) C :=
  Matrix.of (Sum.elim (fun i => if i = 0 then ![1, 0, 0] else ![0, 0, 1])
    (fun i => ![0, w i, 0]))

private def lineProjection (p : Fin d → C) : Matrix (Fin 3) (QuaternionPairIndex d) C :=
  (Matrix.of (Sum.elim (fun i => if i = 0 then ![1, 0, 0] else ![0, 0, 1])
    (fun i => ![0, p i, 0]))).transpose

private theorem lineProjection_leftInverse (w p : Fin d → C)
    (h : ∑ i, p i * w i = 1) : lineProjection p * lineEmbedding w = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [lineProjection, lineEmbedding, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, h]

private def lineMatrix (w p : Fin d → C) (M : Matrix (Fin 3) (Fin 3) C) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) C :=
  1 + lineEmbedding w * (M - 1) * lineProjection p

private theorem lineMatrix_mul (w p : Fin d → C) (h : ∑ i, p i * w i = 1)
    (M N : Matrix (Fin 3) (Fin 3) C) :
    lineMatrix w p (M * N) = lineMatrix w p M * lineMatrix w p N := by
  let j := lineEmbedding w
  let t := lineProjection p
  have hjt : t * j = 1 := lineProjection_leftInverse w p h
  change 1 + j * (M * N - 1) * t = (1 + j * (M - 1) * t) * (1 + j * (N - 1) * t)
  have hcomp : (j * (M - 1) * t) * (j * (N - 1) * t) = j * ((M - 1) * (N - 1)) * t := by
    calc
      _ = j * ((M - 1) * (t * j) * (N - 1)) * t := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hjt, Matrix.mul_one]
  calc
    _ = 1 + (j * (M - 1) * t + j * (N - 1) * t + j * ((M - 1) * (N - 1)) * t) := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add]
      congr 2
      noncomm_ring
    _ = _ := by rw [← hcomp]; noncomm_ring

end MatrixEmbedding

section QuaternionWords

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  (R : TestAlgebra F) (w : Fin d → B) (q : Bˣ)

private abbrev extendedLine (i : Fin d) : R ⊗[F] B := intoTensor R B (w i)
private abbrev extendedQ : (R ⊗[F] B)ˣ := Units.map (intoTensor R B).toMonoidHom q

private noncomputable def lineCoordinates (i : Fin d) : R ⊗[F] B :=
  (↑(extendedQ R q)⁻¹ : R ⊗[F] B) *
    ∑ k, antiValue (coefficientConjugation Q R) (extendedLine R w k) * complementGram Q R k i

private theorem lineCoordinates_splits
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B)) :
    ∑ i, lineCoordinates Q R w q i * extendedLine R w i = 1 := by
  have he : ∑ i, (∑ k, antiValue (coefficientConjugation Q R) (extendedLine R w k) *
        complementGram Q R k i) * extendedLine R w i = (extendedQ R q : R ⊗[F] B) := by
    have ht := congrArg (intoTensor (F := F) R B) h
    rw [hermitianValue, Matrix.dotProduct_mulVec] at ht
    change _ = (1 : R) ⊗ₜ[F] (q : B)
    simpa only [Matrix.vecMul, dotProduct, map_sum, map_mul, extendedLine, extendedQ,
      complementGram, Matrix.map_apply,
      intoTensor, Algebra.TensorProduct.includeRight_apply, extendAnti_tmul] using ht
  simp only [lineCoordinates, mul_assoc, ← Finset.mul_sum, he, Units.inv_mul]

private theorem line_matrix_upper (a b : R ⊗[F] B) :
    lineMatrix (extendedLine R w) (lineCoordinates Q R w q)
      (upperShear (coefficientConjugation Q R) (extendedQ R q) a b) =
        shearMatrix Q true w q R a b := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [lineMatrix, lineEmbedding, lineProjection,
      upperShear, shearMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · fin_cases i <;> simp [lineMatrix, lineEmbedding, lineProjection, upperShear, shearMatrix,
      lineCoordinates, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, mul_assoc, extendedLine, intoTensor,
      extendAnti_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  · fin_cases j <;> simp [lineMatrix, lineEmbedding, lineProjection, upperShear, shearMatrix,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, mul_assoc, extendedLine, intoTensor,
      extendAnti_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · simp [lineMatrix, lineEmbedding, lineProjection, upperShear, shearMatrix,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]

private theorem line_matrix_lower (a b : R ⊗[F] B) :
    lineMatrix (extendedLine R w) (lineCoordinates Q R w q)
      (lowerShear (coefficientConjugation Q R) (extendedQ R q) a b) =
        shearMatrix Q false w q R a b := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [lineMatrix, lineEmbedding, lineProjection,
      lowerShear, shearMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · fin_cases i <;> simp [lineMatrix, lineEmbedding, lineProjection, lowerShear, shearMatrix,
      lineCoordinates, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, mul_assoc, extendedLine, intoTensor,
      extendAnti_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  · fin_cases j <;> simp [lineMatrix, lineEmbedding, lineProjection, lowerShear, shearMatrix,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, mul_assoc, extendedLine, intoTensor,
      extendAnti_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · simp [lineMatrix, lineEmbedding, lineProjection, lowerShear, shearMatrix,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]

private theorem line_matrix_interchange (a : R ⊗[F] B) (b : (R ⊗[F] B)ˣ) :
    lineMatrix (extendedLine R w) (lineCoordinates Q R w q)
      (interchange b
        (1 + (↑(extendedQ R q)⁻¹ : R ⊗[F] B) * antiValue (coefficientConjugation Q R) a *
          (↑b⁻¹ : R ⊗[F] B) * a) (coefficientConjugation Q R)) =
      interchangeMatrix Q w q R a b := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [lineMatrix, lineEmbedding, lineProjection, interchange,
      interchangeMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · fin_cases i <;> simp [lineMatrix, lineEmbedding, lineProjection, interchange,
      interchangeMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · fin_cases j <;> simp [lineMatrix, lineEmbedding, lineProjection, interchange,
      interchangeMatrix, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three]
  · simp [lineMatrix, lineEmbedding, lineProjection, interchange, interchangeMatrix, lineCoordinates,
      Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_three, mul_assoc, extendedLine, intoTensor,
      extendAnti_tmul]

private theorem vectorMatrix_mul (g h : Points G.val.X R) :
    vectorMatrix Q P R (g * h) = vectorMatrix Q P R g * vectorMatrix Q P R h := by
  simp [vectorMatrix, map_mul]

private def hyperbolicPlane (C : Type u) [Ring C] : (Matrix (Fin 2) (Fin 2) C)ˣ where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def quaternionGramUnit : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ where
  val := quaternionHyperbolicGram Q.complement.val
  inv := Matrix.fromBlocks (hyperbolicPlane B).inv 0 0 Q.complement.inv
  val_inv := by
    change Matrix.fromBlocks (hyperbolicPlane B).val 0 0 Q.complement.val *
      Matrix.fromBlocks (hyperbolicPlane B).inv 0 0 Q.complement.inv = 1
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  inv_val := by
    change Matrix.fromBlocks (hyperbolicPlane B).inv 0 0 Q.complement.inv *
      Matrix.fromBlocks (hyperbolicPlane B).val 0 0 Q.complement.val = 1
    simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

private theorem complement_skew : dagger Q.conjugation.anti Q.complement.val = -Q.complement.val := by
  classical
  let H := quaternionGramUnit Q
  let A := Q.matrixModel
  let τ := D.involution.toLinearMap
  let ad := fun X : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B =>
    adjoint Q.conjugation.anti.toAlgHom X
  have ht (x : ρ.fixedSubalgebra) : H.val * A (τ x) = ad (A x) * H.val := Q.adjoint x
  have ht2 (x : ρ.fixedSubalgebra) : H.val * A x = ad (A (τ x)) * H.val := by
    have e := ht (τ x)
    rw [D.involution.involutive x] at e
    exact e
  have hAd (X : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) :
      ad (ad X) = X := by
    ext i j
    exact Q.conjugation.square (X i j)
  have hAdmul (X Y : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) :
      ad (X * Y) = ad Y * ad X := adjoint_mul _ _ _
  let C := H.inv * ad H.val
  have hC (M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) : M * C = C * M := by
    obtain ⟨x, rfl⟩ := A.surjective M
    have h := congrArg ad (ht x)
    rw [hAdmul, hAdmul, hAd] at h
    have h' : ad (A (τ x)) = H.val * A x * H.inv := by
      rw [ht2, Matrix.mul_assoc, H.val_inv, Matrix.mul_one]
    rw [h'] at h
    have h'' := congrArg (H.inv * ·) h
    simpa only [C, Matrix.mul_assoc, ← Matrix.mul_assoc H.inv H.val, H.inv_val,
      Matrix.one_mul] using h''
  have hadH : ad H.val =
      Matrix.fromBlocks (-(hyperbolicPlane B).val) 0 0 (dagger Q.conjugation.anti Q.complement.val) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;>
        simp [H, ad, adjoint, quaternionGramUnit, quaternionHyperbolicGram, hyperbolicPlane]
    · simp [H, ad, adjoint, quaternionGramUnit, quaternionHyperbolicGram]
    · simp [H, ad, adjoint, quaternionGramUnit, quaternionHyperbolicGram]
    · rfl
  let i₀ : QuaternionPairIndex d := Sum.inl 0
  have hC₀ : C i₀ i₀ = -1 := by
    rw [show C = H.inv * ad H.val from rfl, hadH]
    change (Matrix.fromBlocks (hyperbolicPlane B).inv 0 0 Q.complement.inv *
        Matrix.fromBlocks (-(hyperbolicPlane B).val) 0 0
          (dagger Q.conjugation.anti Q.complement.val)) i₀ i₀ = _
    rw [Matrix.fromBlocks_multiply]
    simp [i₀, Matrix.mul_neg]
  have hCmat : C = -1 := by
    ext i j
    have h := congrArg (fun X : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B => X i₀ j)
      (hC (Matrix.single i₀ i 1))
    by_cases hij : i = j <;>
      simpa [Matrix.mul_apply, Matrix.single, Finset.sum_ite_eq, Finset.sum_ite_eq',
        i₀, hC₀, Matrix.one_apply, hij, eq_comm] using h
  have hh : ad H.val = -H.val := by
    have h := congrArg (H.val * ·) hCmat
    simpa only [C, ← Matrix.mul_assoc, H.val_inv, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one] using h
  ext i j
  exact congrArg (fun M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B =>
    M (Sum.inr i) (Sum.inr j)) hh

private theorem fixed_line_pure (v : Fin d → B) (q : Bˣ)
    (h : hermitianValue Q.conjugation.anti Q.complement.val v v = (q : B)) :
    antiValue Q.conjugation.anti (q : B) = -(q : B) := by
  rw [← h, hermitianValue_rev Q.conjugation.anti Q.conjugation.square, complement_skew]
  rw [hermitianValue, Matrix.neg_mulVec, dotProduct_neg]
  rfl

private theorem liftedInterchange_formula {c : Cocharacter G.val} (L : ShearLifts Q P c) :
    LiftedInterchangeFormula Q P L := by
  intro v q R a b h
  have hq := fixed_line_pure Q v q h.1
  have hqR : antiValue (coefficientConjugation Q R) (extendedQ R q : R ⊗[F] B) =
      -(extendedQ R q : R ⊗[F] B) := by
    change antiValue (coefficientConjugation Q R) (1 ⊗ₜ[F] (q : B)) = -(1 ⊗ₜ[F] (q : B))
    rw [extendAnti_tmul, hq, TensorProduct.tmul_neg]
  have hInv := extendAnti_square (R := R) Q.conjugation.anti Q.conjugation.square
  obtain ⟨h₁, h₂, hword⟩ :=
    opposite_shear_word (coefficientConjugation Q R) hInv (extendedQ R q) hqR a b h.2
  let h₁' : ShearAdmissible Q v q R
      (-(antiValue (coefficientConjugation Q R) ↑b⁻¹ * a))
      (antiValue (coefficientConjugation Q R) ↑b⁻¹) := ⟨h.1, h₁⟩
  let h₂' : ShearAdmissible Q v q R (↑b⁻¹ * a) (antiValue (coefficientConjugation Q R) ↑b⁻¹) :=
      ⟨h.1, h₂⟩
  refine ⟨h₁', h₂', ?_⟩
  rw [liftedInterchange, vectorMatrix_mul, vectorMatrix_mul, L.formula, L.formula, L.formula,
    ← line_matrix_lower, ← line_matrix_upper, ← line_matrix_lower,
    ← lineMatrix_mul _ _ (lineCoordinates_splits Q R v q h.1),
    ← lineMatrix_mul _ _ (lineCoordinates_splits Q R v q h.1),
    hword, line_matrix_interchange]

end QuaternionWords

open Specs.Arithmetic.QuaternionSpinScaleCover
  (inverseConjugateUnit diagonalQuaternionScale quaternionScale spinVectorProjection
    spinScalePreimage scalePairs)
open Specs.SymplecticDivisionForms (tensorMap)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint unitPoint mapPoints_unitPoint)
open _root_.Specs.RM03.CSA (reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

open private unitEquiv unitEquiv_unitPoint
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

section AllCoefficientAlgebras

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private theorem matrixAt_map (R S : TestAlgebra F) (f : R ⟶ S)
    (x : R ⊗[F] ρ.fixedSubalgebra) :
    Q.matrixAt S (tensorMap _ f.hom x) = (Q.matrixAt R x).map (tensorMap B f.hom) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [tensorMap, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Q.matrixAtFormula, Matrix.map_map]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    ext i j
    simp only [Matrix.add_apply, Matrix.map_apply, map_add]

private theorem coefficientConjugation_map (R S : TestAlgebra F) (f : R ⟶ S)
    (x : R ⊗[F] B) :
    antiValue (coefficientConjugation Q S) (tensorMap B f.hom x) =
      tensorMap B f.hom (antiValue (coefficientConjugation Q R) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r b => simp [tensorMap, extendAnti_tmul]
  | add x y hx hy =>
    simp only [map_add, antiValue, MulOpposite.unop_add] at hx hy ⊢
    rw [hx, hy]

private theorem scale_matrix (R : TestAlgebra F) (t : (R ⊗[F] B)ˣ) :
    Q.matrixAt R (quaternionScale Q R t).val =
      Matrix.diagonal (Sum.elim ![(t : R ⊗[F] B),
        ((inverseConjugateUnit (coefficientConjugation Q R).toMonoidHom t : (R ⊗[F] B)ˣ) :
          R ⊗[F] B)] (fun _ => 1)) := by
  change Q.matrixAt R ((Q.matrixAt R).symm
    (diagonalQuaternionScale (coefficientConjugation Q R).toMonoidHom d t).val) = _
  rw [AlgEquiv.apply_symm_apply]
  ext i j
  by_cases hij : i = j
  · subst j
    rcases i with i | i
    · fin_cases i <;> rfl
    · rfl
  · change Matrix.diagonal
      (fun i => ((Sum.elim ![t, inverseConjugateUnit (coefficientConjugation Q R).toMonoidHom t]
        (fun _ => 1) i : (R ⊗[F] B)ˣ) : R ⊗[F] B)) i j = _
    simp [hij]

private theorem scale_map (R S : TestAlgebra F) (f : R ⟶ S) (t : (R ⊗[F] B)ˣ) :
    quaternionScale Q S (Units.map (tensorMap B f.hom).toMonoidHom t) =
      Units.map (tensorMap ρ.fixedSubalgebra f.hom).toMonoidHom (quaternionScale Q R t) := by
  apply Units.ext
  apply (Q.matrixAt S).injective
  change Q.matrixAt S (quaternionScale Q S (Units.map (tensorMap B f.hom).toMonoidHom t)).val =
    Q.matrixAt S (tensorMap _ f.hom (quaternionScale Q R t).val)
  rw [matrixAt_map, scale_matrix, scale_matrix]
  ext i j
  by_cases hij : i = j
  · subst j
    rcases i with i | i
    · fin_cases i
      · rfl
      · simp only [Matrix.map_apply, Matrix.diagonal_apply_eq, Sum.elim_inl]
        change antiValue (coefficientConjugation Q S)
            (tensorMap B f.hom (↑t⁻¹ : R ⊗[F] B)) =
          tensorMap B f.hom (antiValue (coefficientConjugation Q R) (↑t⁻¹ : R ⊗[F] B))
        exact coefficientConjugation_map Q R S f _
    · simp
  · simp [hij]

private theorem projection_map (R S : TestAlgebra F) (f : R ⟶ S) (g : Points G.val.X R) :
    spinVectorProjection P S (mapPoints f g) =
      Units.map (tensorMap ρ.fixedSubalgebra f.hom).toMonoidHom (spinVectorProjection P R g) := by
  change P.fullPoints S ((mapPoints f g) ≫ (P.projection ≫ P.inclusion).hom.hom) = _
  rw [show (mapPoints f g) ≫ (P.projection ≫ P.inclusion).hom.hom =
    mapPoints f (g ≫ (P.projection ≫ P.inclusion).hom.hom) from Category.assoc _ _ _]
  exact P.fullNatural R S f _

private theorem normAt_ground {J : Type u} [Fintype J] (b : Module.Basis J F B)
    (x : F ⊗[F] B) : normAt hB b x = reducedNorm hB (Algebra.TensorProduct.lid F B x) := by
  have hx : (1 : F) ⊗ₜ[F] (Algebra.TensorProduct.lid F B x) = x := by
    apply (Algebra.TensorProduct.lid F B).injective
    simp
  conv_lhs => rw [← hx]
  change _ = RM03.CSA.reducedNorm hB (Algebra.TensorProduct.lid F B x)
  rw [← RM03.CSA.reducedNorm_basis_eval hB b]
  simp [normAt, Algebra.algebraMap_self]
  rfl

private theorem spin_scale_lifts_iff
    (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
    (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
    (he : ∀ R x, (e R x).val.1 = x.val.2)
    (hn : ∀ t : (CommAlgCat.of F F ⊗[F] B)ˣ,
      (N (CommAlgCat.of F F) t : F) = reducedNorm hB (Algebra.TensorProduct.lid F B t.val))
    (t : (CommAlgCat.of F F ⊗[F] B)ˣ) :
    (∃ g : Points G.val.X (CommAlgCat.of F F),
      spinVectorProjection P (CommAlgCat.of F F) g = quaternionScale Q (CommAlgCat.of F F) t) ↔
      ∃ s : Fˣ, reducedNorm hB (Algebra.TensorProduct.lid F B t.val) = (s : F) ^ 2 := by
  let R := CommAlgCat.of F F
  constructor
  · rintro ⟨g, hg⟩
    let x : spinScalePreimage P Q R := ⟨(g, t), hg⟩
    refine ⟨(e R x).val.2, ?_⟩
    have h : N R (e R x).val.1 = (e R x).val.2 ^ 2 := (e R x).property
    have hx : (e R x).val.1 = t := he R x
    rw [hx] at h
    simpa only [← hn t, Units.val_pow_eq_pow_val] using congrArg Units.val h
  · rintro ⟨s, hs⟩
    let z : scalePairs (N R) := ⟨(t, s), Units.ext (by
      change (N R t : F) = ((s ^ 2 : Fˣ) : F)
      rw [hn t, Units.val_pow_eq_pow_val]
      exact hs)⟩
    let x := (e R).symm z
    have hx : x.val.2 = t := (he R x).symm.trans (by simp [x, z])
    refine ⟨x.val.1, ?_⟩
    have h : spinVectorProjection P R x.val.1 = quaternionScale Q R x.val.2 := x.property
    rwa [hx] at h

private abbrev scalarParameter (R : TestAlgebra F) (t : Rˣ) : (R ⊗[F] B)ˣ :=
  Units.map (algebraMap R (R ⊗[F] B)).toMonoidHom t

private theorem scalarParameter_map (R S : TestAlgebra F) (f : R ⟶ S) (t : Rˣ) :
    Units.map (tensorMap B f.hom).toMonoidHom (scalarParameter (B := B) R t) =
      scalarParameter S (Units.map f.hom.toMonoidHom t) := by
  apply Units.ext
  change tensorMap B f.hom (t.val ⊗ₜ[F] (1 : B)) = f.hom t.val ⊗ₜ[F] (1 : B)
  simp [tensorMap]

variable (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
  (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
  (hscalar : ∀ (R : TestAlgebra F) (t : Rˣ), N R (scalarParameter (B := B) R t) = t ^ 2)
  (he : ∀ R x, (e R x).val.1 = x.val.2)

private noncomputable def scalarPair (R : TestAlgebra F) : Rˣ →* scalePairs (N R) where
  toFun s := ⟨(scalarParameter R s, s), hscalar R s⟩
  map_one' := Subtype.ext (Prod.ext (map_one _) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (map_mul (Units.map _) s t) rfl)

private noncomputable def scalarSpinLift (R : TestAlgebra F) : Rˣ →* Points G.val.X R :=
  (MonoidHom.fst _ _).comp ((spinScalePreimage P Q R).subtype.comp
    ((e R).symm.toMonoidHom.comp (scalarPair N hscalar R)))

include he

private theorem scalarSpinLift_projection (R : TestAlgebra F) (t : Rˣ) :
    spinVectorProjection P R (scalarSpinLift Q P N e hscalar R t) =
      quaternionScale Q R (scalarParameter R t) := by
  let x := (e R).symm (scalarPair N hscalar R t)
  have hx : x.val.2 = scalarParameter R t := by
    have h := (he R x).symm
    rw [(e R).apply_symm_apply] at h
    exact h
  have h := x.property
  change spinVectorProjection P R x.val.1 = quaternionScale Q R x.val.2 at h
  rwa [hx] at h

private theorem scalarSpinLift_map
    (hnatural : ∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : spinScalePreimage P Q R)
      (y : spinScalePreimage P Q S), y.val.1 = mapPoints f x.val.1 →
      y.val.2 = Units.map (tensorMap B f.hom).toMonoidHom x.val.2 →
      (e S y).val.2 = Units.map f.hom.toMonoidHom (e R x).val.2)
    (R S : TestAlgebra F) (f : R ⟶ S) (t : Rˣ) :
    mapPoints f (scalarSpinLift Q P N e hscalar R t) =
      scalarSpinLift Q P N e hscalar S (Units.map f.hom.toMonoidHom t) := by
  let x := (e R).symm (scalarPair N hscalar R t)
  have hx : x.val.2 = scalarParameter R t := by
    have h := (he R x).symm
    rw [(e R).apply_symm_apply] at h
    exact h
  let y : spinScalePreimage P Q S := ⟨(mapPoints f x.val.1,
    Units.map (tensorMap B f.hom).toMonoidHom x.val.2), by
      change spinVectorProjection P S (mapPoints f x.val.1) =
        quaternionScale Q S (Units.map (tensorMap B f.hom).toMonoidHom x.val.2)
      rw [projection_map, scale_map]
      exact congrArg (Units.map (tensorMap ρ.fixedSubalgebra f.hom).toMonoidHom) x.property⟩
  have hy : e S y = scalarPair N hscalar S (Units.map f.hom.toMonoidHom t) := by
    apply Subtype.ext
    apply Prod.ext
    · rw [he]
      change Units.map (tensorMap B f.hom).toMonoidHom x.val.2 =
        scalarParameter S (Units.map f.hom.toMonoidHom t)
      rw [hx, scalarParameter_map]
    · have h := hnatural R S f x y rfl rfl
      simpa [x, scalarPair] using h
  have heq : y = (e S).symm (scalarPair N hscalar S (Units.map f.hom.toMonoidHom t)) :=
    (e S).injective (hy.trans ((e S).apply_symm_apply _).symm)
  exact congrArg (fun z : spinScalePreimage P Q S => z.val.1) heq

private theorem scalar_spin_cocharacter
    (hnatural : ∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : spinScalePreimage P Q R)
      (y : spinScalePreimage P Q S), y.val.1 = mapPoints f x.val.1 →
      y.val.2 = Units.map (tensorMap B f.hom).toMonoidHom x.val.2 →
      (e S y).val.2 = Units.map f.hom.toMonoidHom (e R x).val.2) :
    ∃ c : Cocharacter G.val, ∀ (R : TestAlgebra F) (t : Rˣ),
      cocharacterPoint c R t = scalarSpinLift Q P N e hscalar R t := by
  let S := specGroup (Specs.DiagonalizableGroups.groupAlgebra F
    Specs.DiagonalizableGroups.IntegerCharacters)
  let α : (groupPointsFunctor F).obj S ⟶ (groupPointsFunctor F).obj G.val :=
    { app := fun R => GrpCat.ofHom ((scalarSpinLift Q P N e hscalar R).comp (unitEquiv R).toMonoidHom)
      naturality := by
        intro R T f
        apply GrpCat.ext
        intro z
        have hz : unitPoint R (unitEquiv R z) = z := by
          apply (unitEquiv R).injective
          exact unitEquiv_unitPoint R (unitEquiv R z)
        let t := unitEquiv R z
        change scalarSpinLift Q P N e hscalar T (unitEquiv T (mapPoints f z)) =
          mapPoints f (scalarSpinLift Q P N e hscalar R t)
        rw [← show unitPoint R t = z from hz, mapPoints_unitPoint, unitEquiv_unitPoint]
        exact (scalarSpinLift_map Q P N e hscalar he hnatural R T f t).symm }
  have ha : IsAffine S.X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra F Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance
  let E := groupHomEquiv S G.val ha
  let c := E.symm α
  refine ⟨c, fun R t => ?_⟩
  have hc := E.apply_symm_apply α
  change (groupPointsFunctor F).map c = α at hc
  rw [cocharacterPoint, hc]
  change scalarSpinLift Q P N e hscalar R (unitEquiv R (unitPoint R t)) = _
  rw [unitEquiv_unitPoint]

end AllCoefficientAlgebras

open private dagger_add dagger_smul
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms
open private exists_mixed_commutator
  from LinearAlgebraicGroups.Arithmetic.QuaternionMixedCommutators

section TensorGram

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (R : TestAlgebra F)

private noncomputable def gramAt : (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ :=
  Units.map (intoTensor R B).mapMatrix.toMonoidHom (quaternionGramUnit Q)

private theorem matrixAt_tmul_smul (r : R) (x : ρ.fixedSubalgebra) :
    Q.matrixAt R (r ⊗ₜ[F] x) = r • (Q.matrixModel x).map (intoTensor R B) := by
  rw [Q.matrixAtFormula]
  ext i j
  change r ⊗ₜ[F] Q.matrixModel x i j = r • ((1 : R) ⊗ₜ[F] Q.matrixModel x i j)
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem dagger_map_intoTensor (M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) :
    dagger (coefficientConjugation Q R) (M.map (intoTensor R B)) =
      (dagger Q.conjugation.anti M).map (intoTensor R B) := by
  ext i j
  exact extendAnti_tmul Q.conjugation.anti (1 : R) (M j i)

private theorem involution_at (x : R ⊗[F] ρ.fixedSubalgebra) :
    (gramAt Q R).val * Q.matrixAt R ((D.involution.baseChange R).toLinearMap x) =
      dagger (coefficientConjugation Q R) (Q.matrixAt R x) * (gramAt Q R).val := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, dagger_add, Matrix.mul_add, Matrix.add_mul, hx, hy]
  | tmul r x =>
    rw [show (D.involution.baseChange R).toLinearMap (r ⊗ₜ[F] x) =
      r ⊗ₜ[F] D.involution.toLinearMap x from LinearMap.baseChange_tmul _ _ _]
    rw [matrixAt_tmul_smul, matrixAt_tmul_smul, Matrix.mul_smul, dagger_smul, Matrix.smul_mul]
    congr 1
    rw [dagger_map_intoTensor]
    have h := congrArg (intoTensor (F := F) R B).mapMatrix (Q.adjoint x)
    rw [map_mul, map_mul] at h
    exact h

private theorem isometry_iff_gram (g : (R ⊗[F] ρ.fixedSubalgebra)ˣ) :
    (D.involution.baseChange R).toLinearMap g.val * g.val = 1 ↔
      dagger (coefficientConjugation Q R) (Q.matrixAt R g.val) * (gramAt Q R).val *
        Q.matrixAt R g.val = (gramAt Q R).val := by
  let H := gramAt Q R
  have he : dagger (coefficientConjugation Q R) (Q.matrixAt R g.val) * H.val *
        Q.matrixAt R g.val =
      H.val * Q.matrixAt R ((D.involution.baseChange R).toLinearMap g.val * g.val) := by
    rw [← involution_at, map_mul, Matrix.mul_assoc]
  change _ ↔ _ = H.val
  rw [he]
  constructor
  · intro h
    rw [h, map_one, Matrix.mul_one]
  · intro h
    apply (Q.matrixAt R).injective
    rw [map_one]
    have hh := congrArg (H.inv * ·) h
    simpa only [← Matrix.mul_assoc, H.inv_val, Matrix.one_mul] using hh

end TensorGram

section RationalScale

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)

set_option maxHeartbeats 2000000 in
private theorem rational_scale_mem
    (h2 : (2 : F) ≠ 0) (hd : degree F B = 2)
    (w : Fin d → B) (q : Bˣ)
    (hw : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B))
    (hq : antiValue Q.conjugation.anti (q : B) = -(q : B))
    (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
    (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
    (he : ∀ R x, (e R x).val.1 = x.val.2)
    (hn : ∀ t : (CommAlgCat.of F F ⊗[F] B)ˣ,
      (N (CommAlgCat.of F F) t : F) = reducedNorm hB (Algebra.TensorProduct.lid F B t.val))
    (hwords : NormalizedLiftedScaleWords Q P L N e)
    (H : Subgroup (Points G.val.X (CommAlgCat.of F F)))
    (hlift : ∀ upper v q a b (h : ShearAdmissible Q v q (CommAlgCat.of F F) a b),
      L.lift upper v q (CommAlgCat.of F F) a b h ∈ H)
    (x : spinScalePreimage P Q (CommAlgCat.of F F)) : x.val.1 ∈ H := by
  classical
  let R := CommAlgCat.of F F
  let A : (R ⊗[F] B) ≃ₐ[F] B := Algebra.TensorProduct.lid F B
  let Aunit : (R ⊗[F] B)ˣ ≃* Bˣ := Units.mapEquiv A.toMulEquiv
  have hA (b : B) : A.symm b = (1 : R) ⊗ₜ[F] b := by
    apply A.injective
    change A (A.symm b) = A ((1 : F) ⊗ₜ[F] b)
    simp [A]
  have hword (a : R ⊗[F] B) (b : (R ⊗[F] B)ˣ)
      (h : ShearAdmissible Q w q R a (b : R ⊗[F] B))
      (h₁ : ShearAdmissible Q w q R (-(antiValue (coefficientConjugation Q R) ↑b⁻¹ * a))
        (antiValue (coefficientConjugation Q R) ↑b⁻¹))
      (h₂ : ShearAdmissible Q w q R (↑b⁻¹ * a) (antiValue (coefficientConjugation Q R) ↑b⁻¹)) :
      liftedInterchange Q P L w q R a b h h₁ h₂ ∈ H :=
    H.mul_mem (H.mul_mem (hlift false w q _ _ h₁) (hlift true w q _ _ h))
      (hlift false w q _ _ h₂)
  obtain ⟨scalarWord, hs, hcomm⟩ := hwords
  have hm (s : Rˣ) : (scalarWord w q R s).val.1 ∈ H := by
    obtain ⟨_, hs, hs₁, hs₂, h1, h1₁, h1₂, hEq⟩ := hs w q R s hw
    rw [hEq]
    exact H.mul_mem (hword 0 _ hs hs₁ hs₂) (H.inv_mem (hword 0 _ h1 h1₁ h1₂))
  let s := (e R x).val.2
  let z := x * (scalarWord w q R s)⁻¹
  have hz₂ : (e R z).val.2 = 1 := by
    dsimp only [z]
    rw [map_mul, map_inv]
    change (e R x).val.2 * (e R (scalarWord w q R s)).val.2⁻¹ = 1
    rw [congrArg Prod.snd ((hs w q R s hw).1), mul_inv_cancel]
  have hzN : N R z.val.2 = 1 := by
    have h : N R (e R z).val.1 = (e R z).val.2 ^ 2 := (e R z).property
    rwa [he, hz₂, one_pow] at h
  let b := Aunit z.val.2
  have hbn : reducedNorm hB (b : B) = 1 := (hn z.val.2).symm.trans (congrArg Units.val hzN)
  have hzmem : z.val.1 ∈ H := by
    by_cases hb1 : b = 1
    · have hb0 : z.val.2 = 1 := Aunit.injective (hb1.trans (map_one Aunit).symm)
      have hz1 : z = 1 := by
        apply (e R).injective
        rw [map_one]
        apply Subtype.ext
        exact Prod.ext ((he R z).trans hb0) hz₂
      rw [hz1]
      exact H.one_mem
    obtain ⟨E, _, _, _, j, qE, hqE, hE, _, _, _, _, hclass⟩ :=
      fixed_line_parameters h2 hB hd Q.conjugation Q.canonical q hq
    obtain ⟨a, b₀, hb₀⟩ := exists_mixed_commutator hB hd j hE hbn hb1
    have hb₀ns : (b₀ : E) ∉ Set.range (algebraMap F E) := by
      rintro ⟨f, hf⟩
      have hh : Commute a (Units.map j.toMonoidHom b₀) := by
        apply Commute.units_of_val
        change Commute (a : B) (j (b₀ : E))
        rw [← hf, j.commutes]
        exact (Algebra.commutes f (a : B)).symm
      apply hb1
      rw [hb₀, commutatorElement_def, hh.eq]
      group
    obtain ⟨t, ht⟩ := hclass b₀ hb₀ns
    let tE := Units.map (algebraMap F E).toMonoidHom t
    let p := Units.map j.toMonoidHom (tE * b₀)
    let bR := Aunit.symm p
    let aR := Aunit.symm a
    have hval : (bR : R ⊗[F] B) = (1 : R) ⊗ₜ[F] (p : B) := hA _
    have ht' : (p : B) - antiValue Q.conjugation.anti (p : B) = -((q : B)⁻¹) := ht
    have hbR : ShearAdmissible Q w q R 1 (bR : R ⊗[F] B) := by
      refine ⟨hw, ?_⟩
      have hone : antiValue (coefficientConjugation Q R) (1 : R ⊗[F] B) = 1 := by simp [antiValue]
      rw [hone, one_mul, mul_one, hval, extendAnti_tmul, ← TensorProduct.tmul_sub,
        ht', TensorProduct.tmul_neg, Units.val_inv_eq_inv_val]
    obtain ⟨z₀, hz₀, h0, h01, h02, h1, h11, h12, hw₀⟩ := hcomm w q R aR bR hbR
    have hprod : a * p * a⁻¹ * p⁻¹ = b := by
      let u := Units.map j.toMonoidHom tE
      let v := Units.map j.toMonoidHom b₀
      have hpu : p = u * v := map_mul (Units.map j.toMonoidHom) _ _
      have hua : Commute a u := by
        apply Commute.units_of_val
        change Commute (a : B) (j (algebraMap F E (t : F)))
        rw [j.commutes]
        exact (Algebra.commutes (t : F) (a : B)).symm
      have huv : Commute v u := (Commute.all b₀ tE).map (Units.map j.toMonoidHom)
      have hub : Commute (a * v * a⁻¹ * v⁻¹) u :=
        ((hua.mul_left huv).mul_left hua.inv_left).mul_left huv.inv_left
      calc
        a * p * a⁻¹ * p⁻¹ = u * (a * v * a⁻¹ * v⁻¹) * u⁻¹ := by
          rw [hpu, show a * (u * v) = u * (a * v) by rw [← mul_assoc, hua.eq, mul_assoc]]
          group
        _ = a * v * a⁻¹ * v⁻¹ := hub.symm.mul_inv_cancel
        _ = b := by rw [hb₀, commutatorElement_def]
    have hz_eq : z₀ = z := by
      apply (e R).injective
      apply Subtype.ext
      rw [hz₀]
      apply Prod.ext _ hz₂.symm
      change aR * bR * aR⁻¹ * bR⁻¹ = (e R z).val.1
      rw [he]
      apply Aunit.injective
      simp only [map_mul, map_inv, aR, bR, MulEquiv.apply_symm_apply]
      exact hprod
    rw [← hz_eq, hw₀]
    exact H.mul_mem (H.mul_mem (hword _ _ h1 h11 h12) (H.inv_mem (hword _ _ h0 h01 h02)))
      (hm (N R aR)⁻¹)
  have hx : x = z * scalarWord w q R s := by
    dsimp only [z]
    group
  rw [hx]
  exact H.mul_mem hzmem (hm s)

end RationalScale

section ScaleWords

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)
  (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)

private noncomputable def interchangeLift
    (a : R ⊗[F] B) (b : (R ⊗[F] B)ˣ)
    (h : ShearAdmissible Q w q R a ↑b) : Points G.val.X R :=
  let E := liftedInterchange_formula Q P L w q R a b h
  liftedInterchange Q P L w q R a b h E.choose E.choose_spec.choose

private theorem interchangeLift_formula
    (a : R ⊗[F] B) (b : (R ⊗[F] B)ˣ)
    (h : ShearAdmissible Q w q R a ↑b) :
    vectorMatrix Q P R (interchangeLift Q P L w q R a b h) = interchangeMatrix Q w q R a b :=
  (liftedInterchange_formula Q P L w q R a b h).choose_spec.choose_spec

private theorem left_scale_mul_interchangeMatrix
    (a a' : R ⊗[F] B) (b b' : (R ⊗[F] B)ˣ)
    (h : (interchangeMatrix Q w q R a b).toBlocks₂₂ =
      (interchangeMatrix Q w q R a' b').toBlocks₂₂) :
    Q.matrixAt R (quaternionScale Q R (b * b'⁻¹)).val *
      interchangeMatrix Q w q R a' b' = interchangeMatrix Q w q R a b := by
  let σ := coefficientConjugation Q R
  let j := inverseConjugateUnit σ.toMonoidHom
  have ht : (b * b'⁻¹) * b' = b := inv_mul_cancel_right _ _
  have hj : j (b * b'⁻¹) * j b' = j b := by rw [← map_mul, ht]
  have hv : ((b * b'⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) * (b' : R ⊗[F] B) = (b : R ⊗[F] B) :=
    congrArg Units.val ht
  have hi : ((j (b * b'⁻¹) : (R ⊗[F] B)ˣ) : R ⊗[F] B) *
      antiValue σ (↑b'⁻¹ : R ⊗[F] B) = antiValue σ (↑b⁻¹ : R ⊗[F] B) :=
    congrArg Units.val hj
  rw [scale_matrix]
  ext i j'
  rw [Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j' with j' | j'
  · fin_cases i <;> fin_cases j'
    · simp [interchangeMatrix]
    · exact hv
    · change (j (b * b'⁻¹)).val * (-antiValue σ ↑b'⁻¹) = -antiValue σ ↑b⁻¹
      rw [mul_neg, hi]
    · simp [interchangeMatrix]
  · simp [interchangeMatrix]
  · simp [interchangeMatrix]
  · simpa [interchangeMatrix] using (congrFun (congrFun h i) j').symm

private theorem scale_of_interchange_ratio
    (a a' : R ⊗[F] B) (b b' : (R ⊗[F] B)ˣ)
    (h : ShearAdmissible Q w q R a ↑b) (h' : ShearAdmissible Q w q R a' ↑b')
    (hW : (interchangeMatrix Q w q R a b).toBlocks₂₂ =
      (interchangeMatrix Q w q R a' b').toBlocks₂₂) :
    spinVectorProjection P R
      (interchangeLift Q P L w q R a b h * (interchangeLift Q P L w q R a' b' h')⁻¹) =
      quaternionScale Q R (b * b'⁻¹) := by
  let x := interchangeLift Q P L w q R a b h
  let y := interchangeLift Q P L w q R a' b' h'
  have he : spinVectorProjection P R x =
      quaternionScale Q R (b * b'⁻¹) * spinVectorProjection P R y := by
    apply Units.ext
    apply (Q.matrixAt R).injective
    change vectorMatrix Q P R x =
      Q.matrixAt R ((quaternionScale Q R (b * b'⁻¹)).val *
        (spinVectorProjection P R y).val)
    rw [map_mul, interchangeLift_formula, ← show vectorMatrix Q P R y =
      Q.matrixAt R (spinVectorProjection P R y).val from rfl, interchangeLift_formula]
    exact (left_scale_mul_interchangeMatrix Q w q R a a' b b' hW).symm
  rw [map_mul, map_inv, he, mul_inv_cancel_right]

private theorem scalarShearAdmissible
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B)) (t : Rˣ) :
    ShearAdmissible Q w q R 0 (scalarParameter R t : (R ⊗[F] B)ˣ) := by
  refine ⟨h, ?_⟩
  change algebraMap R (R ⊗[F] B) t.val -
    antiValue (coefficientConjugation Q R) (algebraMap R (R ⊗[F] B) t.val) = _
  have he : antiValue (coefficientConjugation Q R) (algebraMap R (R ⊗[F] B) t.val) =
      algebraMap R (R ⊗[F] B) t.val := by
    change antiValue (coefficientConjugation Q R) ((t : R) ⊗ₜ[F] (1 : B)) =
      (t : R) ⊗ₜ[F] (1 : B)
    rw [extendAnti_tmul]
    simp [antiValue]
  simp only [he, sub_self, zero_mul, neg_zero]

private noncomputable def scalarInterchangeRatio
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B)) (t : Rˣ) :
    spinScalePreimage P Q R :=
  ⟨(interchangeLift Q P L w q R 0 (scalarParameter R t) (scalarShearAdmissible Q w q R h t) *
      (interchangeLift Q P L w q R 0 (scalarParameter R 1) (scalarShearAdmissible Q w q R h 1))⁻¹,
      scalarParameter R t), by
    change spinVectorProjection P R (_ * _⁻¹) = quaternionScale Q R (scalarParameter R t)
    calc
      _ = quaternionScale Q R (scalarParameter R t * (scalarParameter R 1)⁻¹) := by
        apply scale_of_interchange_ratio
        simp [interchangeMatrix]
      _ = _ := by
        rw [show scalarParameter (B := B) R 1 = 1 from map_one (Units.map _), inv_one, mul_one]⟩

end ScaleWords

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.CentralIsogenies (IsCentralIsogeny)
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

private theorem central_cover_commutator_lift {F : Type u} [Field F]
    {G H : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F} (p : G.val ⟶ H.val)
    (hp : IsCentralIsogeny p) (t : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    ∃ (C : H.val.X ⟶ G.val.X),
      ∀ (T : SchemeOver F) (x : T ⟶ G.val.X),
        (x ≫ p.hom.hom) ≫ C = (toUnit T ≫ t) * x * (toUnit T ≫ t)⁻¹ * x⁻¹ := by
  obtain ⟨_, hpflat, hpsurj, N, hN, hc⟩ := hp
  let _ : IsAffine G.val.X.left := G.property.1
  let _ : IsAffine H.val.X.left := H.property.1
  let _ := hpflat
  let _ := hpsurj
  let _ := isRegularEpi_of_flat_of_surjective_of_isAffine p.hom.hom.left
  let tG : G.val.X ⟶ G.val.X := toUnit G.val.X ≫ t
  let f : G.val.X ⟶ G.val.X := tG * (𝟙 G.val.X) * tG⁻¹ * (𝟙 G.val.X)⁻¹
  have hf {T : SchemeOver F} (x : T ⟶ G.val.X) :
      x ≫ f = (toUnit T ≫ t) * x * (toUnit T ≫ t)⁻¹ * x⁻¹ := by
    simp only [f, tG, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id, ← Category.assoc, comp_toUnit]
  have hrel {T : SchemeOver F} (a b : T ⟶ G.val.X)
      (hab : a ≫ p.hom.hom = b ≫ p.hom.hom) : a ≫ f = b ≫ f := by
    let v := a⁻¹ * b
    have hv : v ≫ p.hom.hom = 1 := by
      rw [show v = a⁻¹ * b from rfl, MonObj.mul_comp, GrpObj.inv_comp, hab, inv_mul_cancel]
    obtain ⟨n, hn⟩ := (schemeKernel_sections hN v).mpr hv
    change n ≫ N.inclusion.hom.hom = v at hn
    let tT := toUnit T ≫ t
    have ht : Commute v tT := by
      rw [← hn]
      simpa using (centralizes_iff _ _).mp hc T n tT
    have hb : b = a * v := by simp [v]
    rw [hf, hf]
    change tT * a * tT⁻¹ * a⁻¹ = tT * b * tT⁻¹ * b⁻¹
    rw [hb, mul_inv_rev]
    symm
    calc
      _ = tT * a * (v * tT⁻¹) * v⁻¹ * a⁻¹ := by group
      _ = _ := by rw [ht.inv_right.eq]; group
  have hrel' {T : Scheme.{u}} (a b : T ⟶ G.val.X.left)
      (hab : a ≫ p.hom.hom.left = b ≫ p.hom.hom.left) : a ≫ f.left = b ≫ f.left := by
    let V : SchemeOver F := Over.mk (a ≫ G.val.X.hom)
    let a' : V ⟶ G.val.X := Over.homMk a
    let b' : V ⟶ G.val.X := Over.homMk b (by
      change b ≫ G.val.X.hom = a ≫ G.val.X.hom
      rw [← Over.w p.hom.hom, ← Category.assoc, ← Category.assoc, hab])
    have he : a' ≫ p.hom.hom = b' ≫ p.hom.hom := Over.OverMorphism.ext hab
    exact congrArg (fun z => z.left) (hrel a' b' he)
  let d := EffectiveEpi.desc p.hom.hom.left f.left (fun a b => hrel' a b)
  have hd : p.hom.hom.left ≫ d = f.left :=
    EffectiveEpi.fac _ _ _
  let C : H.val.X ⟶ G.val.X := Over.homMk d (by
    apply (cancel_epi p.hom.hom.left).mp
    rw [← Category.assoc, hd, Over.w f, Over.w p.hom.hom])
  have hC : p.hom.hom ≫ C = f := Over.OverMorphism.ext hd
  refine ⟨C, fun T x => ?_⟩
  rw [Category.assoc, hC, hf]

private theorem shear_parameters_under_conjugation {F C : Type u} [Field F] [Ring C] [Algebra F C]
    (σ : C ≃ₐ[F] Cᵐᵒᵖ) (hs : Function.Involutive (antiValue σ))
    (q : Cˣ) (hq : antiValue σ (q : C) = -(q : C))
    (t : Fˣ) (ht : (t : F) ^ 2 ≠ 1) (a b : C)
    (h : b - antiValue σ b = -(a * ↑q⁻¹ * antiValue σ a)) :
    ∃ a₀ b₀ : C, b₀ - antiValue σ b₀ = -(a₀ * ↑q⁻¹ * antiValue σ a₀) ∧
      ((t : F) - 1) • a₀ = a ∧
      ((t : F) ^ 2 - 1) • b₀ + ((t : F) - 1) • (a₀ * ↑q⁻¹ * antiValue σ a₀) = b := by
  let s := (t : F) - 1
  let r := (t : F) ^ 2 - 1
  have hs0 : s ≠ 0 := by
    intro hz
    have ht1 : (t : F) = 1 := sub_eq_zero.mp hz
    exact ht (by rw [ht1, one_pow])
  have hr0 : r ≠ 0 := sub_ne_zero.mpr ht
  let a₀ : C := s⁻¹ • a
  let p : C := ↑q⁻¹
  let d := a₀ * p * antiValue σ a₀
  let b₀ : C := r⁻¹ • (b - s • d)
  have hbar_add (x y : C) : antiValue σ (x - y) = antiValue σ x - antiValue σ y := by
    simp [antiValue]
  have hbar_smul (x : C) (k : F) : antiValue σ (k • x) = k • antiValue σ x := by
    simp [antiValue]
  have hbar_mul (x y : C) : antiValue σ (x * y) = antiValue σ y * antiValue σ x := by
    simp [antiValue]
  have hbar_d : antiValue σ d = -d := by
    dsimp [d]
    rw [hbar_mul, hbar_mul, hs a₀, bar_inv_pure σ q hq, neg_mul, mul_neg, ← mul_assoc]
  have ha : s • a₀ = a := by
    simp only [a₀, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  have hb : r • b₀ = b - s • d := by
    simp only [b₀, smul_smul, mul_inv_cancel₀ hr0, one_smul]
  have ha₁ : a * p * antiValue σ a = (s * s) • d := by
    rw [← ha, hbar_smul, smul_mul_assoc, smul_mul_smul]
  have hmain : r • (b₀ - antiValue σ b₀) = r • (-d) := by
    rw [smul_sub, ← hbar_smul, hb, hbar_add, hbar_smul, hbar_d]
    have hh : b - antiValue σ b = -(s * s) • d := by
      rw [neg_smul, ← ha₁]
      exact h
    calc
      _ = (b - antiValue σ b) - s • d - s • d := by simp only [smul_neg]; abel
      _ = (-(s * s) - s - s) • d := by simp only [hh, sub_smul]
      _ = r • (-d) := by rw [smul_neg, ← neg_smul]; congr 1; dsimp [s, r]; ring
  have hproper : b₀ - antiValue σ b₀ = -d := by
    have h' := congrArg (fun x : C => r⁻¹ • x) hmain
    simpa only [smul_smul, inv_mul_cancel₀ hr0, one_smul] using h'
  exact ⟨a₀, b₀, hproper, ha, by rw [hb, sub_add_cancel]⟩

private theorem shear_matrix_products {F C : Type u} [CommRing F] [Ring C] [Algebra F C]
    (σ : C ≃ₐ[F] Cᵐᵒᵖ) (q : Cˣ) (a b a' b' : C) :
    upperShear σ q a b * upperShear σ q a' b' =
      upperShear σ q (a + a') (b + b' - a * ↑q⁻¹ * antiValue σ a') ∧
    lowerShear σ q a b * lowerShear σ q a' b' =
      lowerShear σ q (a + a') (b + b' - a * ↑q⁻¹ * antiValue σ a') := by
  have hbar (x y : C) : antiValue σ (x + y) = antiValue σ x + antiValue σ y := by simp [antiValue]
  constructor
  all_goals
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [upperShear, lowerShear, Matrix.mul_apply, Fin.sum_univ_three, hbar, mul_add]
    all_goals try simp only [← mul_assoc]
    all_goals abel

private theorem shear_scaling_commutator {F C : Type u} [Field F] [Ring C] [Algebra F C]
    (σ : C ≃ₐ[F] Cᵐᵒᵖ) (hs : Function.Involutive (antiValue σ))
    (q : Cˣ) (hq : antiValue σ (q : C) = -(q : C))
    (t : Fˣ) (ht : (t : F) ^ 2 ≠ 1) (a b : C)
    (h : b - antiValue σ b = -(a * ↑q⁻¹ * antiValue σ a)) :
    ∃ a₀ b₀ : C, b₀ - antiValue σ b₀ = -(a₀ * ↑q⁻¹ * antiValue σ a₀) ∧
      upperShear σ q ((t : F) • a₀) ((t : F) ^ 2 • b₀) *
        upperShear σ q (-a₀) (-antiValue σ b₀) = upperShear σ q a b ∧
      lowerShear σ q ((t : F) • a₀) ((t : F) ^ 2 • b₀) *
        lowerShear σ q (-a₀) (-antiValue σ b₀) = lowerShear σ q a b := by
  obtain ⟨a₀, b₀, h₀, hA, hB⟩ := shear_parameters_under_conjugation σ hs q hq t ht a b h
  have ha : (t : F) • a₀ + -a₀ = a := by
    rw [← hA, sub_smul ((t : F)) (1 : F), one_smul, sub_eq_add_neg]
  have hb : (t : F) ^ 2 • b₀ + -antiValue σ b₀ - (t : F) • a₀ * ↑q⁻¹ * antiValue σ (-a₀) = b := by
    simp only [show antiValue σ (-a₀) = -(antiValue σ a₀) by simp [antiValue],
      smul_mul_assoc, mul_neg, sub_neg_eq_add]
    let d := a₀ * (↑q⁻¹ : C) * antiValue σ a₀
    have hbar : antiValue σ b₀ = b₀ + d := by
      have hu := congrArg Neg.neg h₀
      rw [neg_sub, neg_neg] at hu
      calc
        _ = (antiValue σ b₀ - b₀) + b₀ := by abel
        _ = _ := by rw [hu, add_comm]
    rw [hbar]
    change (t : F) ^ 2 • b₀ + -(b₀ + d) + (t : F) • d = b
    calc
      _ = ((t : F) ^ 2 - 1) • b₀ + ((t : F) - 1) • d := by
        rw [sub_smul ((t : F) ^ 2) (1 : F) b₀, sub_smul (t : F) (1 : F) d, one_smul, one_smul]
        abel
      _ = _ := hB
  obtain ⟨hup, hlow⟩ := shear_matrix_products σ q ((t : F) • a₀) ((t : F) ^ 2 • b₀)
    (-a₀) (-antiValue σ b₀)
  rw [ha, hb] at hup hlow
  exact ⟨a₀, b₀, h₀, hup, hlow⟩

open LinearAlgebraicGroups.Specs (SubgroupSections)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open private hermitianValue_nondegenerate
  from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

section RadicalGeneration

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : LinearAlgebraicGroups.Specs.AffineAlgebraicGroup F}
  {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val}

private noncomputable abbrev rationalRadicals (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c)) :
    Subgroup (Points G.val.X (CommAlgCat.of F F)) :=
  SubgroupSections U.contracting ((testSpec F).obj (Opposite.op (CommAlgCat.of F F))) ⊔
    SubgroupSections V.contracting ((testSpec F).obj (Opposite.op (CommAlgCat.of F F)))

private theorem shearLift_mem_radicals (L : ShearLifts Q P c)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c))
    (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (a b : CommAlgCat.of F F ⊗[F] B)
    (hu : ShearAdmissible Q w q (CommAlgCat.of F F) a b) :
    L.lift upper w q (CommAlgCat.of F F) a b hu ∈ rationalRadicals U V := by
  cases upper
  · apply Subgroup.mem_sup_right
    exact (V.contracting_points _ _).mp (L.contracting false w q _ a b hu)
  · apply Subgroup.mem_sup_left
    exact (U.contracting_points _ _).mp (L.contracting true w q _ a b hu)

private def complementSkewPairing :
    SkewHermitianPairing (V := Fin d → B) Q.conjugation where
  value := hermitianValue Q.conjugation.anti Q.complement.val
  add_right x y z := by simp [hermitianValue, Matrix.mulVec_add, dotProduct_add]
  smul_right x y a := by
    have h : Q.complement.val *ᵥ (fun j => y j * a) =
      fun i => (Q.complement.val *ᵥ y) i * a := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
    change hermitianValue Q.conjugation.anti Q.complement.val x (fun j => y j * a) = _
    simp [hermitianValue, h, dotProduct, Finset.sum_mul, mul_assoc]
  skew x y := by
    rw [hermitianValue_rev Q.conjugation.anti Q.conjugation.square, complement_skew]
    simp only [hermitianValue, Matrix.neg_mulVec, dotProduct_neg, neg_neg]
  nondegenerate := hermitianValue_nondegenerate Q.conjugation.anti Q.complement

private theorem spin_scales_mem_radicals (h2 : (2 : F) ≠ 0) (hd : degree F B = 2) (hd₀ : 0 < d)
    (L : ShearLifts Q P c)
    (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
    (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
    (he : ∀ R x, (e R x).val.1 = x.val.2)
    (hn : ∀ t : (CommAlgCat.of F F ⊗[F] B)ˣ,
      (N (CommAlgCat.of F F) t : F) = reducedNorm hB (Algebra.TensorProduct.lid F B t.val))
    (hwords : NormalizedLiftedScaleWords Q P L N e)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c))
    (x : spinScalePreimage P Q (CommAlgCat.of F F)) : x.val.1 ∈ rationalRadicals U V := by
  let h := complementSkewPairing Q
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd₀
  have hex : ∃ v : Fin d → B, v ≠ 0 := ⟨1, one_ne_zero⟩
  obtain ⟨w, hw⟩ := exists_nonzero_self_pairing h h2 hB hd Q.canonical hex
  let q := Units.mk0 (h.value w w) hw
  have hq : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B) := rfl
  exact rational_scale_mem Q P L h2 hd w q hq (fixed_line_pure Q w q hq) N e he hn hwords
    (rationalRadicals U V) (shearLift_mem_radicals Q P L U V) x

end RadicalGeneration

section ShearMatrices

variable {F B : Type*} [CommRing F] [Ring B] [Algebra F B]

private def rectangularDagger {m n : Type*} (σ : B ≃ₐ[F] Bᵐᵒᵖ) (M : Matrix m n B) : Matrix n m B :=
  fun i j => antiValue σ (M j i)

private theorem rectangularDagger_mul {m n p : Type*} [Fintype n]
    (σ : B ≃ₐ[F] Bᵐᵒᵖ) (M : Matrix m n B) (N : Matrix n p B) :
    rectangularDagger σ (M * N) = rectangularDagger σ N * rectangularDagger σ M := by
  ext i j
  simp only [rectangularDagger, Matrix.mul_apply, antiValue,
    map_sum, map_mul, Finset.unop_sum, MulOpposite.unop_mul]

private theorem rectangularDagger_involutive {m n : Type*}
    (σ : B ≃ₐ[F] Bᵐᵒᵖ) (hσ : Function.Involutive (antiValue σ)) (M : Matrix m n B) :
    rectangularDagger σ (rectangularDagger σ M) = M := by
  ext i j
  exact hσ _

private theorem lineMatrix_isometry {d : ℕ} (σ : B ≃ₐ[F] Bᵐᵒᵖ)
    (w p : Fin d → B) (H : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)
    (J M : Matrix (Fin 3) (Fin 3) B)
    (hP : rectangularDagger σ (lineEmbedding w) * H = J * lineProjection p)
    (hE : H * lineEmbedding w = rectangularDagger σ (lineProjection p) * J)
    (hPE : lineProjection p * lineEmbedding w = 1)
    (hM : dagger σ M * J * M = J) :
    dagger σ (lineMatrix w p M) * H * lineMatrix w p M = H := by
  let E := lineEmbedding w
  let P := lineProjection p
  let X := M - 1
  let e := rectangularDagger σ E
  let p' := rectangularDagger σ P
  let x := dagger σ X
  have hd : dagger σ (lineMatrix w p M) = 1 + p' * x * e := by
    have h : rectangularDagger σ (1 : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [rectangularDagger, antiValue]
      · simp [rectangularDagger, hij, Ne.symm hij, antiValue]
    change rectangularDagger σ (1 + E * X * P) = _
    rw [show rectangularDagger σ (1 + E * X * P) =
      rectangularDagger σ 1 + rectangularDagger σ (E * X * P) by
        ext i j
        simp [rectangularDagger, antiValue]]
    rw [h, rectangularDagger_mul, rectangularDagger_mul]
    change 1 + p' * (x * e) = _
    rw [Matrix.mul_assoc]
  have hX : J * X + x * J + x * J * X = 0 := by
    have h : x = dagger σ M - 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [x, X, dagger, antiValue]
      · simp [x, X, dagger, hij, Ne.symm hij, antiValue]
    rw [h]
    calc
      _ = dagger σ M * J * M - J := by dsimp only [X]; noncomm_ring
      _ = 0 := by rw [hM, sub_self]
  change e * H = J * P at hP
  change H * E = p' * J at hE
  rw [hd]
  change (1 + p' * x * e) * H * (1 + E * X * P) = H
  calc
    _ = H + H * E * X * P + p' * x * (e * H) + p' * x * (e * H) * E * X * P := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
      abel
    _ = H + p' * (J * X + x * J + x * J * X) * P := by
      have hCross : p' * x * (e * H) * E * X * P = p' * x * J * X * P := by
        calc
          _ = p' * x * J * (P * E) * X * P := by rw [hP]; simp only [Matrix.mul_assoc]
          _ = _ := by rw [hPE, Matrix.mul_one]
      rw [hCross, hE, hP, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      abel
    _ = H := by simp [hX]

end ShearMatrices

section QuaternionShears

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private theorem gramAt_blocks (R : TestAlgebra F) :
    (gramAt Q R).val = quaternionHyperbolicGram (complementGram Q R) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [gramAt, quaternionGramUnit, quaternionHyperbolicGram]
  · simp [gramAt, quaternionGramUnit, quaternionHyperbolicGram]
  · simp [gramAt, quaternionGramUnit, quaternionHyperbolicGram]
  · rfl

private theorem gramAt_skew (R : TestAlgebra F) :
    dagger (coefficientConjugation Q R) (gramAt Q R).val = -(gramAt Q R).val := by
  rw [gramAt_blocks]
  have hW : dagger (coefficientConjugation Q R) (complementGram Q R) = -complementGram Q R := by
    ext i j
    change antiValue (coefficientConjugation Q R) (1 ⊗ₜ[F] Q.complement.val j i) =
      -(1 ⊗ₜ[F] Q.complement.val i j)
    rw [extendAnti_tmul, ← TensorProduct.tmul_neg]
    exact congrArg (fun b : B => (1 : R) ⊗ₜ[F] b)
      (congrFun (congrFun (complement_skew Q) i) j)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [dagger, quaternionHyperbolicGram, antiValue]
  · simp [dagger, quaternionHyperbolicGram, antiValue]
  · simp [dagger, quaternionHyperbolicGram, antiValue]
  · exact congrFun (congrFun hW i) j

private theorem lineGram_projection (R : TestAlgebra F) (w : Fin d → B) (q : Bˣ) :
    rectangularDagger (coefficientConjugation Q R) (lineEmbedding (extendedLine R w)) *
      (gramAt Q R).val =
    lineGram (extendedQ R q : (R ⊗[F] B)) * lineProjection (lineCoordinates Q R w q) := by
  rw [gramAt_blocks]
  ext i j
  rcases j with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [rectangularDagger, lineGram, lineEmbedding, lineProjection, quaternionHyperbolicGram,
        Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_three, antiValue]
  · fin_cases i <;>
      simp [rectangularDagger, lineGram, lineEmbedding, lineProjection, quaternionHyperbolicGram,
        Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_three,
        lineCoordinates, ← mul_assoc, antiValue]
    rw [← map_mul]
    rw [show (q : B) * (q : B)⁻¹ = 1 from mul_inv_cancel₀ q.ne_zero, map_one, one_mul]

private theorem extendedQ_pure (R : TestAlgebra F) (w : Fin d → B) (q : Bˣ)
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B)) :
    antiValue (coefficientConjugation Q R) (extendedQ R q : R ⊗[F] B) = -(extendedQ R q : R ⊗[F] B) := by
  change antiValue (coefficientConjugation Q R) (1 ⊗ₜ[F] (q : B)) = -(1 ⊗ₜ[F] (q : B))
  rw [extendAnti_tmul, fixed_line_pure Q w q h, TensorProduct.tmul_neg]

private theorem shear_preserves_gram (upper : Bool) (R : TestAlgebra F) (w : Fin d → B) (q : Bˣ)
    (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    let M := shearMatrix Q upper w q R a b
    dagger (coefficientConjugation Q R) M * (gramAt Q R).val * M = (gramAt Q R).val := by
  let σ := coefficientConjugation Q R
  let H := (gramAt Q R).val
  let J := lineGram (extendedQ R q : R ⊗[F] B)
  let E := lineEmbedding (extendedLine R w)
  let p := lineProjection (lineCoordinates Q R w q)
  have hσ : Function.Involutive (antiValue σ) := extendAnti_square (R := R) Q.conjugation.anti Q.conjugation.square
  have hq := extendedQ_pure Q R w q h.1
  have hH : rectangularDagger σ H = -H := gramAt_skew Q R
  have hJ : rectangularDagger σ J = -J := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, lineGram, rectangularDagger, antiValue]
    exact hq
  have hp : rectangularDagger σ E * H = J * p := lineGram_projection Q R w q
  have he : H * E = rectangularDagger σ p * J := by
    have ht := congrArg (rectangularDagger σ) hp
    rw [rectangularDagger_mul, rectangularDagger_mul, rectangularDagger_involutive σ hσ,
      hH, hJ, Matrix.neg_mul, Matrix.mul_neg] at ht
    exact neg_injective ht
  obtain ⟨hu, hl⟩ := shear_isometries σ hσ (extendedQ R q) hq a b h.2
  cases upper
  · dsimp only
    rw [← line_matrix_lower]
    exact lineMatrix_isometry σ _ _ H J _ hp he (lineProjection_leftInverse _ _ (lineCoordinates_splits Q R w q h.1)) hl
  · dsimp only
    rw [← line_matrix_upper]
    exact lineMatrix_isometry σ _ _ H J _ hp he (lineProjection_leftInverse _ _ (lineCoordinates_splits Q R w q h.1)) hu

end QuaternionShears

open LinearAlgebraicGroups.Specs (ClosedSubgroup IsSchemeKernel)
open LinearAlgebraicGroups.CocharacterDynamics
  (polynomialAlgebra laurentAlgebra polynomialToLaurent polynomialEvaluate laurentConstants
    laurentParameter HasLimit)
open RM03.CSA.NormOneGroup (normAt_natural normHom)

open private polynomialConstants polynomialConstants_laurent polynomialConstants_zero opposite_point
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

section ShearCoefficientMaps

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private theorem antiValue_scalar {R C : Type*} [CommRing R] [Ring C] [Algebra R C]
    (σ : C ≃ₐ[R] Cᵐᵒᵖ) (r : R) : antiValue σ (algebraMap R C r) = algebraMap R C r :=
  congrArg MulOpposite.unop (σ.commutes r)

private theorem antiValue_smul {R C : Type*} [CommRing R] [Ring C] [Algebra R C]
    (σ : C ≃ₐ[R] Cᵐᵒᵖ) (r : R) (x : C) : antiValue σ (r • x) = r • antiValue σ x := by
  simp [antiValue]

private theorem shear_zero (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F) :
    shearMatrix Q upper w q R 0 0 = 1 := by
  cases upper <;> ext i j <;> rcases i with i | i <;> rcases j with j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [shearMatrix, antiValue, Matrix.one_apply]

private theorem tensorMap_smul (R S : TestAlgebra F) (f : R ⟶ S)
    (r : R) (x : R ⊗[F] B) :
    tensorMap B f.hom (r • x) = f.hom r • tensorMap B f.hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    simp [tensorMap, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

private theorem tensorMap_ground (R S : TestAlgebra F) (f : R ⟶ S) (x : B) :
    tensorMap B f.hom (intoTensor R B x) = intoTensor S B x := by
  simp [tensorMap, intoTensor]

private theorem shearMatrix_map (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R S : TestAlgebra F) (f : R ⟶ S) (a b : R ⊗[F] B) :
    (shearMatrix Q upper w q R a b).map (tensorMap B f.hom) =
      shearMatrix Q upper w q S (tensorMap B f.hom a) (tensorMap B f.hom b) := by
  have hcomp (i j : Fin d) : tensorMap B f.hom (complementGram Q R i j) = complementGram Q S i j :=
    tensorMap_ground R S f _
  have htmul (x : B) : tensorMap B f.hom (1 ⊗ₜ[F] x) = 1 ⊗ₜ[F] x :=
    tensorMap_ground R S f x
  cases upper <;> ext i j <;> rcases i with i | i <;> rcases j with j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [shearMatrix, ← coefficientConjugation_map, hcomp, Matrix.one_apply, htmul]

private theorem shearAdmissible_map (w : Fin d → B) (q : Bˣ)
    (R S : TestAlgebra F) (f : R ⟶ S) (a b : R ⊗[F] B)
    (h : ShearAdmissible Q w q R a b) :
    ShearAdmissible Q w q S (tensorMap B f.hom a) (tensorMap B f.hom b) := by
  refine ⟨h.1, ?_⟩
  have hh := congrArg (tensorMap B f.hom) h.2
  change tensorMap B f.hom b - antiValue (coefficientConjugation Q S) (tensorMap B f.hom b) =
    -(tensorMap B f.hom a * intoTensor S B (↑q⁻¹ : B) *
      antiValue (coefficientConjugation Q S) (tensorMap B f.hom a))
  simpa only [map_sub, map_neg, map_mul, ← coefficientConjugation_map,
    show (1 : R) ⊗ₜ[F] (↑q⁻¹ : B) = intoTensor R B (↑q⁻¹ : B) from rfl, tensorMap_ground] using hh

private theorem shearAdmissible_smul (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
    (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) (t : R) :
    ShearAdmissible Q w q R (t • a) (t ^ 2 • b) := by
  refine ⟨h.1, ?_⟩
  rw [antiValue_smul, antiValue_smul, ← smul_sub, h.2, smul_mul_assoc, smul_mul_smul, pow_two, smul_neg]

private theorem shearMatrix_mul (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b a' b' : R ⊗[F] B)
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B)) :
    shearMatrix Q upper w q R a b * shearMatrix Q upper w q R a' b' =
      shearMatrix Q upper w q R (a + a')
        (b + b' - a * (↑(extendedQ R q)⁻¹ : R ⊗[F] B) * antiValue (coefficientConjugation Q R) a') := by
  obtain ⟨hu, hl⟩ := shear_matrix_products (F := R) (coefficientConjugation Q R) (extendedQ R q) a b a' b'
  have hm := lineMatrix_mul _ _ (lineCoordinates_splits Q R w q h)
  cases upper
  · rw [← line_matrix_lower, ← line_matrix_lower, ← hm, hl, line_matrix_lower]
  · rw [← line_matrix_upper, ← line_matrix_upper, ← hm, hu, line_matrix_upper]

private theorem shear_isUnit (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B)
    (h : ShearAdmissible Q w q R a b) : IsUnit (shearMatrix Q upper w q R a b) := by
  let z := a * (↑(extendedQ R q)⁻¹ : R ⊗[F] B) * antiValue (coefficientConjugation Q R) a
  let M := shearMatrix Q upper w q R a b
  let N := shearMatrix Q upper w q R (-a) (-(b + z))
  have hz : a * (↑(extendedQ R q)⁻¹ : R ⊗[F] B) * antiValue (coefficientConjugation Q R) a = z := rfl
  have hn : antiValue (coefficientConjugation Q R) (-a) =
      -(antiValue (coefficientConjugation Q R) a) := by simp [antiValue]
  refine ⟨⟨M, N, ?_, ?_⟩, rfl⟩
  · change shearMatrix Q upper w q R a b * N = 1
    rw [show N = shearMatrix Q upper w q R (-a) (-(b + z)) from rfl,
      shearMatrix_mul Q upper w q R _ _ _ _ h.1, add_neg_cancel, hn, mul_neg, hz]
    rw [show b + -(b + z) - -z = 0 by abel]
    exact shear_zero Q upper w q R
  · change N * shearMatrix Q upper w q R a b = 1
    rw [show N = shearMatrix Q upper w q R (-a) (-(b + z)) from rfl,
      shearMatrix_mul Q upper w q R _ _ _ _ h.1, neg_add_cancel, neg_mul, neg_mul, hz]
    rw [show -(b + z) + b - -z = 0 by abel]
    exact shear_zero Q upper w q R

private theorem scalarScale_matrix (R : TestAlgebra F) (t : Rˣ) :
    Q.matrixAt R (quaternionScale Q R (scalarParameter R t)).val =
      (Matrix.diagonal (Sum.elim ![algebraMap R (R ⊗[F] B) t.val,
        algebraMap R (R ⊗[F] B) t.inv] (fun _ : Fin d => 1))) := by
  rw [scale_matrix]
  congr 1
  funext i
  rcases i with i | i
  · fin_cases i
    · rfl
    · exact antiValue_scalar (coefficientConjugation Q R) t.inv
  · rfl

private theorem scalarScale_conjugates_shear (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (t : Rˣ) :
    let s := if upper then t else t⁻¹
    Q.matrixAt R (quaternionScale Q R (scalarParameter R s)).val *
      shearMatrix Q upper w q R a b *
      Q.matrixAt R (quaternionScale Q R (scalarParameter R s⁻¹)).val =
      shearMatrix Q upper w q R ((t : R) • a) ((t : R) ^ 2 • b) := by
  classical
  cases upper <;> dsimp only [Bool.false_eq_true, ite_false, ite_true] <;>
    rw [scalarScale_matrix, scalarScale_matrix] <;> ext i j <;>
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] <;>
    rcases i with i | i <;> rcases j with j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals
    simp [shearMatrix, antiValue_smul, pow_two, smul_smul, smul_mul_assoc,
      mul_smul_comm, smul_neg, Algebra.smul_def, Units.inv_mul, Units.mul_inv,
      mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, ← Algebra.TensorProduct.one_def]
  all_goals
    rw [show b * (↑t ⊗ₜ[F] 1 : R ⊗[F] B) = (↑t ⊗ₜ[F] 1) * b from
      (Algebra.commutes (R := R) (t : R) b).symm, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end ShearCoefficientMaps

section DoubleCover

variable {F : Type u} [Field F] {G H : AffineAlgebraicGroup F}
  (p : G.val ⟶ H.val)

private theorem cancel_after_lifting (hp : IsCentralIsogeny p) {T X : SchemeOver F}
    (y : T ⟶ H.val.X) {a b : T ⟶ X}
    (h : ∀ (S : SchemeOver F) (f : S ⟶ T) (x : S ⟶ G.val.X),
      f ≫ y = x ≫ p.hom.hom → f ≫ a = f ≫ b) : a = b := by
  let π := pullback.fst y p.hom.hom
  let q := pullback.snd y p.hom.hom
  have hpull : IsPullback π.left q.left y.left p.hom.hom.left :=
    (IsPullback.of_hasPullback _ _).map (Over.forget _)
  letI : Flat π.left := MorphismProperty.of_isPullback hpull.flip hp.2.1
  letI : Surjective π.left := MorphismProperty.of_isPullback hpull.flip hp.2.2.1
  letI : Epi π := (Over.forget _).epi_of_epi_map (f := π) (Flat.epi_of_flat_of_surjective π.left)
  exact (cancel_epi π).mp (h _ π q pullback.condition)

private theorem two_torsion_sections (N : ClosedSubgroup G.val)
    (hN : ∀ (R : TestAlgebra F) (z : Points N.group.X R), z * z = 1)
    (T : SchemeOver F) (z : T ⟶ N.group.X) : z * z = 1 := by
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  have ha : IsAffine N.group.X.left := isAffine_of_isAffineHom N.inclusion.hom.hom.left
  obtain ⟨A, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of F)).mpr ha
  let t := z ≫ e.inv
  have hz : z = t ≫ e.hom := by simp [t]
  rw [hz, ← MonObj.comp_mul, hN A.unop e.hom, MonObj.comp_one]

/-- Squaring is independent of the lift through a central cover with
two-torsion kernel. Descent gives the same operation on every test scheme. -/
private theorem square_descends (hp : IsCentralIsogeny p)
    (N : ClosedSubgroup G.val) (hN : IsSchemeKernel p N)
    (hN2 : ∀ (R : TestAlgebra F) (z : Points N.group.X R), z * z = 1) :
    ∃ C : H.val.X ⟶ G.val.X,
      ∀ (T : SchemeOver F) (x : T ⟶ G.val.X), (x ≫ p.hom.hom) ≫ C = x * x := by
  obtain ⟨_, hpflat, hpsurj, M, hM, hc⟩ := hp
  let _ : IsAffine G.val.X.left := G.property.1
  let _ : IsAffine H.val.X.left := H.property.1
  let _ := hpflat
  let _ := hpsurj
  let _ := isRegularEpi_of_flat_of_surjective_of_isAffine p.hom.hom.left
  let f : G.val.X ⟶ G.val.X := (𝟙 G.val.X) * (𝟙 G.val.X)
  have hf {T : SchemeOver F} (x : T ⟶ G.val.X) : x ≫ f = x * x := by
    simp only [f, MonObj.comp_mul, Category.comp_id]
  have hrel {T : SchemeOver F} (a b : T ⟶ G.val.X)
      (hab : a ≫ p.hom.hom = b ≫ p.hom.hom) : a ≫ f = b ≫ f := by
    let v := a⁻¹ * b
    have hv : v ≫ p.hom.hom = 1 := by
      rw [show v = a⁻¹ * b from rfl, MonObj.mul_comp, GrpObj.inv_comp, hab, inv_mul_cancel]
    obtain ⟨n, hn⟩ := (schemeKernel_sections hN v).mpr hv
    obtain ⟨m, hm⟩ := (schemeKernel_sections hM v).mpr hv
    change T ⟶ N.group.X at n
    change T ⟶ M.group.X at m
    change n ≫ N.inclusion.hom.hom = v at hn
    change m ≫ M.inclusion.hom.hom = v at hm
    have hv2 : v * v = 1 := by
      rw [← hn, ← MonObj.mul_comp, two_torsion_sections N hN2 T n, MonObj.one_comp]
    have hcomm : Commute v a := by
      rw [← hm]
      simpa using (centralizes_iff _ _).mp hc T m a
    have hb : b = a * v := by simp [v]
    rw [hf, hf, hb]
    symm
    calc
      _ = a * (v * a) * v := by simp only [mul_assoc]
      _ = _ := by rw [hcomm.eq]; simp [mul_assoc, hv2]
  have hrel' {T : Scheme.{u}} (a b : T ⟶ G.val.X.left)
      (hab : a ≫ p.hom.hom.left = b ≫ p.hom.hom.left) : a ≫ f.left = b ≫ f.left := by
    let V : SchemeOver F := Over.mk (a ≫ G.val.X.hom)
    let a' : V ⟶ G.val.X := Over.homMk a
    let b' : V ⟶ G.val.X := Over.homMk b (by
      change b ≫ G.val.X.hom = a ≫ G.val.X.hom
      rw [← Over.w p.hom.hom, ← Category.assoc, ← Category.assoc, hab])
    have he : a' ≫ p.hom.hom = b' ≫ p.hom.hom := Over.OverMorphism.ext hab
    exact congrArg (fun z => z.left) (hrel a' b' he)
  let d := EffectiveEpi.desc p.hom.hom.left f.left (fun a b => hrel' a b)
  have hd : p.hom.hom.left ≫ d = f.left := EffectiveEpi.fac _ _ _
  let C : H.val.X ⟶ G.val.X := Over.homMk d (by
    apply (cancel_epi p.hom.hom.left).mp
    rw [← Category.assoc, hd, Over.w f, Over.w p.hom.hom])
  have hC : p.hom.hom ≫ C = f := Over.OverMorphism.ext hd
  refine ⟨C, fun T x => ?_⟩
  rw [Category.assoc, hC, hf]

private theorem descended_square_projection (hp : IsCentralIsogeny p)
    (C : H.val.X ⟶ G.val.X)
    (hC : ∀ (T : SchemeOver F) (x : T ⟶ G.val.X), (x ≫ p.hom.hom) ≫ C = x * x)
    {T : SchemeOver F} (y : T ⟶ H.val.X) :
    (y ≫ C) ≫ p.hom.hom = y * y := by
  apply cancel_after_lifting p hp y
  intro S f x hx
  rw [← Category.assoc, ← Category.assoc, hx, hC, MonObj.comp_mul, hx, MonObj.mul_comp]

private theorem descended_square_conjugation (hp : IsCentralIsogeny p)
    (C : H.val.X ⟶ G.val.X)
    (hC : ∀ (T : SchemeOver F) (x : T ⟶ G.val.X), (x ≫ p.hom.hom) ≫ C = x * x)
    {T : SchemeOver F} (y : T ⟶ H.val.X) (a : T ⟶ G.val.X) :
    ((a ≫ p.hom.hom) * y * (a ≫ p.hom.hom)⁻¹) ≫ C =
      a * (y ≫ C) * a⁻¹ := by
  apply cancel_after_lifting p hp y
  intro S f x hx
  calc
    _ = (((f ≫ a) * x * (f ≫ a)⁻¹) ≫ p.hom.hom) ≫ C := by
      simp only [← Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp,
        GrpObj.inv_comp, hx]
    _ = ((f ≫ a) * x * (f ≫ a)⁻¹) * ((f ≫ a) * x * (f ≫ a)⁻¹) := hC _ _
    _ = (f ≫ a) * (x * x) * (f ≫ a)⁻¹ := by group
    _ = _ := by simp only [← Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, hx, hC]

end DoubleCover

section NeutralShears

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private theorem tensorMap_comp (A : Type u) [Ring A] [Algebra F A]
    (R S T : TestAlgebra F) (f : R ⟶ S) (g : S ⟶ T) (x : R ⊗[F] A) :
    tensorMap A g.hom (tensorMap A f.hom x) = tensorMap A (f ≫ g).hom x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private noncomputable def shearVectorUnit (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    (R ⊗[F] ρ.fixedSubalgebra)ˣ :=
  Units.map (Q.matrixAt R).symm.toMonoidHom (shear_isUnit Q upper w q R a b h).unit

private theorem shearVectorUnit_matrix (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    Q.matrixAt R (shearVectorUnit Q upper w q R a b h).val = shearMatrix Q upper w q R a b := by
  change Q.matrixAt R ((Q.matrixAt R).symm (shear_isUnit Q upper w q R a b h).unit.val) = _
  rw [AlgEquiv.apply_symm_apply, IsUnit.unit_spec]

/-- The norm of the polynomial shear family is constant after inverting
the parameter, where the family is a conjugate of the fixed shear. -/
private theorem shearVectorUnit_norm (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b)
    {J : Type*} [Fintype J] (basis : Module.Basis J F ρ.fixedSubalgebra) :
    normAt D.centralSimple basis (shearVectorUnit Q upper w q R a b h).val = 1 := by
  let A := ρ.fixedSubalgebra
  let S := polynomialAlgebra R
  let T := laurentAlgebra R
  let f := polynomialConstants R
  let j := polynomialToLaurent R
  let k := laurentConstants R
  let e := polynomialEvaluate R 0
  let t := laurentParameter R
  let g := shearVectorUnit Q upper w q R a b h
  let a' : S ⊗[F] B := (Polynomial.X : S) • tensorMap B f.hom a
  let b' : S ⊗[F] B := (Polynomial.X : S) ^ 2 • tensorMap B f.hom b
  let h' : ShearAdmissible Q w q S a' b' :=
    shearAdmissible_smul Q w q S _ _ (shearAdmissible_map Q w q R S f a b h) _
  let g' := shearVectorUnit Q upper w q S a' b' h'
  let u := if upper then t else t⁻¹
  let s := quaternionScale Q T (scalarParameter T u)
  have ht : j.hom (Polynomial.X : S) = (t : T) := Polynomial.toLaurent_X
  have hc (x : R ⊗[F] B) : tensorMap B j.hom (tensorMap B f.hom x) = tensorMap B k.hom x := by
    rw [tensorMap_comp, show f ≫ j = k from polynomialConstants_laurent R]
  have hconj : tensorMap A j.hom g'.val =
      s.val * tensorMap A k.hom g.val * s.inv := by
    apply (Q.matrixAt T).injective
    rw [matrixAt_map, shearVectorUnit_matrix, shearMatrix_map, tensorMap_smul, tensorMap_smul,
      hc, hc, map_pow, ht, map_mul, map_mul, matrixAt_map, shearVectorUnit_matrix, shearMatrix_map]
    have hsinv : s.inv = (quaternionScale Q T (scalarParameter T u⁻¹)).val := by
      change (s⁻¹ : (T ⊗[F] A)ˣ).val = _
      apply congrArg Units.val
      exact (map_inv ((quaternionScale Q T).comp (Units.map
        (algebraMap T (T ⊗[F] B)).toMonoidHom)) u).symm
    rw [hsinv]
    exact (scalarScale_conjugates_shear Q upper w q T _ _ t).symm
  let nr : (R ⊗[F] A) →* R := normHom D.centralSimple basis
  let ns : (S ⊗[F] A) →* S := normHom D.centralSimple basis
  let nt : (T ⊗[F] A) →* T := normHom D.centralSimple basis
  have hw : ns g'.val = f.hom (nr g.val) := by
    apply Polynomial.toLaurent_injective
    change j.hom (ns g'.val) = j.hom (f.hom (nr g.val))
    rw [← show k.hom (nr g.val) = j.hom (f.hom (nr g.val)) from
      congrArg (fun m : R ⟶ T => m.hom (nr g.val)) (polynomialConstants_laurent R).symm]
    rw [← show nt (tensorMap A j.hom g'.val) = j.hom (ns g'.val) from
        normAt_natural D.centralSimple basis j.hom g'.val,
      ← show nt (tensorMap A k.hom g.val) = k.hom (nr g.val) from
        normAt_natural D.centralSimple basis k.hom g.val, hconj]
    rw [map_mul, map_mul, mul_right_comm (nt s.val), ← map_mul, s.val_inv, map_one, one_mul]
  have hz : e.hom (Polynomial.X : S) = 0 := Polynomial.eval₂_X _ _
  have hg0 : tensorMap A e.hom g'.val = 1 := by
    apply (Q.matrixAt R).injective
    change Q.matrixAt R (tensorMap A e.hom g'.val) = Q.matrixAt R 1
    rw [matrixAt_map, shearVectorUnit_matrix, shearMatrix_map, map_one, tensorMap_smul, tensorMap_smul,
      map_pow, hz, zero_pow (by decide), zero_smul, zero_smul, shear_zero]
  change nr g.val = 1
  calc
    nr g.val = e.hom (f.hom (nr g.val)) := by
      exact congrArg (fun m : R ⟶ R => m.hom (nr g.val)) (polynomialConstants_zero R).symm
    _ = e.hom (ns g'.val) := congrArg e.hom hw.symm
    _ = nr (tensorMap A e.hom g'.val) := (normAt_natural D.centralSimple basis e.hom g'.val).symm
    _ = 1 := by rw [hg0, map_one]

private noncomputable def neutralMatrixUnits (R : TestAlgebra F) :
    Points P.neutral.val.X R →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B))ˣ :=
  (Units.map (Q.matrixAt R).toMonoidHom).comp
    ((P.fullPoints R).comp (((groupPointsFunctor F).map P.inclusion).app R).hom)

private theorem neutralMatrixUnits_injective (R : TestAlgebra F) :
    Function.Injective (neutralMatrixUnits Q P R) := by
  intro x y h
  letI : IsClosedImmersion P.inclusion.hom.hom.left := P.closedImmersion
  letI : Mono P.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono P.inclusion.hom.hom).mp
  apply P.fullFaithful R
  apply Units.ext
  apply (Q.matrixAt R).injective
  exact congrArg Units.val h

private theorem neutralMatrixUnits_map (R S : TestAlgebra F) (f : R ⟶ S)
    (x : Points P.neutral.val.X R) :
    (neutralMatrixUnits Q P S (mapPoints f x)).val =
      (neutralMatrixUnits Q P R x).val.map (tensorMap B f.hom) := by
  change Q.matrixAt S (P.fullPoints S (mapPoints f x ≫ P.inclusion.hom.hom)).val = _
  rw [show mapPoints f x ≫ P.inclusion.hom.hom = mapPoints f (x ≫ P.inclusion.hom.hom)
    from Category.assoc _ _ _, P.fullNatural]
  exact matrixAt_map Q R S f _

set_option maxHeartbeats 1200000 in
private theorem neutralShear_exists (h2 : (2 : F) ≠ 0)
    (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    ∃ x : Points P.neutral.val.X R, (neutralMatrixUnits Q P R x).val =
      shearMatrix Q upper w q R a b := by
  obtain ⟨n, basis, hneutral⟩ := P.reducedNormOne h2
  let g := shearVectorUnit Q upper w q R a b h
  have hg : Q.matrixAt R g.val = shearMatrix Q upper w q R a b :=
    shearVectorUnit_matrix Q upper w q R a b h
  have hi : (D.involution.baseChange R).toLinearMap g.val * g.val = 1 := by
    apply (isometry_iff_gram Q R g).mpr
    rw [hg]
    exact shear_preserves_gram Q upper R w q a b h
  have hn := shearVectorUnit_norm Q upper w q R a b h (J := Fin n) basis
  have hp : ∃ x : Points P.neutral.val.X R, P.fullPoints R (x ≫ P.inclusion.hom.hom) = g :=
    (hneutral R g).mpr ⟨hi, hn⟩
  obtain ⟨x, hx⟩ := hp
  refine ⟨x, ?_⟩
  change Q.matrixAt R (P.fullPoints R (x ≫ P.inclusion.hom.hom)).val = shearMatrix Q upper w q R a b
  have he := congrArg (fun z : (R ⊗[F] ρ.fixedSubalgebra)ˣ => Q.matrixAt R z.val) hx
  exact he.trans hg

private noncomputable def neutralShear (h2 : (2 : F) ≠ 0)
    (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    Points P.neutral.val.X R :=
  (neutralShear_exists Q P h2 upper w q R a b h).choose

private theorem neutralShear_matrix (h2 : (2 : F) ≠ 0)
    (upper : Bool) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    (neutralMatrixUnits Q P R (neutralShear Q P h2 upper w q R a b h)).val =
      shearMatrix Q upper w q R a b :=
  (neutralShear_exists Q P h2 upper w q R a b h).choose_spec

end NeutralShears

section ContractingShears

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private abbrev inverseTwo (R : TestAlgebra F) : R := algebraMap F R ((2 : F)⁻¹)

private theorem inverseTwo_add (h2 : (2 : F) ≠ 0) (R : TestAlgebra F) :
    inverseTwo R + inverseTwo R = 1 := by
  rw [← map_add, ← two_mul, mul_inv_cancel₀ h2, map_one]

private def halfShearFirst (R : TestAlgebra F) (a : R ⊗[F] B) : R ⊗[F] B :=
  inverseTwo R • a

private noncomputable def shearCross (q : Bˣ) (R : TestAlgebra F) (a : R ⊗[F] B) : R ⊗[F] B :=
  a * (↑(extendedQ R q)⁻¹ : R ⊗[F] B) * antiValue (coefficientConjugation Q R) a

private noncomputable def halfShearSecond (q : Bˣ) (R : TestAlgebra F) (a b : R ⊗[F] B) :
    R ⊗[F] B :=
  inverseTwo R • (b + shearCross Q q R (halfShearFirst R a))

private theorem square_shear_parameters (h2 : (2 : F) ≠ 0) (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
    let a₀ := halfShearFirst R a
    let b₀ := halfShearSecond Q q R a b
    ShearAdmissible Q w q R a₀ b₀ ∧
      a₀ + a₀ = a ∧ b₀ + b₀ - shearCross Q q R a₀ = b := by
  dsimp only
  let a₀ := halfShearFirst R a
  let b₀ := halfShearSecond Q q R a b
  let m := inverseTwo R
  let p := (↑(extendedQ R q)⁻¹ : R ⊗[F] B)
  let σ := coefficientConjugation Q R
  let z := shearCross Q q R a₀
  have hm : m + m = 1 := inverseTwo_add h2 R
  have ha : a₀ + a₀ = a := by
    change m • a + m • a = a
    rw [← add_smul, hm, one_smul]
  have hb : b₀ + b₀ = b + z := by
    change m • (b + z) + m • (b + z) = b + z
    rw [← add_smul, hm, one_smul]
  have hσ := extendAnti_square (R := R) Q.conjugation.anti Q.conjugation.square
  have hp : antiValue σ p = -p := bar_inv_pure σ _ (extendedQ_pure Q R w q h.1)
  have hz : antiValue σ z = -z := by
    change antiValue σ (a₀ * p * antiValue σ a₀) = -(a₀ * p * antiValue σ a₀)
    rw [bar_mul, bar_mul, hσ a₀, hp, neg_mul, mul_neg, ← mul_assoc]
  have hadd (x y : R ⊗[F] B) : antiValue σ (x + y) = antiValue σ x + antiValue σ y := by
    simp [antiValue]
  have hcross : a * p * antiValue σ a = z + z + z + z := by
    rw [← ha, hadd]
    change (a₀ + a₀) * p * (antiValue σ a₀ + antiValue σ a₀) =
      (a₀ * p * antiValue σ a₀) + (a₀ * p * antiValue σ a₀) +
        (a₀ * p * antiValue σ a₀) + (a₀ * p * antiValue σ a₀)
    simp only [add_mul, mul_add]
    abel
  refine ⟨⟨h.1, ?_⟩, ha, by rw [hb, add_sub_cancel_right]⟩
  change b₀ - antiValue σ b₀ = -z
  have hh := h.2
  change b - antiValue σ b = -(a * p * antiValue σ a) at hh
  rw [hcross] at hh
  have hbbar := congrArg (antiValue σ) hb
  rw [hadd, hadd, hz] at hbbar
  have hd : (b₀ - antiValue σ b₀) + (b₀ - antiValue σ b₀) = -z + -z := by
    calc
      _ = (b₀ + b₀) - (antiValue σ b₀ + antiValue σ b₀) := by abel
      _ = (b - antiValue σ b) + z + z := by rw [hb, hbbar]; abel
      _ = _ := by rw [hh]; abel
  have ht := congrArg (m • ·) hd
  simpa only [smul_add, ← add_smul m m, hm, one_smul] using ht

private theorem halfShearFirst_map (R S : TestAlgebra F) (f : R ⟶ S) (a : R ⊗[F] B) :
    tensorMap B f.hom (halfShearFirst R a) = halfShearFirst S (tensorMap B f.hom a) := by
  rw [halfShearFirst, tensorMap_smul, f.hom.commutes]
  rfl

private theorem halfShearSecond_map (q : Bˣ) (R S : TestAlgebra F) (f : R ⟶ S) (a b : R ⊗[F] B) :
    tensorMap B f.hom (halfShearSecond Q q R a b) =
      halfShearSecond Q q S (tensorMap B f.hom a) (tensorMap B f.hom b) := by
  unfold halfShearSecond shearCross
  rw [tensorMap_smul, f.hom.commutes, map_add, map_mul, map_mul,
    ← coefficientConjugation_map, halfShearFirst_map]
  have hn : tensorMap B f.hom (↑(extendedQ R q)⁻¹ : R ⊗[F] B) = (↑(extendedQ S q)⁻¹ : S ⊗[F] B) :=
    tensorMap_ground R S f (↑q⁻¹ : B)
  rw [hn]

private theorem halfShearFirst_smul (R : TestAlgebra F) (t : R) (a : R ⊗[F] B) :
    halfShearFirst R (t • a) = t • halfShearFirst R a := by
  simp only [halfShearFirst, smul_smul, mul_comm (inverseTwo R) t]

private theorem halfShearSecond_smul (q : Bˣ) (R : TestAlgebra F) (t : R) (a b : R ⊗[F] B) :
    halfShearSecond Q q R (t • a) (t ^ 2 • b) = t ^ 2 • halfShearSecond Q q R a b := by
  unfold halfShearSecond shearCross
  rw [halfShearFirst_smul, antiValue_smul, smul_mul_assoc, smul_mul_smul,
    ← pow_two, ← smul_add, smul_smul, smul_smul, mul_comm (inverseTwo R)]

private theorem kernel_squares (R : TestAlgebra F) (x : Points P.kernel.group.X R) :
    x * x = 1 := by
  apply (P.kernelPoints R).injective
  rw [map_mul, map_one, ← pow_two]
  apply Subtype.ext
  exact (mem_rootsOfUnity 2 (P.kernelPoints R x).val).mp (P.kernelPoints R x).property

private theorem contracting_shear_lifts (h2 : (2 : F) ≠ 0) (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t)) :
    ∃ L : ShearLifts Q P c, ∀ upper w q R h, L.lift upper w q R 0 0 h = 1 := by
  obtain ⟨C, hC⟩ := square_descends P.projection P.centralIsogeny P.kernel P.isKernel (kernel_squares P)
  let half (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
      (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) : Points P.neutral.val.X R :=
    neutralShear Q P h2 upper w q R (halfShearFirst R a) (halfShearSecond Q q R a b)
      (square_shear_parameters Q h2 w q R a b h).1
  let lift (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
      (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) : Points G.val.X R :=
    half upper w q R a b h ≫ C
  have hhalf (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
      (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
      (neutralMatrixUnits Q P R (half upper w q R a b h)).val =
        shearMatrix Q upper w q R (halfShearFirst R a) (halfShearSecond Q q R a b) :=
    neutralShear_matrix Q P h2 upper w q R _ _ _
  have hnatural (upper : Bool) (w : Fin d → B) (q : Bˣ) (R S : TestAlgebra F) (f : R ⟶ S)
      (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b)
      (h' : ShearAdmissible Q w q S (tensorMap B f.hom a) (tensorMap B f.hom b)) :
      mapPoints f (lift upper w q R a b h) =
        lift upper w q S (tensorMap B f.hom a) (tensorMap B f.hom b) h' := by
    change mapPoints f (half upper w q R a b h) ≫ C =
      half upper w q S (tensorMap B f.hom a) (tensorMap B f.hom b) h' ≫ C
    apply congrArg (· ≫ C)
    apply neutralMatrixUnits_injective Q P S
    apply Units.ext
    rw [neutralMatrixUnits_map, hhalf upper w q R a b h, hhalf upper w q S _ _ h',
      shearMatrix_map, halfShearFirst_map, halfShearSecond_map]
  have hformula (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
      (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
      vectorMatrix Q P R (lift upper w q R a b h) = shearMatrix Q upper w q R a b := by
    let x := half upper w q R a b h
    change (neutralMatrixUnits Q P R ((x ≫ C) ≫ P.projection.hom.hom)).val = _
    rw [descended_square_projection _ P.centralIsogeny C hC x, map_mul, Units.val_mul]
    rw [show x = half upper w q R a b h from rfl, hhalf upper w q R a b h,
      shearMatrix_mul Q upper w q R _ _ _ _ h.1]
    have hpar := (square_shear_parameters Q h2 w q R a b h).2
    rw [hpar.1]
    exact congrArg (shearMatrix Q upper w q R a) hpar.2
  have hzero (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
      (h : ShearAdmissible Q w q R 0 0) : lift upper w q R 0 0 h = 1 := by
    have hx : half upper w q R 0 0 h = 1 := by
      apply neutralMatrixUnits_injective Q P R
      apply Units.ext
      rw [hhalf upper w q R 0 0 h, map_one, Units.val_one]
      simpa only [halfShearFirst, halfShearSecond, shearCross, smul_zero, zero_mul, add_zero] using
        shear_zero Q upper w q R
    change half upper w q R 0 0 h ≫ C = 1
    rw [hx, ← show (1 : Points G.val.X R) ≫ P.projection.hom.hom = 1 from MonObj.one_comp _,
      hC, one_mul]
  have hscale (upper : Bool) (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F) (t : Rˣ)
      (a b : R ⊗[F] B) (h : ShearAdmissible Q w q R a b) :
      let g : Points G.val.X R := cocharacterPoint (if upper then c else oppositeCocharacter c) R t
      lift upper w q R ((t : R) • a) ((t : R) ^ 2 • b)
        (shearAdmissible_smul Q w q R a b h ↑t) = g * lift upper w q R a b h * g⁻¹ := by
    let g : Points G.val.X R := cocharacterPoint (if upper then c else oppositeCocharacter c) R t
    let a₀ := half upper w q R a b h
    let s := if upper then t else t⁻¹
    let gt : Points P.neutral.val.X R := g ≫ P.projection.hom.hom
    have hh : spinVectorProjection P R g = quaternionScale Q R (scalarParameter R s) := by
      cases upper
      · simpa only [g, s, Bool.false_eq_true, ite_false, opposite_point] using hc R t⁻¹
      · exact hc R t
    have hti : (neutralMatrixUnits Q P R gt).val = Q.matrixAt R (quaternionScale Q R (scalarParameter R s)).val :=
      congrArg (fun y : (R ⊗[F] ρ.fixedSubalgebra)ˣ => Q.matrixAt R y.val) hh
    have htinv : (neutralMatrixUnits Q P R gt⁻¹).val =
        Q.matrixAt R (quaternionScale Q R (scalarParameter R s⁻¹)).val := by
      have he : neutralMatrixUnits Q P R gt = Units.map (Q.matrixAt R).toMonoidHom
          (quaternionScale Q R (scalarParameter R s)) := Units.ext hti
      rw [map_inv, he, ← map_inv, ← map_inv, ← map_inv]
      rfl
    have hm : half upper w q R ((t : R) • a) ((t : R) ^ 2 • b)
        (shearAdmissible_smul Q w q R a b h ↑t) = gt * a₀ * gt⁻¹ := by
      apply neutralMatrixUnits_injective Q P R
      apply Units.ext
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hti, htinv,
        show a₀ = half upper w q R a b h from rfl, hhalf upper w q R a b h,
        hhalf upper w q R _ _ (shearAdmissible_smul Q w q R a b h ↑t),
        halfShearFirst_smul, halfShearSecond_smul]
      exact (scalarScale_conjugates_shear Q upper w q R _ _ t).symm
    change (half upper w q R _ _ (shearAdmissible_smul Q w q R a b h ↑t) ≫ C) =
      g * (show Points G.val.X R from a₀ ≫ C) * g⁻¹
    rw [hm]
    exact descended_square_conjugation _ P.centralIsogeny C hC a₀ g
  refine ⟨⟨lift, hformula, ?_, hnatural⟩, hzero⟩
  intro upper w q R a b h
  let S := polynomialAlgebra R
  let T := laurentAlgebra R
  let f := polynomialConstants R
  let j := polynomialToLaurent R
  let e := polynomialEvaluate R 0
  let k := laurentConstants R
  let t := laurentParameter R
  let a' : S ⊗[F] B := (Polynomial.X : S) • tensorMap B f.hom a
  let b' : S ⊗[F] B := (Polynomial.X : S) ^ 2 • tensorMap B f.hom b
  let h' : ShearAdmissible Q w q S a' b' :=
    shearAdmissible_smul Q w q S _ _ (shearAdmissible_map Q w q R S f a b h) _
  refine ⟨lift upper w q S a' b' h', ?_, ?_⟩
  · have ht : j.hom (Polynomial.X : S) = (t : T) := Polynomial.toLaurent_X
    have hm (x : R ⊗[F] B) : tensorMap B j.hom (tensorMap B f.hom x) = tensorMap B k.hom x := by
      rw [tensorMap_comp, show f ≫ j = k from polynomialConstants_laurent R]
    have ha : tensorMap B j.hom a' = (t : T) • tensorMap B k.hom a := by
      rw [show a' = (Polynomial.X : S) • tensorMap B f.hom a from rfl, tensorMap_smul, ht, hm]
    have hb : tensorMap B j.hom b' = (t : T) ^ 2 • tensorMap B k.hom b := by
      rw [show b' = (Polynomial.X : S) ^ 2 • tensorMap B f.hom b from rfl,
        tensorMap_smul, map_pow, ht, hm]
    let hT := shearAdmissible_map Q w q R T k a b h
    have hJ : ShearAdmissible Q w q T (tensorMap B j.hom a') (tensorMap B j.hom b') := by
      rw [ha, hb]
      exact shearAdmissible_smul Q w q T _ _ hT ↑t
    rw [hnatural upper w q S T j a' b' h' hJ]
    have hh := hscale upper w q T t _ _ hT
    rw [← hnatural upper w q R T k a b h hT] at hh
    revert hJ
    rw [ha, hb]
    exact fun _ => hh
  · have hz : e.hom (Polynomial.X : S) = 0 := Polynomial.eval₂_X _ _
    have ha : tensorMap B e.hom a' = 0 := by
      rw [show a' = (Polynomial.X : S) • tensorMap B f.hom a from rfl, tensorMap_smul, hz, zero_smul]
    have hb : tensorMap B e.hom b' = 0 := by
      rw [show b' = (Polynomial.X : S) ^ 2 • tensorMap B f.hom b from rfl, tensorMap_smul,
        map_pow, hz, zero_pow (by decide), zero_smul]
    have he : ShearAdmissible Q w q R (tensorMap B e.hom a') (tensorMap B e.hom b') :=
      shearAdmissible_map Q w q S R e a' b' h'
    rw [hnatural upper w q S R e a' b' h' he]
    change lift upper w q R _ _ he = (1 : Points G.val.X R)
    revert he
    rw [ha, hb]
    exact hzero upper w q R

end ContractingShears

section QuaternionNorm

open Algebra.TensorProduct
open Specs.SymplecticDivisionForms (extendAnti)
open RM03.CSA.NormOneGroup (normAt_eq_det extendSplitting extendSplitting_tmul)

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
  {R : Type u} [CommRing R] [Algebra F R]

private theorem quaternion_adjugate {S : Type*} [CommRing S] (M : Matrix (Fin 2) (Fin 2) S) :
    M.adjugate = algebraMap S (Matrix (Fin 2) (Fin 2) S) M.trace - M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.algebraMap_matrix_apply, add_sub_cancel_left]

private theorem quaternion_adjugate_add {S : Type*} [CommRing S] (M N : Matrix (Fin 2) (Fin 2) S) :
    (M + N).adjugate = M.adjugate + N.adjugate := by
  simp only [quaternion_adjugate, Matrix.trace_add, map_add, add_sub_add_comm]

private theorem quaternion_adjugate_smul {S : Type*} [CommRing S] (a : S)
    (M : Matrix (Fin 2) (Fin 2) S) : (a • M).adjugate = a • M.adjugate := by
  rw [quaternion_adjugate, Matrix.trace_smul, quaternion_adjugate, smul_sub, smul_eq_mul, map_mul]
  rw [Algebra.smul_def a ((algebraMap S (Matrix (Fin 2) (Fin 2) S)) M.trace)]

private theorem quaternion_normAt_det {L : Type u} [Field L] [Algebra F L]
    [Algebra L R] [IsScalarTower F L R] (hB : isCentralSimple F B) (hd : RM03.CSA.degree F B = 2)
    {J : Type u} [Fintype J] (basis : Module.Basis J F B) (x : R ⊗[F] B)
    (e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) :
    normAt hB basis x = (extendSplitting e x).det := by
  revert e
  rw [← hd]
  exact fun e => normAt_eq_det hB basis e x

private theorem quaternion_conjugation_norm (hB : isCentralSimple F B) (hd : degree F B = 2)
    (σ : Involution F B) (hσ : ∀ x, antiValue σ.anti x = quaternionConjugate hB x)
    {J : Type u} [Fintype J] (basis : Module.Basis J F B) (x : R ⊗[F] B) :
    x * antiValue (extendAnti σ.anti R) x = algebraMap R (R ⊗[F] B) (normAt hB basis x) ∧
      antiValue (extendAnti σ.anti R) x * x = algebraMap R (R ⊗[F] B) (normAt hB basis x) := by
  let L := AlgebraicClosure F
  let T := L ⊗[F] R
  let f : R →ₐ[F] T := includeRight
  have hf : Function.Injective f := includeRight_injective (algebraMap F L).injective
  have hfi : Function.Injective (tensorMap B f) := by
    change Function.Injective (f.toLinearMap.rTensor B)
    exact Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  have hd' : RM03.CSA.degree F B = 2 := hd
  obtain ⟨e₀⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hB
  let e : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L := hd' ▸ e₀
  have htrace (y : B) :
      algebraMap F L (LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction.reducedTrace hB y) =
        (e (1 ⊗ₜ[F] y)).trace := by
    have ht (E : (L ⊗[F] B) ≃ₐ[L] Matrix (Fin 2) (Fin 2) L) :
        algebraMap F L (LinearAlgebraicGroups.Arithmetic.LocalDivisionNormTraceReduction.reducedTrace hB y) =
          (E (1 ⊗ₜ[F] y)).trace := by
      revert E
      rw [← hd']
      exact fun E => LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras.reducedTrace_map hB E y
    exact ht e
  have he (y : B) : e ((1 : L) ⊗ₜ[F] antiValue σ.anti y) = (e (1 ⊗ₜ[F] y)).adjugate := by
    let i : B →ₐ[F] Matrix (Fin 2) (Fin 2) L := (e.restrictScalars F).toAlgHom.comp includeRight
    rw [hσ]
    change i (algebraMap F B _ - y) = (i y).adjugate
    rw [map_sub, i.commutes, IsScalarTower.algebraMap_apply F L (Matrix (Fin 2) (Fin 2) L),
      htrace y, quaternion_adjugate]
    rfl
  let E : (T ⊗[F] B) ≃ₐ[T] Matrix (Fin 2) (Fin 2) T := extendSplitting e
  have hE (y : T ⊗[F] B) : E (antiValue (extendAnti σ.anti T) y) = (E y).adjugate := by
    induction y using TensorProduct.inductionOn with
    | tmul r b =>
      rw [extendAnti_tmul]
      change extendSplitting e (r ⊗ₜ[F] antiValue σ.anti b) = _
      rw [extendSplitting_tmul, he]
      change _ = (extendSplitting e (r ⊗ₜ[F] b)).adjugate
      rw [extendSplitting_tmul, quaternion_adjugate_smul]
      exact congrArg (r • ·) ((algebraMap L T).map_adjugate (e (1 ⊗ₜ[F] b)))
    | add x y hx hy =>
      have h : antiValue (extendAnti σ.anti T) (x + y) =
          antiValue (extendAnti σ.anti T) x + antiValue (extendAnti σ.anti T) y := by simp [antiValue]
      rw [h, map_add, map_add, hx, hy, quaternion_adjugate_add]
  have hn (z : T ⊗[F] B) : normAt hB basis z = (E z).det :=
    quaternion_normAt_det hB hd' basis z e
  have hbar (y : R ⊗[F] B) :
      tensorMap B f (antiValue (extendAnti σ.anti R) y) =
        antiValue (extendAnti σ.anti T) (tensorMap B f y) := by
    induction y using TensorProduct.inductionOn with
    | tmul r b => simp [tensorMap, extendAnti_tmul]
    | add x y hx hy => simp only [antiValue, map_add, MulOpposite.unop_add] at hx hy ⊢
                       rw [hx, hy]
  have hscalar (r : R) : tensorMap B f (algebraMap R (R ⊗[F] B) r) =
      algebraMap T (T ⊗[F] B) (f r) := by simp [tensorMap]
  have hfx : f (normAt hB basis x) = (E (tensorMap B f x)).det :=
    (normAt_natural hB basis f x).symm.trans (hn (tensorMap B f x))
  constructor <;> apply hfi <;> apply E.injective <;>
    rw [map_mul (tensorMap B f), hbar, map_mul E, hE, hscalar, E.commutes,
      hfx]
  · rw [Matrix.mul_adjugate, Algebra.smul_def, mul_one]
  · rw [Matrix.adjugate_mul, Algebra.smul_def, mul_one]

end QuaternionNorm

open Specs.Arithmetic.QuaternionSpinScaleCover (NormalizedScaleFamilies)
open Specs.SymplecticDivisionForms (extendAnti)
open Specs.Arithmetic.NontrialitarianSpinModels (IsPairIsometry)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)
open private evalLaurent evalLaurent_parameter
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

section InterchangeFamilies

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)

private noncomputable abbrev changeSpinPoints {R S : TestAlgebra F} (f : R ⟶ S) :
    Points G.val.X R →* Points G.val.X S := (((groupPointsFunctor F).obj G.val).map f).hom

private theorem shearLift_map_congr (upper : Bool) (w : Fin d → B) (q : Bˣ)
    {R S : TestAlgebra F} (f : R ⟶ S)
    {a b : R ⊗[F] B} {a' b' : S ⊗[F] B}
    (ha : tensorMap B f.hom a = a') (hb : tensorMap B f.hom b = b')
    (h : ShearAdmissible Q w q R a b) (h' : ShearAdmissible Q w q S a' b') :
    mapPoints f (L.lift upper w q R a b h) = L.lift upper w q S a' b' h' := by
  subst a'
  subst b'
  exact L.natural upper w q R S f a b h h'

private theorem interchangeLift_map (w : Fin d → B) (q : Bˣ)
    {R S : TestAlgebra F} (f : R ⟶ S)
    (a : R ⊗[F] B) (b : (R ⊗[F] B)ˣ)
    (h : ShearAdmissible Q w q R a b)
    (h' : ShearAdmissible Q w q S (tensorMap B f.hom a)
      (Units.map (tensorMap B f.hom).toMonoidHom b)) :
    mapPoints f (interchangeLift Q P L w q R a b h) =
      interchangeLift Q P L w q S (tensorMap B f.hom a)
        (Units.map (tensorMap B f.hom).toMonoidHom b) h' := by
  unfold interchangeLift
  dsimp only
  unfold liftedInterchange
  let m := changeSpinPoints (G := G) f
  change m (_ * _ * _) = _
  rw [map_mul m, map_mul m]
  congr 1
  · congr 1
    · apply shearLift_map_congr Q P L false w q f
      · simp only [map_neg, map_mul, ← coefficientConjugation_map]
        rfl
      · exact (coefficientConjugation_map Q R S f _).symm
    · exact L.natural true w q R S f a b _ _
  · apply shearLift_map_congr Q P L false w q f
    · rw [map_mul]
      rfl
    · exact (coefficientConjugation_map Q R S f _).symm

private theorem scalarInterchangeRatio_map (w : Fin d → B) (q : Bˣ)
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B))
    {R S : TestAlgebra F} (f : R ⟶ S) (t : Rˣ) :
    (scalarInterchangeRatio Q P L w q S h (Units.map f.hom.toMonoidHom t)).val.1 =
      mapPoints f (scalarInterchangeRatio Q P L w q R h t).val.1 := by
  let m := changeSpinPoints (G := G) f
  change _ * _⁻¹ = m (_ * _⁻¹)
  rw [map_mul m, map_inv m]
  have hh (r : Rˣ) :
      m (interchangeLift Q P L w q R 0 (scalarParameter R r) (scalarShearAdmissible Q w q R h r)) =
        interchangeLift Q P L w q S 0 (scalarParameter S (Units.map f.hom.toMonoidHom r))
          (scalarShearAdmissible Q w q S h (Units.map f.hom.toMonoidHom r)) := by
    have hz : tensorMap B f.hom (0 : R ⊗[F] B) = 0 := map_zero _
    have hu := scalarParameter_map (B := B) R S f r
    have h' : ShearAdmissible Q w q S (tensorMap B f.hom (0 : R ⊗[F] B))
        (Units.map (tensorMap B f.hom).toMonoidHom (scalarParameter R r)) := by
      rw [hz, hu]
      exact scalarShearAdmissible Q w q S h _
    rw [show m _ = _ from interchangeLift_map Q P L w q f 0 _ _ h']
    revert h'
    rw [hz, hu]
    intro _
    rfl
  rw [hh t, hh 1, map_one (Units.map f.hom.toMonoidHom)]

private noncomputable def conjugateUnit (R : TestAlgebra F) (a : (R ⊗[F] B)ˣ) : (R ⊗[F] B)ˣ :=
  (Units.opEquiv (Units.map (coefficientConjugation Q R).toMonoidHom a)).unop

private theorem conjugateUnit_val (R : TestAlgebra F) (a : (R ⊗[F] B)ˣ) :
    (conjugateUnit Q R a).val = antiValue (coefficientConjugation Q R) a.val := rfl

private theorem conjugateUnit_map {R S : TestAlgebra F} (f : R ⟶ S) (a : (R ⊗[F] B)ˣ) :
    Units.map (tensorMap B f.hom).toMonoidHom (conjugateUnit Q R a) =
      conjugateUnit Q S (Units.map (tensorMap B f.hom).toMonoidHom a) := by
  apply Units.ext
  exact (coefficientConjugation_map Q R S f a.val).symm

private theorem conjugateParameter_admissible (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : (R ⊗[F] B)ˣ) (h : ShearAdmissible Q w q R 1 b.val) :
    ShearAdmissible Q w q R a.val (a * b * conjugateUnit Q R a).val := by
  refine ⟨h.1, ?_⟩
  let σ := coefficientConjugation Q R
  let p := (1 : R) ⊗ₜ[F] (↑q⁻¹ : B)
  have hσ := extendAnti_square (R := R) Q.conjugation.anti Q.conjugation.square
  have hs : b.val - antiValue σ b.val = -p := by
    have hh := h.2
    change b.val - antiValue σ b.val = -(1 * p * antiValue σ 1) at hh
    simpa only [bar_one, one_mul, mul_one] using hh
  change a.val * b.val * antiValue σ a.val - antiValue σ (a.val * b.val * antiValue σ a.val) =
    -(a.val * p * antiValue σ a.val)
  rw [bar_mul, bar_mul, hσ a.val, ← mul_assoc, ← sub_mul, ← mul_sub, hs, mul_neg, neg_mul]

private theorem conjugateParameter_complement (w : Fin d → B) (q : Bˣ)
    (R : TestAlgebra F) (a b : (R ⊗[F] B)ˣ) :
    (interchangeMatrix Q w q R a.val (a * b * conjugateUnit Q R a)).toBlocks₂₂ =
      (interchangeMatrix Q w q R 1 b).toBlocks₂₂ := by
  have hδ : (antiValue (coefficientConjugation Q R) a.val) *
      (((a * b * conjugateUnit Q R a)⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) * a.val =
      ((b⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) := by
    change (conjugateUnit Q R a).val * ((a * b * conjugateUnit Q R a)⁻¹ :
      (R ⊗[F] B)ˣ).val * a.val = b.inv
    exact congrArg Units.val (by group : conjugateUnit Q R a *
      (a * b * conjugateUnit Q R a)⁻¹ * a = b⁻¹)
  ext i j
  simp only [interchangeMatrix, Matrix.toBlocks_fromBlocks₂₂, Matrix.add_apply, Matrix.of_apply,
    antiValue, map_one, MulOpposite.unop_one, mul_one]
  have hδ' : (1 ⊗ₜ[F] (↑q⁻¹ : B)) * antiValue (coefficientConjugation Q R) a.val *
      (((a * b * conjugateUnit Q R a)⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) * a.val =
    (1 ⊗ₜ[F] (↑q⁻¹ : B)) * b.inv := by
    calc
      _ = (1 ⊗ₜ[F] (↑q⁻¹ : B)) *
          (antiValue (coefficientConjugation Q R) a.val *
            (((a * b * conjugateUnit Q R a)⁻¹ : (R ⊗[F] B)ˣ) : R ⊗[F] B) * a.val) := by
              simp only [mul_assoc]
      _ = _ := by rw [hδ]; rfl
  rw [show MulOpposite.unop ((coefficientConjugation Q R) a.val) =
    antiValue (coefficientConjugation Q R) a.val from rfl, hδ']
  rfl

private theorem conjugateUnit_norm
    (hd : degree F B = 2) {J : Type u} [Fintype J] (basis : Module.Basis J F B)
    (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
    (hN : ∀ (R : TestAlgebra F) a, (N R a : R) = normAt hB basis a.val) (R : TestAlgebra F)
    (a : (R ⊗[F] B)ˣ) :
    a * conjugateUnit Q R a = scalarParameter R (N R a) := by
  apply Units.ext
  change a.val * antiValue (coefficientConjugation Q R) a.val =
    algebraMap R (R ⊗[F] B) (N R a : R)
  rw [hN]
  exact (quaternion_conjugation_norm hB hd Q.conjugation Q.canonical basis a.val).1

private theorem conjugateParameter_ratio
    (hd : degree F B = 2) {J : Type u} [Fintype J] (basis : Module.Basis J F B)
    (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
    (hN : ∀ (R : TestAlgebra F) a, (N R a : R) = normAt hB basis a.val)
    (R : TestAlgebra F) (a b : (R ⊗[F] B)ˣ) :
    a * b * conjugateUnit Q R a * b⁻¹ * (scalarParameter R (N R a))⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have he := conjugateUnit_norm Q hd basis N hN R a
  have hcentral (t : Rˣ) : Commute (scalarParameter (B := B) R t) b := by
    show _ * _ = _ * _
    apply Units.ext
    exact Algebra.commutes t.val b.val
  have hbar : conjugateUnit Q R a = a⁻¹ * scalarParameter R (N R a) := by rw [← he, inv_mul_cancel_left]
  rw [hbar]
  calc
    _ = (a * b * a⁻¹) * (scalarParameter R (N R a) * b⁻¹) *
        (scalarParameter R (N R a))⁻¹ := by group
    _ = _ := by rw [(hcentral (N R a)).inv_right.eq]; group

end InterchangeFamilies

section ScaleNormalization

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)

variable (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
  (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
  (he : ∀ R x, (e R x).val.1 = x.val.2)
  (hen : ∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : spinScalePreimage P Q R)
    (y : spinScalePreimage P Q S), y.val.1 = mapPoints f x.val.1 →
    y.val.2 = Units.map (tensorMap B f.hom).toMonoidHom x.val.2 →
    (e S y).val.2 = Units.map f.hom.toMonoidHom (e R x).val.2)

include he hen

private theorem normalized_scalar_ratio
    (normal : NormalizedScaleFamilies.{u}) (hd : degree F B = 2)
    {J : Type u} [Fintype J] (basis : Module.Basis J F B)
    (hN : ∀ (R : TestAlgebra F) t, (N R t : R) = normAt hB basis t.val)
    (w : Fin d → B) (q : Bˣ)
    (h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B)) :
    ∀ (R : TestAlgebra F) (t : Rˣ), (e R (scalarInterchangeRatio Q P L w q R h t)).val =
      (scalarParameter R t, t) := by
  let R₀ := CommAlgCat.of F F
  let A := laurentAlgebra R₀
  let t₀ := laurentParameter R₀
  let p : A ⟶ R₀ := evalLaurent (𝟙 R₀) 1
  let x := scalarInterchangeRatio Q P L w q A h t₀
  let s := (e A x).val.2
  have hm (R : TestAlgebra F) (f : A ⟶ R) (t : Rˣ)
      (ht : Units.map f.hom.toMonoidHom t₀ = t) :
      (e R (scalarInterchangeRatio Q P L w q R h t)).val.2 = Units.map f.hom.toMonoidHom s := by
    let y := scalarInterchangeRatio Q P L w q R h t
    apply hen A R f x y
    · have hh := scalarInterchangeRatio_map Q P L w q h f t₀
      rw [ht] at hh
      exact hh
    · change scalarParameter R t = Units.map (tensorMap B f.hom).toMonoidHom (scalarParameter A t₀)
      rw [scalarParameter_map, ht]
  have h1 : scalarInterchangeRatio Q P L w q R₀ h 1 = 1 := by
    apply Subtype.ext
    apply Prod.ext
    · change _ * _⁻¹ = 1
      exact mul_inv_cancel _
    · exact map_one (Units.map (algebraMap R₀ (R₀ ⊗[F] B)).toMonoidHom)
  have hst : p.hom s.val = 1 := by
    have hsp := (hm R₀ p 1 (evalLaurent_parameter (𝟙 R₀) 1)).symm
    rw [h1, map_one (e R₀)] at hsp
    exact congrArg Units.val hsp
  have hnt : normAt hB basis (algebraMap A (A ⊗[F] B) t₀.val) = s.val ^ 2 := by
    have ht : N A (e A x).val.1 = s ^ 2 := (e A x).property
    rw [he A x] at ht
    change N A (scalarParameter A t₀) = s ^ 2 at ht
    have hh := congrArg Units.val ht
    rw [hN A (scalarParameter A t₀), Units.val_pow_eq_pow_val] at hh
    exact hh
  have hD : IsDomain (LaurentPolynomial F) := inferInstance
  have hs : s = t₀ := (normal hB hd basis p.hom).1 t₀ s
    (congrArg Units.val (evalLaurent_parameter (𝟙 R₀) 1)) hst hnt
  intro R t
  apply Prod.ext
  · exact he R _
  · let f := evalLaurent (CommAlgCat.ofHom (Algebra.ofId F R)) t
    have hft := evalLaurent_parameter (CommAlgCat.ofHom (Algebra.ofId F R)) t
    exact (hm R f t hft).trans ((congrArg (Units.map f.hom.toMonoidHom) hs).trans hft)

end ScaleNormalization

section PolynomialPaths

open scoped Polynomial PowerSeries

variable {F : Type u} [Field F] (R : TestAlgebra F)

private noncomputable abbrev polynomialPath (f : Polynomial R) := CommAlgCat.of F (Localization.Away f)

private noncomputable def polynomialPathMap (f : Polynomial R) : polynomialAlgebra R ⟶ polynomialPath R f :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom F (Polynomial R) (Localization.Away f))

private noncomputable def polynomialPathEval (f : Polynomial R) (x : R)
    (h : IsUnit ((polynomialEvaluate R x).hom f)) : polynomialPath R f ⟶ R :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom f h)

private theorem polynomialPathMap_eval (f : Polynomial R) (x : R)
    (h : IsUnit ((polynomialEvaluate R x).hom f)) :
    polynomialPathMap R f ≫ polynomialPathEval R f x h = polynomialEvaluate R x := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  exact IsLocalization.Away.lift_eq _ h z

/-- A square-one unit on this localized polynomial path is one if it
specializes to one at zero. Formal power series also handle nonreduced
coefficient algebras. -/
private theorem polynomialPath_square_one (h2 : (2 : F) ≠ 0)
    (f : Polynomial R) (hf : (polynomialEvaluate R 0).hom f = 1)
    (h : IsUnit ((polynomialEvaluate R 0).hom f)) (s : (polynomialPath R f)ˣ)
    (hs : s ^ 2 = 1) (hs₀ : (polynomialPathEval R f 0 h).hom s.val = 1) : s = 1 := by
  let C := Localization.Away f
  let l₀ : Polynomial R →+* PowerSeries R := Polynomial.coeToPowerSeries.ringHom
  have hf' : IsUnit (l₀ f) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    change IsUnit (f.coeff 0)
    have e : (polynomialEvaluate R 0).hom f = f.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero f).symm
    rw [← e, hf]
    exact isUnit_one
  let l : C →+* PowerSeries R := IsLocalization.Away.lift f hf'
  have hlBase (z : Polynomial R) : l (algebraMap (Polynomial R) C z) = l₀ z :=
    IsLocalization.Away.lift_eq _ hf' z
  have hl : Function.Injective l := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers f) l).mpr
    intro x y
    constructor
    · intro h
      exact congrArg l h
    · rw [hlBase x, hlBase y]
      intro h
      exact congrArg (algebraMap (Polynomial R) C) (Polynomial.coe_injective R h)
  have hcomp : (PowerSeries.constantCoeff (R := R)).comp l =
      (polynomialPathEval R f 0 h).hom.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro z
    change PowerSeries.constantCoeff (l (algebraMap (Polynomial R) C z)) =
      IsLocalization.Away.lift f h (algebraMap (Polynomial R) C z)
    rw [hlBase z, IsLocalization.Away.lift_eq _ h]
    exact Polynomial.coeff_zero_eq_eval_zero z
  let v : PowerSeries R := l s.val
  have hv₀ : PowerSeries.constantCoeff v = 1 :=
    (congrArg (fun p : C →+* R => p s.val) hcomp).trans hs₀
  have hv₂ : v ^ 2 = 1 := by
    change l s.val ^ 2 = 1
    rw [← map_pow]
    have hh := congrArg Units.val hs
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hh
    rw [hh, map_one]
  have hunit : IsUnit (v + 1) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [map_add, hv₀, map_one, ← map_one (algebraMap F R), ← map_add, one_add_one_eq_two]
    exact (isUnit_iff_ne_zero.mpr h2).map (algebraMap F R)
  have hprod : (v - 1) * (v + 1) = 0 := by
    calc
      _ = v ^ 2 - 1 := by ring
      _ = 0 := by rw [hv₂, sub_self]
  obtain ⟨w, hw⟩ := hunit
  have he : v - 1 = 0 := by
    have H := congrArg (· * w.inv) hprod
    rw [← hw, mul_assoc, w.val_inv, mul_one, zero_mul] at H
    exact H
  apply Units.ext
  apply hl
  rw [Units.val_one, map_one]
  exact sub_eq_zero.mp he

end PolynomialPaths

section UnitPaths

variable {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]

private theorem quaternion_unit_path (hB : isCentralSimple F B) (hd : degree F B = 2)
    (σ : Involution F B) (hσ : ∀ x, antiValue σ.anti x = quaternionConjugate hB x)
    {J : Type u} [Fintype J] (basis : Module.Basis J F B)
    (R : TestAlgebra F) (a : (R ⊗[F] B)ˣ) :
    ∃ (f : Polynomial R) (hf : (polynomialEvaluate R 0).hom f = 1)
      (h₁ : IsUnit ((polynomialEvaluate R 1).hom f))
      (A : (polynomialPath R f ⊗[F] B)ˣ),
      Units.map (tensorMap B (polynomialPathEval R f 0 (hf.symm ▸ isUnit_one)).hom).toMonoidHom A = 1 ∧
      Units.map (tensorMap B (polynomialPathEval R f 1 h₁).hom).toMonoidHom A = a := by
  let S := polynomialAlgebra R
  let m := polynomialConstants R
  let x : S ⊗[F] B := 1 + (Polynomial.X : S) • tensorMap B m.hom (a.val - 1)
  let f : Polynomial R := normAt hB basis x
  have hid (v : R ⊗[F] B) : tensorMap B (𝟙 R : R ⟶ R).hom v = v := by
    induction v using TensorProduct.inductionOn with
    | tmul r b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hh (t : R) : tensorMap B (polynomialEvaluate R t).hom x = 1 + t • (a.val - 1) := by
    have hX : (polynomialEvaluate R t).hom (Polynomial.X : S) = t := Polynomial.eval₂_X _ _
    have hcomp : m ≫ polynomialEvaluate R t = 𝟙 R := by
      apply CommAlgCat.hom_ext
      exact AlgHom.ext fun r => Polynomial.eval₂_C _ _
    change tensorMap B (polynomialEvaluate R t).hom
      (1 + (Polynomial.X : S) • tensorMap B m.hom (a.val - 1)) = _
    rw [map_add, map_one, tensorMap_smul, hX, tensorMap_comp, hcomp, hid]
  have hx₀ : tensorMap B (polynomialEvaluate R 0).hom x = 1 := by rw [hh, zero_smul, add_zero]
  have hx₁ : tensorMap B (polynomialEvaluate R 1).hom x = a.val := by rw [hh, one_smul, add_comm, sub_add_cancel]
  have hf : (polynomialEvaluate R 0).hom f = 1 := by
    calc
      _ = (normHom hB basis : (R ⊗[F] B) →* R) (tensorMap B (polynomialEvaluate R 0).hom x) :=
        (normAt_natural hB basis (polynomialEvaluate R 0).hom x).symm
      _ = 1 := by rw [hx₀, map_one]
  have h₁ : IsUnit ((polynomialEvaluate R 1).hom f) := by
    have he : (polynomialEvaluate R 1).hom f = (normHom hB basis : (R ⊗[F] B) →* R) a.val := by
      rw [← hx₁]
      exact (normAt_natural hB basis (polynomialEvaluate R 1).hom x).symm
    exact he.symm ▸ (a.isUnit.map (normHom hB basis : (R ⊗[F] B) →* R))
  let C := polynomialPath R f
  let i := polynomialPathMap R f
  let y := tensorMap B i.hom x
  have hy : normAt hB basis y = i.hom f := normAt_natural hB basis i.hom x
  let n : Cˣ := (IsLocalization.Away.algebraMap_isUnit (S := C) f).unit
  have hn : normAt hB basis y = n.val := hy.trans (IsUnit.unit_spec _).symm
  let s := Units.map (algebraMap C (C ⊗[F] B)).toMonoidHom n
  have he : y * antiValue (extendAnti σ.anti C) y = s.val ∧
      antiValue (extendAnti σ.anti C) y * y = s.val := by
    have h := quaternion_conjugation_norm hB hd σ hσ basis y
    rw [hn] at h
    exact h
  let z := antiValue (extendAnti σ.anti C) y
  let A : (C ⊗[F] B)ˣ :=
    ⟨y, z * s.inv, by
      rw [← mul_assoc, show y * z = s.val from he.1, s.val_inv], by
      have hc : Commute s.inv y := Algebra.commutes (R := C) n.inv y
      rw [mul_assoc, hc.eq, ← mul_assoc, show z * y = s.val from he.2, s.val_inv]⟩
  use f, hf, h₁, A
  constructor <;> apply Units.ext
  · change tensorMap B (polynomialPathEval R f 0 _).hom y = 1
    rw [show y = tensorMap B i.hom x from rfl, tensorMap_comp, polynomialPathMap_eval, hx₀]
  · change tensorMap B (polynomialPathEval R f 1 _).hom y = a.val
    rw [show y = tensorMap B i.hom x from rfl, tensorMap_comp, polynomialPathMap_eval, hx₁]

end UnitPaths

section MixedScaleNormalization

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)
  (hd : degree F B = 2) {J : Type u} [Fintype J] (basis : Module.Basis J F B)
  (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
  (hN : ∀ (R : TestAlgebra F) a, (N R a : R) = normAt hB basis a.val)

include hN

private theorem normUnits_map {R S : TestAlgebra F} (f : R ⟶ S) (a : (R ⊗[F] B)ˣ) :
    N S (Units.map (tensorMap B f.hom).toMonoidHom a) = Units.map f.hom.toMonoidHom (N R a) := by
  apply Units.ext
  change (N S (Units.map (tensorMap B f.hom).toMonoidHom a) : S) = f.hom (N R a : R)
  rw [hN, hN]
  exact normAt_natural hB basis f.hom a.val

include hd

private noncomputable def mixedInterchangeRatio (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
    (a b : (R ⊗[F] B)ˣ) (h : ShearAdmissible Q w q R 1 b.val) : spinScalePreimage P Q R :=
  let b' := a * b * conjugateUnit Q R a
  ⟨(interchangeLift Q P L w q R a.val b' (conjugateParameter_admissible Q w q R a b h) *
      (interchangeLift Q P L w q R 1 b h)⁻¹ *
      (scalarInterchangeRatio Q P L w q R h.1 (N R a)⁻¹).val.1,
      a * b * a⁻¹ * b⁻¹), by
    let x := scalarInterchangeRatio Q P L w q R h.1 (N R a)⁻¹
    change spinVectorProjection P R (_ * x.val.1) = quaternionScale Q R (a * b * a⁻¹ * b⁻¹)
    have hx : spinVectorProjection P R x.val.1 = quaternionScale Q R (scalarParameter R (N R a)⁻¹) :=
      x.property
    rw [map_mul, hx,
      scale_of_interchange_ratio Q P L w q R a.val 1 b' b _ h
        (conjugateParameter_complement Q w q R a b), ← map_mul]
    change quaternionScale Q R (a * b * conjugateUnit Q R a * b⁻¹ *
      (scalarParameter R (N R a))⁻¹) = _
    exact congrArg (quaternionScale Q R) (conjugateParameter_ratio Q hd basis N hN R a b)⟩

private theorem mixedInterchangeRatio_one (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
    (b : (R ⊗[F] B)ˣ) (h : ShearAdmissible Q w q R 1 b.val) :
    mixedInterchangeRatio Q P L hd basis N hN w q R 1 b h = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · have hbar : conjugateUnit Q R 1 = 1 := by
      apply Units.ext
      simp [conjugateUnit]
    have hb : 1 * b * conjugateUnit Q R 1 = b := by rw [hbar, one_mul, mul_one]
    have hw : ∀ (z : (R ⊗[F] B)ˣ), z = b → ∀ hz : ShearAdmissible Q w q R 1 z.val,
        interchangeLift Q P L w q R 1 z hz = interchangeLift Q P L w q R 1 b h := by
      intro z e hz
      subst z
      rfl
    have hs : ∀ t : Rˣ, t = 1 → (scalarInterchangeRatio Q P L w q R h.1 t).val.1 = 1 := by
      intro t ht
      subst t
      change _ * _⁻¹ = 1
      exact mul_inv_cancel _
    change interchangeLift Q P L w q R 1 (1 * b * conjugateUnit Q R 1) _ *
        (interchangeLift Q P L w q R 1 b h)⁻¹ *
        (scalarInterchangeRatio Q P L w q R h.1 (N R 1)⁻¹).val.1 = 1
    rw [hw _ hb, mul_inv_cancel, hs _ (by rw [map_one, inv_one]), one_mul]
  · change 1 * b * (1 : (R ⊗[F] B)ˣ)⁻¹ * b⁻¹ = 1
    simp

private theorem mixedInterchangeRatio_map (w : Fin d → B) (q : Bˣ) {R S : TestAlgebra F}
    (f : R ⟶ S) (a b : (R ⊗[F] B)ˣ)
    (h : ShearAdmissible Q w q R 1 b.val) (a' b' : (S ⊗[F] B)ˣ)
    (ha : Units.map (tensorMap B f.hom).toMonoidHom a = a')
    (hb : Units.map (tensorMap B f.hom).toMonoidHom b = b')
    (h' : ShearAdmissible Q w q S 1 b'.val) :
    (mixedInterchangeRatio Q P L hd basis N hN w q S a' b' h').val.1 =
        mapPoints f (mixedInterchangeRatio Q P L hd basis N hN w q R a b h).val.1 ∧
    (mixedInterchangeRatio Q P L hd basis N hN w q S a' b' h').val.2 =
      Units.map (tensorMap B f.hom).toMonoidHom
        (mixedInterchangeRatio Q P L hd basis N hN w q R a b h).val.2 := by
  let m := Units.map (tensorMap B f.hom).toMonoidHom
  let n := changeSpinPoints (G := G) f
  let z := a * b * conjugateUnit Q R a
  let z' := a' * b' * conjugateUnit Q S a'
  let hz := conjugateParameter_admissible Q w q R a b h
  let hz' := conjugateParameter_admissible Q w q S a' b' h'
  have hmap : m z = z' := by
    change m (a * b * conjugateUnit Q R a) = a' * b' * conjugateUnit Q S a'
    rw [map_mul, map_mul, show m (conjugateUnit Q R a) = conjugateUnit Q S (m a)
      from conjugateUnit_map Q f a, ha, hb]
  have hw (x : R ⊗[F] B) (u : (R ⊗[F] B)ˣ) (h₀ : ShearAdmissible Q w q R x u.val)
      (y : S ⊗[F] B) (v : (S ⊗[F] B)ˣ) (h₁ : ShearAdmissible Q w q S y v.val)
      (hxy : tensorMap B f.hom x = y) (huv : m u = v) :
      n (interchangeLift Q P L w q R x u h₀) = interchangeLift Q P L w q S y v h₁ := by
    subst y
    subst v
    exact interchangeLift_map Q P L w q f x u h₀ h₁
  constructor
  · change interchangeLift Q P L w q S a'.val z' hz' * (interchangeLift Q P L w q S 1 b' h')⁻¹ *
        (scalarInterchangeRatio Q P L w q S h'.1 (N S a')⁻¹).val.1 =
        n (interchangeLift Q P L w q R a.val z hz * (interchangeLift Q P L w q R 1 b h)⁻¹ *
        (scalarInterchangeRatio Q P L w q R h.1 (N R a)⁻¹).val.1)
    rw [map_mul n, map_mul n, map_inv n, hw _ _ hz _ _ hz' (congrArg Units.val ha) hmap,
      hw _ _ h _ _ h' (map_one _) hb]
    have hs := scalarInterchangeRatio_map Q P L w q h.1 f (N R a)⁻¹
    change _ = n _ at hs
    rw [map_inv, ← normUnits_map basis N hN f a, ha] at hs
    rw [← hs]
  · change a' * b' * a'⁻¹ * b'⁻¹ = m (a * b * a⁻¹ * b⁻¹)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb]

variable (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
  (he : ∀ R x, (e R x).val.1 = x.val.2)
  (hen : ∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : spinScalePreimage P Q R)
    (y : spinScalePreimage P Q S), y.val.1 = mapPoints f x.val.1 →
    y.val.2 = Units.map (tensorMap B f.hom).toMonoidHom x.val.2 →
    (e S y).val.2 = Units.map f.hom.toMonoidHom (e R x).val.2)

include he hen

private theorem normalized_mixed_ratio (h2 : (2 : F) ≠ 0)
    (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F)
    (a b : (R ⊗[F] B)ˣ) (h : ShearAdmissible Q w q R 1 b.val) :
    (e R (mixedInterchangeRatio Q P L hd basis N hN w q R a b h)).val =
      (a * b * a⁻¹ * b⁻¹, 1) := by
  obtain ⟨f, hf, h₁, A, hA₀, hA₁⟩ := quaternion_unit_path hB hd Q.conjugation Q.canonical basis R a
  let C := polynomialPath R f
  let p₀ := polynomialPathEval R f 0 (hf.symm ▸ isUnit_one)
  let p₁ := polynomialPathEval R f 1 h₁
  let m := polynomialConstants R ≫ polynomialPathMap R f
  let bC := Units.map (tensorMap B m.hom).toMonoidHom b
  have hC : ShearAdmissible Q w q C 1 bC.val := by
    have he := shearAdmissible_map Q w q R C m 1 b.val h
    rwa [map_one] at he
  let x := mixedInterchangeRatio Q P L hd basis N hN w q C A bC hC
  let s := (e C x).val.2
  have hs : s ^ 2 = 1 := by
    have H : N C (e C x).val.1 = s ^ 2 := (e C x).property
    rw [he, show x.val.2 = A * bC * A⁻¹ * bC⁻¹ from rfl, map_mul, map_mul, map_mul, map_inv, map_inv] at H
    exact H.symm.trans (calc
      _ = N C A * (N C A)⁻¹ * (N C bC * (N C bC)⁻¹) := by ac_rfl
      _ = 1 := by simp)
  have hb (t : R) (ht : IsUnit ((polynomialEvaluate R t).hom f)) :
      Units.map (tensorMap B (polynomialPathEval R f t ht).hom).toMonoidHom bC = b := by
    apply Units.ext
    change tensorMap B (polynomialPathEval R f t ht).hom (tensorMap B m.hom b.val) = b.val
    rw [tensorMap_comp, show m ≫ polynomialPathEval R f t ht =
      polynomialConstants R ≫ polynomialEvaluate R t by
        rw [show m = polynomialConstants R ≫ polynomialPathMap R f from rfl,
          Category.assoc, polynomialPathMap_eval]]
    have hid : polynomialConstants R ≫ polynomialEvaluate R t = 𝟙 R :=
      CommAlgCat.hom_ext (AlgHom.ext fun _ => Polynomial.eval₂_C _ _)
    rw [hid]
    suffices ∀ x : R ⊗[F] B, tensorMap B (𝟙 R : R ⟶ R).hom x = x from this b.val
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r y => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hs₀ : p₀.hom s.val = 1 := by
    let y := mixedInterchangeRatio Q P L hd basis N hN w q R 1 b h
    obtain ⟨hh, ht⟩ := mixedInterchangeRatio_map Q P L hd basis N hN w q p₀ A bC hC 1 b
      hA₀ (hb 0 _) h
    have hval := hen C R p₀ x y hh ht
    change (e R y).val.2 = Units.map p₀.hom.toMonoidHom s at hval
    rw [show y = 1 from mixedInterchangeRatio_one Q P L hd basis N hN w q R b h, map_one] at hval
    exact congrArg Units.val hval.symm
  have hs1 : s = 1 := polynomialPath_square_one R h2 f hf _ s hs hs₀
  apply Prod.ext
  · exact he R _
  · let y := mixedInterchangeRatio Q P L hd basis N hN w q R a b h
    obtain ⟨hh, ht⟩ := mixedInterchangeRatio_map Q P L hd basis N hN w q p₁ A bC hC a b hA₁ (hb 1 _) h
    have hval := hen C R p₁ x y hh ht
    change (e R y).val.2 = Units.map p₁.hom.toMonoidHom s at hval
    rwa [hs1, map_one] at hval

private theorem normalized_lifted_scale_words (h2 : (2 : F) ≠ 0) (normal : NormalizedScaleFamilies.{u}) :
    NormalizedLiftedScaleWords Q P L N e := by
  classical
  let scalarWord (w : Fin d → B) (q : Bˣ) (R : TestAlgebra F) (t : Rˣ) :
      spinScalePreimage P Q R :=
    if h : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B) then
      scalarInterchangeRatio Q P L w q R h t else 1
  refine ⟨scalarWord, ?_, ?_⟩
  · intro w q R t h
    dsimp only [scalarWord]
    rw [dite_eq_left h]
    refine ⟨normalized_scalar_ratio Q P L N e he hen normal hd basis hN w q h R t, ?_⟩
    let hs := scalarShearAdmissible Q w q R h t
    let h1 := scalarShearAdmissible Q w q R h 1
    let E := liftedInterchange_formula Q P L w q R 0 (scalarParameter R t) hs
    have hU : scalarParameter (B := B) R 1 = 1 := map_one _
    have hword (z : (R ⊗[F] B)ˣ) (hz : ShearAdmissible Q w q R 0 z.val) (hh : z = 1) :
        ∃ h₀ h₀₁ h₀₂, interchangeLift Q P L w q R 0 z hz = liftedInterchange Q P L w q R 0 1 h₀ h₀₁ h₀₂ := by
      subst z
      unfold interchangeLift
      dsimp only
      exact ⟨hz, _, _, rfl⟩
    obtain ⟨h₀, h₀₁, h₀₂, hh⟩ := hword (scalarParameter R 1) h1 hU
    refine ⟨hs, E.choose, E.choose_spec.choose, h₀, h₀₁, h₀₂, ?_⟩
    change _ * (interchangeLift Q P L w q R 0 (scalarParameter R 1) h1)⁻¹ = _
    rw [hh]
    rfl
  · intro w q R a b h
    dsimp only
    let z := mixedInterchangeRatio Q P L hd basis N hN w q R a b h
    refine ⟨z, normalized_mixed_ratio Q P L hd basis N hN e he hen h2 w q R a b h, ?_⟩
    let b' := a * b * conjugateUnit Q R a
    let hb' := conjugateParameter_admissible Q w q R a b h
    let E := liftedInterchange_formula Q P L w q R 1 b h
    let E' := liftedInterchange_formula Q P L w q R a.val b' hb'
    refine ⟨h, E.choose, E.choose_spec.choose, hb', E'.choose, E'.choose_spec.choose, ?_⟩
    simp only [scalarWord, dite_eq_left h.1]
    rfl

end MixedScaleNormalization

section ScalarWeights

variable (F : Type u) [Field F]

private theorem exists_distinct_scalar_weights [Infinite F] :
    ∃ t : Fˣ, (t : F) ≠ 1 ∧ (t⁻¹ : Fˣ).val ≠ 1 ∧ (t : F) ≠ (t⁻¹ : Fˣ).val := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  have hx₀ : x ≠ 0 := fun h => hx (by simp [h])
  have hx₁ : x ≠ 1 := fun h => hx (by simp [h])
  have hx₂ : x ≠ -1 := fun h => hx (by simp [h])
  let t := Units.mk0 x hx₀
  refine ⟨t, hx₁, ?_, ?_⟩
  · intro h
    have ht := t.mul_inv
    rw [h, mul_one] at ht
    exact hx₁ ht
  · intro h
    have ht : x ^ 2 = 1 := by
      change (t : F) ^ 2 = 1
      rw [pow_two, ← t.inv_mul]
      exact congrArg (· * (t : F)) h
    rcases sq_eq_one_iff.mp ht with h | h
    · exact hx₁ h
    · exact hx₂ h

end ScalarWeights

section QuaternionLevi

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private abbrev groundAlgebra (F : Type u) [Field F] := CommAlgCat.of F F

private noncomputable def groundVectorUnits :
    Points G.val.X (groundAlgebra F) →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ :=
  (Units.map (Algebra.TensorProduct.lid F B).toRingHom.mapMatrix.toMonoidHom).comp
    ((Units.map (Q.matrixAt (groundAlgebra F)).toMonoidHom).comp (spinVectorProjection P (groundAlgebra F)))

private theorem groundVectorUnits_matrix (g : Points G.val.X (groundAlgebra F)) :
    (groundVectorUnits Q P g).val =
      (vectorMatrix Q P (groundAlgebra F) g).map (Algebra.TensorProduct.lid F B) := rfl

private theorem groundVectorUnits_isometry (g : Points G.val.X (groundAlgebra F)) :
    let H := quaternionHyperbolicGram Q.complement.val
    let M := (groundVectorUnits Q P g).val
    dagger Q.conjugation.anti M * H * M = H := by
  let R := groundAlgebra F
  let E := Algebra.TensorProduct.lid F B
  let x := spinVectorProjection P R g
  have hg : IsPairIsometry D R x :=
    (P.fullRange R x).mp ⟨g ≫ (P.projection ≫ P.inclusion).hom.hom, rfl⟩
  have hv := (isometry_iff_gram Q R x).mp hg.1
  have hmap (y : R ⊗[F] B) : E (antiValue (coefficientConjugation Q R) y) = antiValue Q.conjugation.anti (E y) := by
    obtain ⟨b, rfl⟩ := E.symm.surjective y
    have he : E.symm b = (1 : R) ⊗ₜ[F] b := by
      apply E.injective
      have hh : E ((1 : R) ⊗ₜ[F] b) = b := by simp [E]
      exact (E.apply_symm_apply b).trans hh.symm
    rw [he, extendAnti_tmul]
    simp [E]
  have hDag (M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B)) :
      (dagger (coefficientConjugation Q R) M).map E = dagger Q.conjugation.anti (M.map E) := by
    ext i j
    exact hmap (M j i)
  have hH : (gramAt Q R).val.map E = quaternionHyperbolicGram Q.complement.val := by
    rw [gramAt_blocks]
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · fin_cases i <;> fin_cases j <;> simp [quaternionHyperbolicGram]
    · simp [quaternionHyperbolicGram]
    · simp [quaternionHyperbolicGram]
    · simp [quaternionHyperbolicGram, complementGram, E]
  have hh := congrArg E.toRingHom.mapMatrix hv
  simp only [map_mul, RingHom.mapMatrix_apply] at hh
  change (dagger (coefficientConjugation Q R) (Q.matrixAt R x.val)).map E *
    (gramAt Q R).val.map E * (Q.matrixAt R x.val).map E = (gramAt Q R).val.map E at hh
  rw [hDag, hH] at hh
  exact hh

private theorem off_diagonal_weight_zero (wt : QuaternionPairIndex d → F)
    (X : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)
    (hX : Commute (Matrix.diagonal (fun i => algebraMap F B (wt i))) X)
    (i j : QuaternionPairIndex d) (h : wt i ≠ wt j) : X i j = 0 := by
  have he := congrArg (fun M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B => M i j) hX.eq
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, ← (Algebra.commutes (wt j) (X i j)),
    ← Algebra.smul_def, ← Algebra.smul_def] at he
  have hz : (wt i - wt j) • X i j = 0 := by rw [sub_smul, he, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h)

private theorem split_weight_blocks (t : Fˣ) (h₀ : (t : F) ≠ 1) (h₁ : t.inv ≠ 1) (h₂ : (t : F) ≠ t.inv)
    (X : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)
    (hX : Commute (Matrix.diagonal (fun i => algebraMap F B (Sum.elim ![t.val, t.inv] (fun _ => 1) i))) X) :
    X = Matrix.fromBlocks (Matrix.diagonal ![X (Sum.inl 0) (Sum.inl 0), X (Sum.inl 1) (Sum.inl 1)])
      0 0 X.toBlocks₂₂ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j
    · simp
    · exact off_diagonal_weight_zero _ X hX _ _ h₂
    · exact off_diagonal_weight_zero _ X hX _ _ h₂.symm
    · simp
  · fin_cases i
    · exact off_diagonal_weight_zero _ X hX _ _ h₀
    · exact off_diagonal_weight_zero _ X hX _ _ h₁
  · fin_cases j
    · exact off_diagonal_weight_zero _ X hX _ _ h₀.symm
    · exact off_diagonal_weight_zero _ X hX _ _ h₁.symm
  · rfl

private theorem groundScalar_matrix (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))
    (t : Fˣ) :
    (groundVectorUnits Q P (show Points G.val.X (groundAlgebra F) from
      cocharacterPoint c (groundAlgebra F) t)).val =
      Matrix.diagonal (fun i => algebraMap F B (Sum.elim ![t.val, t.inv] (fun _ => 1) i)) := by
  let R := groundAlgebra F
  let E := Algebra.TensorProduct.lid F B
  rw [groundVectorUnits_matrix]
  change (Q.matrixAt R (spinVectorProjection P R (cocharacterPoint c R t)).val).map E = _
  rw [hc R t, scalarScale_matrix]
  ext i j
  by_cases hij : i = j
  · subst j
    rcases i with i | i
    · fin_cases i
      · exact E.commutes t.val
      · exact E.commutes t.inv
    · simp
  · simp [hij]

private theorem dagger_blockDiagonal (X : Matrix (Fin 2) (Fin 2) B) (W : Matrix (Fin d) (Fin d) B) :
    dagger Q.conjugation.anti (Matrix.fromBlocks X 0 0 W) =
      Matrix.fromBlocks (dagger Q.conjugation.anti X) 0 0 (dagger Q.conjugation.anti W) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [dagger, antiValue]

private theorem centralizing_vector_blocks [Infinite F] (c : Cocharacter G.val)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))
    (g : Points G.val.X (groundAlgebra F)) (hg : Centralizes c g) :
    ∃ t : Bˣ, ∃ W : (Matrix (Fin d) (Fin d) B)ˣ,
      (groundVectorUnits Q P g).val =
        Matrix.fromBlocks (Matrix.diagonal ![t.val, antiValue Q.conjugation.anti t.inv]) 0 0 W.val ∧
      dagger Q.conjugation.anti W.val * Q.complement.val * W.val = Q.complement.val := by
  obtain ⟨t, ht₀, ht₁, ht₂⟩ := exists_distinct_scalar_weights F
  let R := groundAlgebra F
  let z : Points G.val.X R := cocharacterPoint c R t
  have hz := (centralizes_iff c g).mp hg _ (𝟙 _) (unitPoint R t)
  have hz' : Commute (groundVectorUnits Q P z).val (groundVectorUnits Q P g).val := by
    change Commute (g : Points G.val.X R) z at hz
    exact (hz.symm.map (groundVectorUnits Q P)).map (Units.coeHom _)
  have hv (k : Points G.val.X R) (hk : Commute (groundVectorUnits Q P z).val (groundVectorUnits Q P k).val) :
      let M := (groundVectorUnits Q P k).val
      M = Matrix.fromBlocks (Matrix.diagonal ![M (Sum.inl 0) (Sum.inl 0), M (Sum.inl 1) (Sum.inl 1)])
        0 0 M.toBlocks₂₂ := by
    have hs : (groundVectorUnits Q P z).val =
        Matrix.diagonal (fun i => algebraMap F B (Sum.elim ![t.val, t.inv] (fun _ => 1) i)) :=
      groundScalar_matrix Q P c hc t
    rw [hs] at hk
    exact split_weight_blocks t ht₀ ht₁ ht₂ _ hk
  let X := (groundVectorUnits Q P g).val
  let Y := (groundVectorUnits Q P g⁻¹).val
  let D₀ (M : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B) : Fin 2 → B :=
    ![M (Sum.inl 0) (Sum.inl 0), M (Sum.inl 1) (Sum.inl 1)]
  have hX : X = Matrix.fromBlocks (Matrix.diagonal (D₀ X)) 0 0 X.toBlocks₂₂ := hv g hz'
  have hY : Y = Matrix.fromBlocks (Matrix.diagonal (D₀ Y)) 0 0 Y.toBlocks₂₂ := by
    apply hv g⁻¹
    have w := (hz.symm.inv_right.map (groundVectorUnits Q P)).map (Units.coeHom _)
    exact w
  have hxym : Matrix.fromBlocks
      (Matrix.diagonal (fun i => D₀ X i * D₀ Y i)) 0 0 (X.toBlocks₂₂ * Y.toBlocks₂₂) = 1 := by
    have hx : X * Y = 1 := by
      change (groundVectorUnits Q P g).val * (groundVectorUnits Q P g⁻¹).val = 1
      rw [map_inv]
      exact (groundVectorUnits Q P g).val_inv
    conv at hx => lhs; arg 1; rw [hX]
    conv at hx => lhs; arg 2; rw [hY]
    simpa [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal'] using hx
  have hyxm : Matrix.fromBlocks
      (Matrix.diagonal (fun i => D₀ Y i * D₀ X i)) 0 0 (Y.toBlocks₂₂ * X.toBlocks₂₂) = 1 := by
    have hy : Y * X = 1 := by
      change (groundVectorUnits Q P g⁻¹).val * (groundVectorUnits Q P g).val = 1
      rw [map_inv]
      exact (groundVectorUnits Q P g).inv_val
    conv at hy => lhs; arg 1; rw [hY]
    conv at hy => lhs; arg 2; rw [hX]
    simpa [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal'] using hy
  let s : Bˣ := ⟨D₀ X 0, D₀ Y 0, by
      simpa using congrArg (fun M => M (Sum.inl 0) (Sum.inl 0)) hxym, by
      simpa using congrArg (fun M => M (Sum.inl 0) (Sum.inl 0)) hyxm⟩
  have hWone : (1 : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B).toBlocks₂₂ = 1 := by
    ext i j
    simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  let W : (Matrix (Fin d) (Fin d) B)ˣ :=
    ⟨X.toBlocks₂₂, Y.toBlocks₂₂, by simpa [hWone] using congrArg Matrix.toBlocks₂₂ hxym,
      by simpa [hWone] using congrArg Matrix.toBlocks₂₂ hyxm⟩
  have hIso := groundVectorUnits_isometry Q P g
  change dagger Q.conjugation.anti X * quaternionHyperbolicGram Q.complement.val * X =
    quaternionHyperbolicGram Q.complement.val at hIso
  have hIso' :
      Matrix.fromBlocks
        (dagger Q.conjugation.anti (Matrix.diagonal (D₀ X)) * (!![0, 1; -1, 0]) *
          Matrix.diagonal (D₀ X)) 0 0
        (dagger Q.conjugation.anti W.val * Q.complement.val * W.val) =
        quaternionHyperbolicGram Q.complement.val := by
    conv at hIso => lhs; arg 1; arg 1; arg 2; rw [hX]
    conv at hIso => lhs; arg 2; rw [hX]
    simpa [dagger_blockDiagonal, quaternionHyperbolicGram, Matrix.fromBlocks_multiply, W] using hIso
  have hpair : antiValue Q.conjugation.anti s.val * D₀ X 1 = 1 := by
    have hh := congrArg (fun M => M (Sum.inl 0) (Sum.inl 1)) hIso'
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_two, dagger,
      quaternionHyperbolicGram, antiValue, s, D₀] using hh
  have hs : D₀ X 1 = antiValue Q.conjugation.anti s.inv := by
    calc
      _ = antiValue Q.conjugation.anti s.inv * (antiValue Q.conjugation.anti s.val * D₀ X 1) := by
        have hh : antiValue Q.conjugation.anti s.inv * antiValue Q.conjugation.anti s.val = 1 :=
          bar_inv_mul Q.conjugation.anti s
        rw [← mul_assoc, hh, one_mul]
      _ = _ := by rw [hpair, mul_one]
  refine ⟨s, W, ?_, ?_⟩
  · change X = Matrix.fromBlocks _ 0 0 _
    refine hX.trans ?_
    congr 2
    funext i
    fin_cases i
    · rfl
    · exact hs
  · simpa [quaternionHyperbolicGram] using congrArg Matrix.toBlocks₂₂ hIso'

end QuaternionLevi

open Specs.Arithmetic.QuaternionSpinScaleCover (inverseConjugateUnit)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)

section LeviWords

open private hermitianValue_congr from LinearAlgebraicGroups.Arithmetic.SymplecticDivisionForms

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val}

private def matrixOnColumns (X : Matrix (Fin d) (Fin d) B) :
    (Fin d → B) →ₗ[Bᵐᵒᵖ] (Fin d → B) where
  toFun v := X *ᵥ v
  map_add' x y := Matrix.mulVec_add X x y
  map_smul' a x := by
    ext i
    change (X *ᵥ fun j => x j * unop a) i = (X *ᵥ x) i * unop a
    simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

private def unitsOnColumns (X : (Matrix (Fin d) (Fin d) B)ˣ) :
    (Fin d → B) ≃ₗ[Bᵐᵒᵖ] (Fin d → B) :=
  LinearEquiv.ofLinearMap (matrixOnColumns X.val) (matrixOnColumns X.inv)
    (by apply LinearMap.ext; intro x; change X.val *ᵥ (X.inv *ᵥ x) = x; rw [Matrix.mulVec_mulVec, X.val_inv, Matrix.one_mulVec])
    (by apply LinearMap.ext; intro x; change X.inv *ᵥ (X.val *ᵥ x) = x; rw [Matrix.mulVec_mulVec, X.inv_val, Matrix.one_mulVec])

private noncomputable def columnUnits :
    ((Fin d → B) ≃ₗ[Bᵐᵒᵖ] (Fin d → B)) →* (Matrix (Fin d) (Fin d) B)ˣ :=
  MonoidHom.toHomUnits
    { toFun g := columnMatrix g.toLinearMap
      map_one' := by
        apply Matrix.mulVec_injective
        funext x
        rw [columnMatrix_mulVec, Matrix.one_mulVec]
        rfl
      map_mul' g h := by
        apply Matrix.mulVec_injective
        funext x
        rw [columnMatrix_mulVec, ← Matrix.mulVec_mulVec, columnMatrix_mulVec, columnMatrix_mulVec]
        rfl }

private theorem column_units_inverse (X : (Matrix (Fin d) (Fin d) B)ˣ) :
    columnUnits (unitsOnColumns X) = X := by
  apply Units.ext
  change columnMatrix (unitsOnColumns X).toLinearMap = X.val
  apply Matrix.mulVec_injective
  funext x
  rw [columnMatrix_mulVec]
  rfl

private noncomputable def leviUnits :
    (Bˣ × (Matrix (Fin d) (Fin d) B)ˣ) →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B)ˣ :=
  MonoidHom.toHomUnits
    { toFun z := Matrix.fromBlocks (Matrix.diagonal ![z.1.val,
        (inverseConjugateUnit Q.conjugation.anti.toMonoidHom z.1).val]) 0 0 z.2.val
      map_one' := by
        ext i j
        rcases i with i | i <;> rcases j with j | j
        · fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
        · simp [Matrix.one_apply]
        · simp [Matrix.one_apply]
        · simp [Matrix.one_apply]
      map_mul' x y := by
        rw [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal']
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul, Matrix.mul_zero,
          Matrix.zero_mul, zero_add, add_zero]
        congr 2
        funext i
        fin_cases i <;> rfl }

private theorem ground_scale (t : Bˣ) :
    Units.map (Algebra.TensorProduct.lid F B).toRingHom.mapMatrix.toMonoidHom
      (Units.map (Q.matrixAt (groundAlgebra F)).toMonoidHom
        (quaternionScale Q (groundAlgebra F) (Units.map (intoTensor (groundAlgebra F) B).toMonoidHom t))) =
      leviUnits Q (t, 1) := by
  apply Units.ext
  let R := groundAlgebra F
  change (Q.matrixAt R (quaternionScale Q R (Units.map (intoTensor R B).toMonoidHom t)).val).map
      (Algebra.TensorProduct.lid F B) = _
  rw [scale_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [leviUnits, intoTensor, inverseConjugateUnit]
    change (Algebra.TensorProduct.lid F B)
      (antiValue (coefficientConjugation Q R) (1 ⊗ₜ[F] t.val)) =
      antiValue Q.conjugation.anti t.val
    rw [extendAnti_tmul]
    simp
  · simp [leviUnits]
  · simp [leviUnits]
  · by_cases h : i = j <;> simp [leviUnits, Matrix.one_apply, h]

private theorem rotation_parameter (h2 : (2 : F) ≠ 0) (hd : degree F B = 2)
    (q r : Bˣ) (hq : antiValue Q.conjugation.anti q.val = -q.val)
    (hr : Commute r.val q.val) (hr₀ : antiValue Q.conjugation.anti r.val * r.val = 1)
    (hr₁ : r ≠ 1) :
    ∃ b : Bˣ, b.val - antiValue Q.conjugation.anti b.val = -(q.val)⁻¹ ∧ 1 + (q.val)⁻¹ * (b.val)⁻¹ = r.val := by
  obtain ⟨E, hE, hFE, hSep, j, qE, hqE, _, hcentral, _, hnorm, hparams, _⟩ :=
    fixed_line_parameters h2 hB hd Q.conjugation Q.canonical q hq
  letI : Field E := hE
  letI : Algebra F E := hFE
  obtain ⟨x, hx⟩ := (hcentral r.val).mp hr
  have hx₀ : x ≠ 0 := by
    intro H
    rw [H, map_zero] at hx
    exact r.ne_zero hx.symm
  let s := Units.mk0 x hx₀
  have hs : s ≠ 1 := by
    intro H
    apply hr₁
    apply Units.ext
    rw [← hx, show x = 1 from congrArg Units.val H, map_one]
    rfl
  have hsN : Algebra.norm F (s : E) = 1 := by
    apply (algebraMap F B).injective
    rw [← hnorm, show j (s : E) = r.val from hx, hr₀, map_one]
  obtain ⟨b, _, hbar, hb⟩ := hparams s hsN hs
  refine ⟨Units.map j.toMonoidHom b, ?_, ?_⟩
  · exact hbar
  · change 1 + (q.val)⁻¹ * (j b.val)⁻¹ = _
    rw [hb]
    exact hx

private theorem groundInterchange_matrix (L : ShearLifts Q P c) (w : Fin d → B) (q : Bˣ)
    (a : B) (b : Bˣ)
    (h : ShearAdmissible Q w q (groundAlgebra F) (intoTensor (groundAlgebra F) B a)
      (Units.map (intoTensor (groundAlgebra F) B).toMonoidHom b).val) :
    (groundVectorUnits Q P (interchangeLift Q P L w q (groundAlgebra F) _ _ h)).val =
      Matrix.fromBlocks !![0, b.val; -antiValue Q.conjugation.anti b.inv, 0] 0 0
        (1 + Matrix.of fun i j => w i * (q.inv * antiValue Q.conjugation.anti a * b.inv * a) *
          q.inv * ∑ k, antiValue Q.conjugation.anti (w k) * Q.complement.val k j) := by
  rw [groundVectorUnits_matrix, interchangeLift_formula]
  let E := Algebra.TensorProduct.lid F B
  have ht (x : B) : E (1 ⊗ₜ[F] x) = x := by simp [E]
  have hf (x : B) :
      E (antiValue (coefficientConjugation Q (groundAlgebra F)) (1 ⊗ₜ[F] x)) =
        antiValue Q.conjugation.anti x := by rw [extendAnti_tmul, ht]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [interchangeMatrix, Matrix.map_apply, intoTensor, E, extendAnti_tmul]
  · simp [interchangeMatrix]
  · simp [interchangeMatrix]
  · simp [interchangeMatrix, Matrix.map_apply, complementGram, intoTensor, extendAnti_tmul, Matrix.one_apply]

private theorem lift_word_mem (L : ShearLifts Q P c)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c))
    (w : Fin d → B) (q : Bˣ) (a : groundAlgebra F ⊗[F] B) (b : (groundAlgebra F ⊗[F] B)ˣ)
    (h : ShearAdmissible Q w q (groundAlgebra F) a b.val) :
    interchangeLift Q P L w q (groundAlgebra F) a b h ∈ rationalRadicals U V := by
  unfold interchangeLift liftedInterchange
  dsimp only
  exact (rationalRadicals U V).mul_mem
    ((rationalRadicals U V).mul_mem
      (shearLift_mem_radicals Q P L U V false w q _ _ _)
      (shearLift_mem_radicals Q P L U V true w q _ _ h))
    (shearLift_mem_radicals Q P L U V false w q _ _ _)

private theorem lineRotation_lift_column (h2 : (2 : F) ≠ 0) (hd : degree F B = 2) (L : ShearLifts Q P c)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c))
    (g : (Fin d → B) ≃ₗ[Bᵐᵒᵖ] (Fin d → B)) (hg : IsLineRotation (complementSkewPairing Q) g) :
    ∃ t : Bˣ, ∃ x ∈ rationalRadicals U V,
      groundVectorUnits Q P x = leviUnits Q (t, columnUnits g) := by
  obtain ⟨w, r, hw, hr, hr₀, hg⟩ := hg
  by_cases hr₁ : r = 1
  · subst r
    have hg₁ : g = 1 := by
      ext x i
      simp [hg]
    refine ⟨1, 1, (rationalRadicals U V).one_mem, ?_⟩
    rw [hg₁, map_one, map_one]
    exact (leviUnits Q).map_one.symm
  let q := Units.mk0 ((complementSkewPairing Q).value w w) hw
  have hq : hermitianValue Q.conjugation.anti Q.complement.val w w = q.val := rfl
  obtain ⟨b, hb, hδ⟩ := rotation_parameter Q h2 hd q r (fixed_line_pure Q w q hq) hr hr₀ hr₁
  let R := groundAlgebra F
  let j : B →ₐ[F] R ⊗[F] B := intoTensor R B
  let bb := Units.map j.toMonoidHom b
  let b₁ := Units.map j.toMonoidHom (1 : Bˣ)
  have hab : ShearAdmissible Q w q R (j 1) bb.val := by
    refine ⟨hq, ?_⟩
    have hbinv : (q.val)⁻¹ = q.inv := (Units.val_inv_eq_inv_val q).symm
    rw [hbinv] at hb
    have he := congrArg j hb
    change j b.val - antiValue (coefficientConjugation Q R) (j b.val) =
      -(j 1 * j q.inv * antiValue (coefficientConjugation Q R) (j 1))
    have hbar (x : B) : antiValue (coefficientConjugation Q R) (j x) =
        j (antiValue Q.conjugation.anti x) := extendAnti_tmul Q.conjugation.anti _ _
    simp only [hbar, bar_one, map_one, one_mul, mul_one]
    simpa only [map_sub, map_neg] using he
  have ha₁ : ShearAdmissible Q w q R (j 0) b₁.val := by
    refine ⟨hq, ?_⟩
    change j 1 - antiValue (coefficientConjugation Q R) (j 1) =
      -(j 0 * j q.inv * antiValue (coefficientConjugation Q R) (j 0))
    simp [antiValue]
  let x := interchangeLift Q P L w q R _ _ hab
  let y := interchangeLift Q P L w q R _ _ ha₁
  have hx : x ∈ rationalRadicals U V := lift_word_mem Q P L U V w q _ _ hab
  have hy : y ∈ rationalRadicals U V := lift_word_mem Q P L U V w q _ _ ha₁
  have hU (i j' : Fin d) : (columnUnits g).val i j' =
      (1 : Matrix (Fin d) (Fin d) B) i j' +
        w i * (r.val - 1) * q.inv * ∑ k, antiValue Q.conjugation.anti (w k) * Q.complement.val k j' := by
    change g (Pi.single j' 1) i = _
    rw [hg]
    simp only [complementSkewPairing, hermitianValue, Matrix.mulVec_single_one, dotProduct, Pi.add_apply,
      Pi.smul_apply]
    have hdg : (Pi.single j' (1 : B) : Fin d → B) i = (1 : Matrix (Fin d) (Fin d) B) i j' := by
      simp [Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hdg]
    congr 1
    have hq' : ∑ x, antiValue Q.conjugation.anti (w x) * (Q.complement.val *ᵥ w) x = q.val := hq
    rw [hq']
    change w i * ((r.val - 1) * (q.val)⁻¹ *
      (∑ x, antiValue Q.conjugation.anti (w x) * Q.complement.val x j')) = _
    have he : (q.val)⁻¹ = q.inv := (Units.val_inv_eq_inv_val q).symm
    rw [he]
    simp only [mul_assoc]
  have hu : (groundVectorUnits Q P x).val = (leviUnits Q (b, columnUnits g) * groundVectorUnits Q P y).val := by
    rw [Units.val_mul]
    rw [show (groundVectorUnits Q P x).val = _ from groundInterchange_matrix Q P L w q 1 b hab,
      show (groundVectorUnits Q P y).val = _ from groundInterchange_matrix Q P L w q 0 1 ha₁]
    have hδ' : q.inv * b.inv = r.val - 1 := by
      change (↑q⁻¹ : B) * (↑b⁻¹ : B) = _
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hδ]
      abel
    change _ = Matrix.fromBlocks (Matrix.diagonal ![b.val, antiValue Q.conjugation.anti b.inv]) 0 0
      (columnUnits g).val * _
    rw [Matrix.fromBlocks_multiply]
    ext i j'
    rcases i with i | i <;> rcases j' with j' | j'
    · fin_cases i <;> fin_cases j' <;> simp [Matrix.diagonal_mul, antiValue]
    · simp
    · simp
    · have hδ'' : (q.val)⁻¹ * (b.val)⁻¹ = r.val - 1 := by rw [← hδ]; abel
      have hzero : (Matrix.of fun (_ _ : Fin d) => (0 : B)) = 0 := rfl
      simpa [antiValue, hδ'', hzero, Matrix.one_apply] using (hU i j').symm
  refine ⟨b, x * y⁻¹, (rationalRadicals U V).mul_mem hx ((rationalRadicals U V).inv_mem hy), ?_⟩
  rw [map_mul, map_inv, Units.ext hu, mul_inv_cancel_right]

private theorem remove_perpendicular_action [Infinite F] (h2 : (2 : F) ≠ 0) (hd : degree F B = 2)
    (L : ShearLifts Q P c)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c))
    (g : Points G.val.X (groundAlgebra F)) (hg : Centralizes c g) :
    ∃ x ∈ rationalRadicals U V, ∃ t : (groundAlgebra F ⊗[F] B)ˣ,
      spinVectorProjection P (groundAlgebra F) (x⁻¹ * g) = quaternionScale Q (groundAlgebra F) t := by
  let R := groundAlgebra F
  let H := rationalRadicals U V
  let D := groundVectorUnits Q P
  let v := leviUnits Q
  let n := MonoidHom.snd Bˣ (Matrix (Fin d) (Fin d) B)ˣ
  let L₀ := (H.map D).comap v
  let H₀ := (L₀.map n).comap columnUnits
  have h₀ : Subgroup.closure {g | IsLineRotation (complementSkewPairing Q) g} ≤ H₀ := by
    apply (Subgroup.closure_le H₀).mpr
    intro f hf
    obtain ⟨t, x, hx, he⟩ := lineRotation_lift_column Q P h2 hd L U V f hf
    exact ⟨(t, columnUnits f), ⟨x, hx, he⟩, rfl⟩
  obtain ⟨t, W, hW, hIsom⟩ := centralizing_vector_blocks Q P c hc g hg
  let f := unitsOnColumns W
  have hfiso (x y : Fin d → B) :
      (complementSkewPairing Q).value (f x) (f y) = (complementSkewPairing Q).value x y := by
    change hermitianValue Q.conjugation.anti Q.complement.val (W.val *ᵥ x) (W.val *ᵥ y) =
      hermitianValue Q.conjugation.anti Q.complement.val x y
    rw [hermitianValue_congr, hIsom]
  letI : Module.Finite Bᵐᵒᵖ (Fin d → B) :=
    Module.Finite.equiv (LinearEquiv.piCongrRight fun _ : Fin d => rightCoordinates (B := B)).symm
  have hf := h₀ ((perpendicular_rotation_generation h2 hB hd Q.conjugation Q.canonical _).2 f |>.mp hfiso)
  change columnUnits f ∈ L₀.map n at hf
  rw [show columnUnits f = W from column_units_inverse W] at hf
  obtain ⟨p, hp, hpW⟩ := hf
  change p.2 = W at hpW
  obtain ⟨x, hx, hv⟩ := hp
  change D x = v p at hv
  have hgv : D g = v (t, W) := Units.ext hW
  have he : D (x⁻¹ * g) = v (p.1⁻¹ * t, 1) := by
    rw [map_mul, map_inv, hv, hgv, ← map_inv, ← map_mul]
    apply congrArg v
    exact Prod.ext rfl (by change p.2⁻¹ * W = 1; rw [hpW, inv_mul_cancel])
  let s : (R ⊗[F] B)ˣ := Units.map (intoTensor R B).toMonoidHom (p.1⁻¹ * t)
  refine ⟨x, hx, s, ?_⟩
  have hscale := ground_scale Q (p.1⁻¹ * t)
  rw [← hscale] at he
  apply Units.ext
  apply (Q.matrixAt R).injective
  apply Matrix.map_injective (Algebra.TensorProduct.lid F B).injective
  exact congrArg Units.val he

end LeviWords

section ScalarHyperbolicCell

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)
  (w : Fin d → B) (q : Bˣ)
  (hw : hermitianValue Q.conjugation.anti Q.complement.val w w = (q : B))

private def scalarPlaneBlock (R : TestAlgebra F) (d : ℕ) (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B) :=
  Matrix.fromBlocks (M.map (algebraMap R (R ⊗[F] B))) 0 0 1

private theorem scalarPlaneBlock_mul (R : TestAlgebra F) (d : ℕ) (M N : Matrix (Fin 2) (Fin 2) R) :
    scalarPlaneBlock (B := B) R d (M * N) =
      scalarPlaneBlock (B := B) R d M * scalarPlaneBlock (B := B) R d N := by
  simp [scalarPlaneBlock, Matrix.fromBlocks_multiply, ← RingHom.mapMatrix_apply]

include hw in
private theorem scalar_admissible (R : TestAlgebra F) (x : R) :
    ShearAdmissible Q w q R 0 (algebraMap R (R ⊗[F] B) x) := by
  refine ⟨hw, ?_⟩
  rw [antiValue_scalar, sub_self, zero_mul, zero_mul, neg_zero]

private noncomputable def scalarTransvectionLift (upper : Bool) (R : TestAlgebra F) (x : R) :
    Points G.val.X R :=
  let b := if upper then x else -x
  L.lift upper w q R 0 (algebraMap R (R ⊗[F] B) b) (scalar_admissible Q w q hw R b)

private theorem scalar_transvection_matrix (upper : Bool) (R : TestAlgebra F) (x : R) :
    vectorMatrix Q P R (scalarTransvectionLift Q P L w q hw upper R x) =
      scalarPlaneBlock (B := B) R d (if upper then !![1, x; 0, 1] else !![1, 0; x, 1]) := by
  unfold scalarTransvectionLift
  dsimp only
  rw [L.formula]
  cases upper <;> ext i j <;> rcases i with i | i <;> rcases j with j | j
  all_goals try fin_cases i
  all_goals try fin_cases j
  all_goals simp [shearMatrix, scalarPlaneBlock, antiValue, ← Algebra.TensorProduct.one_def, ← TensorProduct.neg_tmul]

private theorem scalar_diagonal_matrix (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))
    (R : TestAlgebra F) (t : Rˣ) :
    vectorMatrix Q P R (cocharacterPoint c R t) =
      scalarPlaneBlock (B := B) R d !![t.val, 0; 0, (↑t⁻¹ : R)] := by
  change Q.matrixAt R (spinVectorProjection P R (cocharacterPoint c R t)).val = _
  rw [hc, scalarScale_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · fin_cases i <;> fin_cases j <;> simp [scalarPlaneBlock]
  · simp [scalarPlaneBlock, Matrix.diagonal_apply_ne]
  · simp [scalarPlaneBlock, Matrix.diagonal_apply_ne]
  · simp [scalarPlaneBlock, Matrix.one_apply, Matrix.diagonal_apply]

private noncomputable def gaussianSpinLift (R : TestAlgebra F) (M : Matrix (Fin 2) (Fin 2) R) (a : Rˣ) :
    Points G.val.X R :=
  scalarTransvectionLift Q P L w q hw false R (M 1 0 * (↑a⁻¹ : R)) *
    (show Points G.val.X R from cocharacterPoint c R a) *
    scalarTransvectionLift Q P L w q hw true R ((↑a⁻¹ : R) * M 0 1)

private theorem two_by_two_gaussian {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (a : Rˣ) (ha : a.val = M 0 0) (hdet : M.det = 1) :
    !![1, 0; M 1 0 * (↑a⁻¹ : R), 1] * !![a.val, 0; 0, (↑a⁻¹ : R)] * !![1, (↑a⁻¹ : R) * M 0 1; 0, 1] = M := by
  have hdet' : a.val * M 1 1 = 1 + M 0 1 * M 1 0 := by
    rw [ha]
    rw [Matrix.det_fin_two, sub_eq_iff_eq_add] at hdet
    exact hdet
  have hdiag : M 1 0 * ((↑a⁻¹ : R) * M 0 1) + (↑a⁻¹ : R) = M 1 1 := by
    calc
      _ = (↑a⁻¹ : R) * (1 + M 0 1 * M 1 0) := by ring
      _ = _ := by
        have h := a.inv_mul
        rw [← hdet', ← mul_assoc, h, one_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  · exact ha
  · simpa only [mul_assoc] using hdiag

private theorem gaussianSpinLift_matrix
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))
    (R : TestAlgebra F) (M : Matrix (Fin 2) (Fin 2) R) (a : Rˣ) (ha : a.val = M 0 0) (hdet : M.det = 1) :
    vectorMatrix Q P R (gaussianSpinLift Q P L w q hw R M a) = scalarPlaneBlock (B := B) R d M := by
  rw [gaussianSpinLift, vectorMatrix_mul, vectorMatrix_mul,
    scalar_transvection_matrix, scalar_transvection_matrix, scalar_diagonal_matrix Q P hc]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← scalarPlaneBlock_mul, ← scalarPlaneBlock_mul]
  exact congrArg (scalarPlaneBlock (B := B) R d) (two_by_two_gaussian M a ha hdet)

end ScalarHyperbolicCell

section ScalarTransvections

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)

private theorem scalarTransvectionLift_map (w : Fin d → B) (q : Bˣ)
    (hw : hermitianValue Q.conjugation.anti Q.complement.val w w = q.val)
    (upper : Bool) {R S : TestAlgebra F} (f : R ⟶ S) (x : R) :
    mapPoints f (scalarTransvectionLift Q P L w q hw upper R x) =
      scalarTransvectionLift Q P L w q hw upper S (f.hom x) := by
  unfold scalarTransvectionLift
  dsimp only
  apply shearLift_map_congr Q P L (upper := upper) w q f
  · exact map_zero _
  · cases upper <;> simp [tensorMap]

include L in
private theorem scalar_cocharacter_noncentral [Infinite F] (h2 : (2 : F) ≠ 0)
    (hd : degree F B = 2) (hd₀ : 0 < d)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t)) :
    IsNoncentral c := by
  let h := complementSkewPairing Q
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd₀
  have hex : ∃ v : Fin d → B, v ≠ 0 := ⟨1, one_ne_zero⟩
  obtain ⟨w, hw⟩ := exists_nonzero_self_pairing h h2 hB hd Q.canonical hex
  let q := Units.mk0 (h.value w w) hw
  have hq : hermitianValue Q.conjugation.anti Q.complement.val w w = q.val := rfl
  let R := groundAlgebra F
  let y := scalarTransvectionLift Q P L w q hq true R 1
  refine ⟨(testSpec F).obj (Opposite.op R), y, fun hy => ?_⟩
  obtain ⟨t, W, hform, _⟩ := centralizing_vector_blocks Q P c hc y hy
  have he : (groundVectorUnits Q P y).val (Sum.inl 0) (Sum.inl 1) = (1 : B) := by
    rw [groundVectorUnits_matrix,
      show vectorMatrix Q P R y = _ from scalar_transvection_matrix Q P L w q hq true R 1]
    simp [scalarPlaneBlock]
  rw [hform] at he
  exact (zero_ne_one : (0 : B) ≠ 1) (by simpa using he)

end ScalarTransvections

section CompareNormalizedLifts

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private theorem equal_spin_lifts_on_path (h2 : (2 : F) ≠ 0) (R : TestAlgebra F)
    (f : Polynomial R) (hf : (polynomialEvaluate R 0).hom f = 1)
    (x y : Points G.val.X (polynomialPath R f))
    (hm : vectorMatrix Q P (polynomialPath R f) x = vectorMatrix Q P (polynomialPath R f) y)
    (h₀ : mapPoints (polynomialPathEval R f 0 (hf.symm ▸ isUnit_one)) x =
      mapPoints (polynomialPathEval R f 0 (hf.symm ▸ isUnit_one)) y) : x = y := by
  let A := polynomialPath R f
  let p := polynomialPathEval R f 0 (hf.symm ▸ isUnit_one)
  let m : Points G.val.X A →* Points G.val.X R := (((groupPointsFunctor F).obj G.val).map p).hom
  have hp : x ≫ P.projection.hom.hom = y ≫ P.projection.hom.hom := by
    apply neutralMatrixUnits_injective Q P A
    exact Units.ext hm
  let z := x⁻¹ * y
  have hz : z ≫ P.projection.hom.hom = 1 := by
    change (x⁻¹ * y) ≫ P.projection.hom.hom = _
    rw [MonObj.mul_comp, GrpObj.inv_comp, hp, inv_mul_cancel]
  obtain ⟨k, hk⟩ := (schemeKernel_sections P.isKernel z).mpr hz
  change Points P.kernel.group.X A at k
  change k ≫ P.kernel.inclusion.hom.hom = z at hk
  have hz₀ : m z = 1 := by
    change m (x⁻¹ * y) = 1
    have h : m x = m y := h₀
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hk₀ : mapPoints p k = 1 := by
    letI : IsClosedImmersion P.kernel.inclusion.hom.hom.left := P.kernel.isClosedImmersion
    letI : Mono P.kernel.inclusion.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono P.kernel.inclusion.hom.hom).mp
    change mapPoints p (k ≫ P.kernel.inclusion.hom.hom) = (1 : Points P.kernel.group.X R) ≫ P.kernel.inclusion.hom.hom
    rw [hk, MonObj.one_comp]
    exact hz₀
  let s := (P.kernelPoints A k).val
  have hs : s ^ 2 = 1 := (mem_rootsOfUnity 2 s).mp (P.kernelPoints A k).property
  have hs₀ : p.hom s.val = 1 := by
    rw [← P.kernelNatural A R p k, hk₀, map_one]
    rfl
  have hss : s = 1 := polynomialPath_square_one R h2 f hf _ s hs hs₀
  have hk1 : k = 1 := by
    apply (P.kernelPoints A).injective
    rw [map_one]
    exact Subtype.ext hss
  rw [hk1, MonObj.one_comp] at hk
  exact inv_mul_eq_one.mp hk.symm

end CompareNormalizedLifts

open LinearAlgebraicGroups.CocharacterDynamics (mapPoints_cocharacterPoint mapPoints_comp)

section ShiftedHyperbolicCell

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)
  (w : Fin d → B) (q : Bˣ)
  (hw : LinearAlgebraicGroups.Specs.SymplecticDivisionForms.hermitianValue
    Q.conjugation.anti Q.complement.val w w = q.val)

private theorem gaussianSpinLift_map {R S : TestAlgebra F} (f : R ⟶ S)
    (M : Matrix (Fin 2) (Fin 2) R) (a : Rˣ) :
    mapPoints f (gaussianSpinLift Q P L w q hw R M a) =
      gaussianSpinLift Q P L w q hw S (M.map f.hom) (Units.map f.hom.toMonoidHom a) := by
  let m := changeSpinPoints (G := G) f
  unfold gaussianSpinLift
  change m (_ * _ * _) = _
  rw [map_mul m, map_mul m]
  change mapPoints f _ * (show Points G.val.X S from mapPoints f (cocharacterPoint c R a)) *
    mapPoints f _ = _
  rw [mapPoints_cocharacterPoint, scalarTransvectionLift_map, scalarTransvectionLift_map]
  simp only [map_mul, Matrix.map_apply]
  rfl

private def upperScalarMatrix {R : Type*} [Ring R] (x : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, x; 0, 1]

private theorem upperScalarMatrix_det {R : Type*} [CommRing R] (x : R) :
    (upperScalarMatrix x).det = 1 := by simp [upperScalarMatrix, Matrix.det_fin_two]

private theorem upperScalarMatrix_shift {R : Type*} [Ring R] (M : Matrix (Fin 2) (Fin 2) R) (x : R) :
    (upperScalarMatrix x * M) 0 0 = M 0 0 + x * M 1 0 := by
  simp [upperScalarMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem upperScalarMatrix_cancel {R : Type*} [Ring R] (x : R) :
    upperScalarMatrix (-x) * upperScalarMatrix x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperScalarMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private noncomputable def shiftedGaussianLift (R : TestAlgebra F)
    (M : Matrix (Fin 2) (Fin 2) R) (x : R) (a : Rˣ) : Points G.val.X R :=
  scalarTransvectionLift Q P L w q hw true R (-x) *
    gaussianSpinLift Q P L w q hw R (upperScalarMatrix x * M) a

private theorem shiftedGaussianLift_map {R S : TestAlgebra F} (f : R ⟶ S)
    (M : Matrix (Fin 2) (Fin 2) R) (x : R) (a : Rˣ) :
    mapPoints f (shiftedGaussianLift Q P L w q hw R M x a) =
      shiftedGaussianLift Q P L w q hw S (M.map f.hom) (f.hom x) (Units.map f.hom.toMonoidHom a) := by
  let m := changeSpinPoints (G := G) f
  unfold shiftedGaussianLift
  change m (_ * _) = _
  rw [map_mul m]
  change mapPoints f _ * mapPoints f _ = _
  rw [scalarTransvectionLift_map, gaussianSpinLift_map, map_neg]
  congr 2
  rw [Matrix.map_mul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperScalarMatrix]

private theorem shiftedGaussianLift_matrix
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), spinVectorProjection P R (cocharacterPoint c R t) =
      quaternionScale Q R (scalarParameter R t))
    (R : TestAlgebra F) (M : Matrix (Fin 2) (Fin 2) R) (x : R) (a : Rˣ)
    (hdet : M.det = 1) (ha : a.val = M 0 0 + x * M 1 0) :
    vectorMatrix Q P R (shiftedGaussianLift Q P L w q hw R M x a) = scalarPlaneBlock (B := B) R d M := by
  have hd : (upperScalarMatrix x * M).det = 1 := by rw [Matrix.det_mul, upperScalarMatrix_det, hdet, one_mul]
  have hs : a.val = (upperScalarMatrix x * M) 0 0 := ha.trans (upperScalarMatrix_shift M x).symm
  rw [shiftedGaussianLift, vectorMatrix_mul, gaussianSpinLift_matrix Q P L w q hw hc R _ a hs hd,
    scalar_transvection_matrix, if_pos rfl]
  change scalarPlaneBlock (B := B) R d (upperScalarMatrix (-x)) *
    scalarPlaneBlock (B := B) R d (upperScalarMatrix x * M) = _
  rw [← scalarPlaneBlock_mul, ← Matrix.mul_assoc, upperScalarMatrix_cancel, Matrix.one_mul]

/-- Two choices of shift with invertible pivots give the same spin point.
Interpolate the shift and invert its pivot on the polynomial path. -/
private theorem shiftedGaussianLift_independent (h2 : (2 : F) ≠ 0)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ), spinVectorProjection P R (cocharacterPoint c R t) =
      quaternionScale Q R (scalarParameter R t))
    (R : TestAlgebra F) (M : Matrix (Fin 2) (Fin 2) R) (hdet : M.det = 1)
    (x₀ x₁ : R) (a₀ a₁ : Rˣ)
    (ha₀ : a₀.val = M 0 0 + x₀ * M 1 0)
    (ha₁ : a₁.val = M 0 0 + x₁ * M 1 0) :
    shiftedGaussianLift Q P L w q hw R M x₀ a₀ =
      shiftedGaussianLift Q P L w q hw R M x₁ a₁ := by
  let S := polynomialAlgebra R
  let v : Polynomial R := Polynomial.C x₀ + Polynomial.X * Polynomial.C (x₁ - x₀)
  let b : Polynomial R := Polynomial.C (M 0 0) + v * Polynomial.C (M 1 0)
  let f : Polynomial R := Polynomial.C (↑a₀⁻¹ : R) * b
  have hC (t x : R) : (polynomialEvaluate R t).hom (Polynomial.C x) = x := Polynomial.eval₂_C _ _
  have hX (t : R) : (polynomialEvaluate R t).hom (Polynomial.X : S) = t := Polynomial.eval₂_X _ _
  have hv (t : R) : (polynomialEvaluate R t).hom v = x₀ + t * (x₁ - x₀) := by
    change (polynomialEvaluate R t).hom (Polynomial.C x₀ + Polynomial.X * Polynomial.C (x₁ - x₀)) = _
    rw [map_add, map_mul, hC, hX, hC]
  have hb (t : R) : (polynomialEvaluate R t).hom b =
      M 0 0 + (polynomialEvaluate R t).hom v * M 1 0 := by
    change (polynomialEvaluate R t).hom (Polynomial.C (M 0 0) + v * Polynomial.C (M 1 0)) = _
    rw [map_add, map_mul, hC, hC]
  have hv₀ : (polynomialEvaluate R 0).hom v = x₀ := by rw [hv, zero_mul, add_zero]
  have hv₁ : (polynomialEvaluate R 1).hom v = x₁ := by rw [hv, one_mul, add_comm, sub_add_cancel]
  have hb₀ : (polynomialEvaluate R 0).hom b = a₀.val := by rw [hb, hv₀, ha₀]
  have hb₁ : (polynomialEvaluate R 1).hom b = a₁.val := by rw [hb, hv₁, ha₁]
  have hf : (polynomialEvaluate R 0).hom f = 1 := by
    change (polynomialEvaluate R 0).hom (Polynomial.C (↑a₀⁻¹ : R) * b) = _
    rw [map_mul, hC, hb₀, a₀.inv_mul]
  have hf₁ : IsUnit ((polynomialEvaluate R 1).hom f) := by
    change IsUnit ((polynomialEvaluate R 1).hom (Polynomial.C (↑a₀⁻¹ : R) * b))
    rw [map_mul, hC, hb₁]
    exact a₀⁻¹.isUnit.mul a₁.isUnit
  let C := polynomialPath R f
  let p := polynomialPathMap R f
  let k := polynomialConstants R ≫ p
  let p₀ := polynomialPathEval R f 0 (hf.symm ▸ isUnit_one)
  let p₁ := polynomialPathEval R f 1 hf₁
  have hk_eval (t : R) (ht : IsUnit ((polynomialEvaluate R t).hom f)) :
      k ≫ polynomialPathEval R f t ht = 𝟙 R := by
    rw [show k = polynomialConstants R ≫ p from rfl, Category.assoc, polynomialPathMap_eval]
    exact CommAlgCat.hom_ext (AlgHom.ext (hC t))
  have hpb : IsUnit (p.hom b) := by
    have hp : IsUnit (p.hom f) := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f
    change IsUnit (p.hom (Polynomial.C (↑a₀⁻¹ : R) * b)) at hp
    rw [map_mul] at hp
    exact isUnit_of_mul_isUnit_right hp
  let y := p.hom v
  let a := hpb.unit
  let M' := M.map k.hom
  have ha : a.val = M' 0 0 + y * M' 1 0 := by
    change a.val = p.hom (Polynomial.C (M 0 0)) + p.hom v * p.hom (Polynomial.C (M 1 0))
    rw [hpb.unit_spec, show b = Polynomial.C (M 0 0) + v * Polynomial.C (M 1 0) from rfl, map_add, map_mul]
  have hdet' : M'.det = 1 := by
    exact (k.hom.map_det M).symm.trans (by rw [hdet, map_one])
  let l := shiftedGaussianLift Q P L w q hw C M' y a
  have h_eval (t : R) (ht : IsUnit ((polynomialEvaluate R t).hom f)) :
      let m := polynomialPathEval R f t ht
      M'.map m.hom = M ∧ m.hom y = (polynomialEvaluate R t).hom v ∧
        (Units.map m.hom.toMonoidHom a).val = (polynomialEvaluate R t).hom b := by
    let m := polynomialPathEval R f t ht
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      exact congrArg (fun j' : R ⟶ R => j'.hom (M i j)) (hk_eval t ht)
    · exact congrArg (fun m' : S ⟶ R => m'.hom v) (polynomialPathMap_eval R f t ht)
    · change m.hom a.val = _
      rw [hpb.unit_spec]
      exact congrArg (fun m' : S ⟶ R => m'.hom b) (polynomialPathMap_eval R f t ht)
  have h₀ : mapPoints p₀ l = shiftedGaussianLift Q P L w q hw R M x₀ a₀ := by
    obtain ⟨hm, hv, hu⟩ := h_eval 0 (hf.symm ▸ isUnit_one)
    change mapPoints p₀ (shiftedGaussianLift Q P L w q hw C M' y a) = _
    rw [shiftedGaussianLift_map, hm, hv, hv₀, Units.ext (hu.trans hb₀)]
  have h₁ : mapPoints p₁ l = shiftedGaussianLift Q P L w q hw R M x₁ a₁ := by
    obtain ⟨hm, hv, hu⟩ := h_eval 1 hf₁
    change mapPoints p₁ (shiftedGaussianLift Q P L w q hw C M' y a) = _
    rw [shiftedGaussianLift_map, hm, hv, hv₁, Units.ext (hu.trans hb₁)]
  let g₀ := shiftedGaussianLift Q P L w q hw R M x₀ a₀
  let g := mapPoints k g₀
  have hid : mapPoints (𝟙 R) g₀ = g₀ := by simp [mapPoints]
  have hzero : mapPoints p₀ g = mapPoints p₀ l := by
    change mapPoints p₀ (mapPoints k g₀) = _
    rw [← mapPoints_comp, hk_eval 0 _, hid]
    exact h₀.symm
  have hvec : vectorMatrix Q P C g = vectorMatrix Q P C l := by
    rw [show g = shiftedGaussianLift Q P L w q hw C M' (k.hom x₀)
      (Units.map k.hom.toMonoidHom a₀) from
        shiftedGaussianLift_map Q P L w q hw k M x₀ a₀]
    have hpar : (Units.map k.hom.toMonoidHom a₀).val = M' 0 0 + k.hom x₀ * M' 1 0 := by
      change k.hom a₀.val = _
      rw [ha₀, map_add, map_mul]
      rfl
    rw [shiftedGaussianLift_matrix Q P L w q hw hc C M' _ _ hdet' hpar,
      show l = shiftedGaussianLift Q P L w q hw C M' y a from rfl,
      shiftedGaussianLift_matrix Q P L w q hw hc C M' y a hdet' ha]
  have hz := equal_spin_lifts_on_path Q P h2 R f hf g l hvec hzero
  calc
    g₀ = mapPoints p₁ g := by
      change _ = mapPoints p₁ (mapPoints k g₀)
      rw [← mapPoints_comp, hk_eval 1 _, hid]
    _ = _ := (congrArg (mapPoints p₁) hz).trans h₁

end ShiftedHyperbolicCell

section PrincipalCover

open Opposite

variable {F : Type u} [Field F] (R : TestAlgebra F)

private noncomputable abbrev principalAlgebra (r : R) : TestAlgebra F :=
  CommAlgCat.of F (Localization.Away r)

private noncomputable def principalMap (r : R) : R ⟶ principalAlgebra R r :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom F R (Localization.Away r))

private noncomputable def principalLift {r : R} {S : TestAlgebra F}
    (f : R ⟶ S) (h : IsUnit (f.hom r)) : principalAlgebra R r ⟶ S :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom r h)

private theorem principalLift_comp {r : R} {S : TestAlgebra F}
    (f : R ⟶ S) (h : IsUnit (f.hom r)) :
    principalMap R r ≫ principalLift R f h = f := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact IsLocalization.Away.lift_eq _ h x

private theorem principalPoints_injective {X : SchemeOver F} {Idx : Type*}
    (s : Idx → R) (hs : Ideal.span (Set.range s) = ⊤)
    (g g' : Points X R)
    (h : ∀ i, mapPoints (principalMap R (s i)) g = mapPoints (principalMap R (s i)) g') :
    g = g' := by
  let U := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) s hs).openCover
  apply Over.OverMorphism.ext
  apply U.hom_ext
  intro i
  exact congrArg Over.Hom.left (h i)

set_option backward.isDefEq.respectTransparency false in
private theorem glue_principal_points {X : SchemeOver F} {Idx : Type*}
    (s : Idx → R) (hs : Ideal.span (Set.range s) = ⊤)
    (g : ∀ i, Points X (principalAlgebra R (s i)))
    (h : ∀ (i j : Idx) (S : TestAlgebra F)
      (a : principalAlgebra R (s i) ⟶ S) (b : principalAlgebra R (s j) ⟶ S),
      principalMap R (s i) ≫ a = principalMap R (s j) ≫ b →
      mapPoints a (g i) = mapPoints b (g j)) :
    ∃ g₀ : Points X R, ∀ i, mapPoints (principalMap R (s i)) g₀ = g i := by
  let W := (testSpec F).obj (Opposite.op R)
  let U := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) s hs).openCover
  let m (i : Idx) := (testSpec F).map (principalMap R (s i)).op
  have hm (i j : Idx) :
      pullback.fst (U.f i) (U.f j) ≫ (g i).left = pullback.snd _ _ ≫ (g j).left := by
    let P := pullback (m i) (m j)
    let a := pullback.fst (m i) (m j)
    let b := pullback.snd (m i) (m j)
    have hp : IsPullback a.left b.left (U.f i) (U.f j) :=
      (IsPullback.of_hasPullback _ _).map (Over.forget _)
    have hAff (k : Idx) : IsAffine (U.X k) := by
      change IsAffine (Spec (CommRingCat.of (Localization.Away (s k))))
      infer_instance
    letI : IsAffine (pullback (U.f i) (U.f j)) :=
      @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine _ _ _ (U.f i) (U.f j)
        (hAff i) (hAff j) inferInstance
    let hP : IsAffine P.left := IsAffine.of_isIso hp.isoPullback.hom
    obtain ⟨S, ⟨e⟩⟩ := (essImage_algSpec (R := CommRingCat.of F)).mpr hP
    let A := algSpec.fullyFaithful (R := CommRingCat.of F)
    let i' := (A.preimage (e.hom ≫ a)).unop
    let j' := (A.preimage (e.hom ≫ b)).unop
    have hi : (testSpec F).map i'.op = e.hom ≫ a := A.map_preimage _
    have hj : (testSpec F).map j'.op = e.hom ≫ b := A.map_preimage _
    have h' : principalMap R (s i) ≫ i' = principalMap R (s j) ≫ j' := by
      apply Quiver.Hom.op_inj
      apply A.map_injective
      rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp, hi, hj, Category.assoc, Category.assoc]
      exact congrArg (e.hom ≫ ·) pullback.condition
    have he := h i j S.unop i' j' h'
    change (testSpec F).map i'.op ≫ g i = (testSpec F).map j'.op ≫ g j at he
    rw [hi, hj, Category.assoc, Category.assoc, cancel_epi] at he
    apply (cancel_epi hp.isoPullback.hom).mp
    simp only [← Category.assoc, hp.isoPullback_hom_fst, hp.isoPullback_hom_snd]
    exact congrArg Over.Hom.left he
  let f := U.glueMorphisms (fun i => (g i).left) hm
  have hf : f ≫ X.hom = W.hom := by
    apply U.hom_ext
    intro i
    rw [← Category.assoc, show U.f i ≫ f = (g i).left from U.ι_glueMorphisms _ hm i]
    exact (Over.w (g i)).trans (Over.w (m i)).symm
  refine ⟨Over.homMk f hf, fun i => ?_⟩
  apply Over.OverMorphism.ext
  exact U.ι_glueMorphisms _ hm i

end PrincipalCover

section ScalarLiftGluing

set_option maxHeartbeats 1500000

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)
  (w : Fin d → B) (q : Bˣ)
  (hw : hermitianValue Q.conjugation.anti Q.complement.val w w = q.val)
  (h2 : (2 : F) ≠ 0)
  (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
    spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))

private theorem determinant_one_column_span {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det = 1) :
    Ideal.span (Set.range (fun i => M i 0)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hM, Matrix.det_fin_two]
  exact sub_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩))

private theorem shifted_pivot {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (i : Fin 2) (hi : IsUnit (M i 0)) :
    ∃ (x : R) (a : Rˣ), a.val = M 0 0 + x * M 1 0 := by
  fin_cases i
  · exact ⟨0, hi.unit, by simpa using hi.unit_spec⟩
  · refine ⟨(1 - M 0 0) * (↑hi.unit⁻¹ : R), 1, ?_⟩
    have hv : hi.unit.val = M 1 0 := hi.unit_spec
    have hp : (↑hi.unit⁻¹ : R) * M 1 0 = 1 := by rw [← hv, hi.unit.inv_mul]
    change 1 = M 0 0 + (1 - M 0 0) * (↑hi.unit⁻¹ : R) * M 1 0
    rw [mul_assoc, hp, mul_one]
    ring

private theorem matrix_map_det_one {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det = 1) :
    (M.map f).det = 1 :=
  (f.map_det M).symm.trans (by rw [hM, map_one])

private theorem matrix_map_comp {R S T : Type*} (M : Matrix (Fin 2) (Fin 2) R)
    (f : R → S) (g : S → T) :
    (M.map f).map g = M.map (g ∘ f) := rfl

include h2 hc in
private theorem exists_scalar_matrix_lift (R : TestAlgebra F)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) :
    ∃ g : Points G.val.X R, ∀ (S : TestAlgebra F) (f : R ⟶ S) (x : S) (a : Sˣ),
      a.val = (M.val.map f.hom) 0 0 + x * (M.val.map f.hom) 1 0 →
      mapPoints f g = shiftedGaussianLift Q P L w q hw S (M.val.map f.hom) x a := by
  classical
  let s (i : Fin 2) := M.val i 0
  let A (i : Fin 2) := principalAlgebra R (s i)
  let k (i : Fin 2) := principalMap R (s i)
  have hunit (i : Fin 2) : IsUnit ((M.val.map (k i).hom) i 0) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (s i)) (s i)
  choose x a ha using fun i => shifted_pivot (M.val.map (k i).hom) i (hunit i)
  let l (i : Fin 2) := shiftedGaussianLift Q P L w q hw (A i) (M.val.map (k i).hom) (x i) (a i)
  have hl (i : Fin 2) (S : TestAlgebra F) (b : A i ⟶ S) :
      mapPoints b (l i) = shiftedGaussianLift Q P L w q hw S
        (M.val.map (k i ≫ b).hom) (b.hom (x i)) (Units.map b.hom.toMonoidHom (a i)) := by
    rw [show l i = shiftedGaussianLift Q P L w q hw (A i) (M.val.map (k i).hom) (x i) (a i) from rfl,
      shiftedGaussianLift_map, matrix_map_comp]
    rfl
  have hp (i : Fin 2) (S : TestAlgebra F) (b : A i ⟶ S) :
      (Units.map b.hom.toMonoidHom (a i)).val =
        (M.val.map (k i ≫ b).hom) 0 0 + b.hom (x i) * (M.val.map (k i ≫ b).hom) 1 0 := by
    change b.hom (a i).val = _
    rw [ha, map_add, map_mul]
    rfl
  obtain ⟨g, hg⟩ := glue_principal_points R s (determinant_one_column_span M.val M.prop) l
    (fun i j S b b' e => by
      have hj := hp j S b'
      have hl' := hl j S b'
      change k i ≫ b = k j ≫ b' at e
      rw [← e] at hj hl'
      rw [hl i S b, hl']
      exact shiftedGaussianLift_independent Q P L w q hw h2 hc S _
        (matrix_map_det_one (k i ≫ b).hom.toRingHom M.val M.prop) _ _ _ _ (hp i S b) hj)
  refine ⟨g, fun S f y b hb => ?_⟩
  let N := M.val.map f.hom
  let t (i : Fin 2) := N i 0
  apply principalPoints_injective S t
    (determinant_one_column_span N (matrix_map_det_one f.hom.toRingHom M.val M.prop))
  intro i
  let p := principalMap S (t i)
  have hu : IsUnit ((f ≫ p).hom (s i)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (t i)) (t i)
  let j := principalLift R (f ≫ p) hu
  have hj : k i ≫ j = f ≫ p := principalLift_comp R _ _
  rw [← mapPoints_comp, ← hj, mapPoints_comp, hg i, hl i _ j, hj,
    shiftedGaussianLift_map, matrix_map_comp]
  have hp' := hp i _ j
  rw [hj] at hp'
  have hb' : (Units.map p.hom.toMonoidHom b).val =
      (M.val.map (f ≫ p).hom) 0 0 + p.hom y * (M.val.map (f ≫ p).hom) 1 0 := by
    change p.hom b.val = _
    rw [hb, map_add, map_mul]
    rfl
  exact shiftedGaussianLift_independent Q P L w q hw h2 hc _ _
    (matrix_map_det_one (f ≫ p).hom.toRingHom M.val M.prop) _ _ _ _ hp' hb'

private noncomputable def scalarMatrixLift (R : TestAlgebra F)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) : Points G.val.X R :=
  (exists_scalar_matrix_lift Q P L w q hw h2 hc R M).choose

private theorem scalarMatrixLift_chart (R : TestAlgebra F)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) (x : R) (a : Rˣ)
    (ha : a.val = M.val 0 0 + x * M.val 1 0) :
    scalarMatrixLift Q P L w q hw h2 hc R M =
      shiftedGaussianLift Q P L w q hw R M.val x a := by
  have hm : M.val.map (CommAlgCat.Hom.hom (𝟙 R)) = M.val := by
    ext i j
    rfl
  have hh := (exists_scalar_matrix_lift Q P L w q hw h2 hc R M).choose_spec R (𝟙 R) x a
    (by simpa only [hm] using ha)
  change (testSpec F).map (𝟙 (Opposite.op R)) ≫ _ = _ at hh
  rw [(testSpec F).map_id, Category.id_comp, hm] at hh
  exact hh

private theorem scalarMatrixLift_map {R S : TestAlgebra F} (f : R ⟶ S)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) :
    mapPoints f (scalarMatrixLift Q P L w q hw h2 hc R M) =
      scalarMatrixLift Q P L w q hw h2 hc S (Matrix.SpecialLinearGroup.map f.hom.toRingHom M) := by
  let N := Matrix.SpecialLinearGroup.map f.hom.toRingHom M
  let t (i : Fin 2) := N.val i 0
  apply principalPoints_injective S t (determinant_one_column_span N.val N.prop)
  intro i
  let p := principalMap S (t i)
  have hu : IsUnit ((N.val.map p.hom) i 0) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (t i)) (t i)
  obtain ⟨x, a, ha⟩ := shifted_pivot (N.val.map p.hom) i hu
  rw [← mapPoints_comp]
  exact ((exists_scalar_matrix_lift Q P L w q hw h2 hc R M).choose_spec _ (f ≫ p) x a ha).trans
    ((exists_scalar_matrix_lift Q P L w q hw h2 hc S N).choose_spec _ p x a ha).symm

end ScalarLiftGluing

section ScalarLiftMultiplication

set_option maxHeartbeats 1500000

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val} (L : ShearLifts Q P c)
  (w : Fin d → B) (q : Bˣ)
  (hw : hermitianValue Q.conjugation.anti Q.complement.val w w = q.val)
  (h2 : (2 : F) ≠ 0)
  (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
    spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))

private theorem vectorMatrix_map {R S : TestAlgebra F} (f : R ⟶ S) (g : Points G.val.X R) :
    vectorMatrix Q P S (mapPoints f g) =
      (vectorMatrix Q P R g).map (tensorMap B f.hom) := by
  unfold vectorMatrix
  rw [projection_map]
  exact matrixAt_map Q R S f _

private theorem scalarPlaneBlock_map {R S : TestAlgebra F} (f : R ⟶ S)
    (M : Matrix (Fin 2) (Fin 2) R) :
    (scalarPlaneBlock (B := B) R d M).map (tensorMap B f.hom) =
      scalarPlaneBlock (B := B) S d (M.map f.hom) := by
  have h (x : R) : tensorMap B f.hom (algebraMap R (R ⊗[F] B) x) =
      algebraMap S (S ⊗[F] B) (f.hom x) := by
    change tensorMap B f.hom (x ⊗ₜ[F] (1 : B)) = f.hom x ⊗ₜ[F] (1 : B)
    simp [tensorMap]
  ext (i | i) (j | j)
  · exact h (M i j)
  · simp [scalarPlaneBlock]
  · simp [scalarPlaneBlock]
  · by_cases hij : i = j <;> simp [scalarPlaneBlock, Matrix.one_apply, hij]

private theorem principal_tensor_injective (hB : isCentralSimple F B) (R : TestAlgebra F) {Idx : Type*}
    (s : Idx → R) (hs : Ideal.span (Set.range s) = ⊤) (x y : R ⊗[F] B)
    (h : ∀ i, tensorMap B (principalMap R (s i)).hom x =
        tensorMap B (principalMap R (s i)).hom y) : x = y := by
  let : FiniteDimensional F B := hB.2.2
  let b := Module.finBasis F B
  have natural (S : TestAlgebra F) (f : R ⟶ S) (z : R ⊗[F] B) (i : Fin (Module.finrank F B)) :
      (b.baseChange S).repr (tensorMap B f.hom z) i = f.hom ((b.baseChange R).repr z i) := by
    induction z using TensorProduct.inductionOn with
    | tmul r z =>
      simp [tensorMap, Algebra.smul_def, AlgHom.commutes]
    | add z z' hz hz' =>
      simp only [map_add, Finsupp.add_apply, hz, hz']
  apply (b.baseChange R).repr.injective
  apply Finsupp.ext
  intro j
  apply Localization.algebraMap_injective_of_span_eq_top (Set.range s) hs
  funext v
  obtain ⟨i, hi⟩ := v.property
  change algebraMap R (Localization.Away v.val) _ = _
  cases v with
  | mk r hr =>
    dsimp at hi ⊢
    subst r
    let f := principalMap R (s i)
    have he := congrArg (fun z : principalAlgebra R (s i) ⊗[F] B =>
      (b.baseChange (principalAlgebra R (s i))).repr z j) (h i)
    exact (natural _ f x j).symm.trans (he.trans (natural _ f y j))

private theorem scalarMatrixLift_matrix (R : TestAlgebra F)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) :
    vectorMatrix Q P R (scalarMatrixLift Q P L w q hw h2 hc R M) =
      scalarPlaneBlock (B := B) R d M.val := by
  let s (i : Fin 2) := M.val i 0
  ext j k
  apply principal_tensor_injective hB R s (determinant_one_column_span _ M.prop)
  intro i
  let p := principalMap R (s i)
  have hu : IsUnit ((M.val.map p.hom) i 0) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (s i)) (s i)
  obtain ⟨x, a, ha⟩ := shifted_pivot (M.val.map p.hom) i hu
  have h := (exists_scalar_matrix_lift Q P L w q hw h2 hc R M).choose_spec _ p x a ha
  change mapPoints p (scalarMatrixLift Q P L w q hw h2 hc R M) = _ at h
  have he := shiftedGaussianLift_matrix Q P L w q hw hc _ (M.val.map p.hom) x a
    (matrix_map_det_one p.hom.toRingHom _ M.prop) ha
  rw [← h, vectorMatrix_map, ← scalarPlaneBlock_map] at he
  exact congrFun (congrFun he j) k

private def upperSpecialLinear {R : Type*} [CommRing R] (x : R) :
    Matrix.SpecialLinearGroup (Fin 2) R := ⟨upperScalarMatrix x, upperScalarMatrix_det x⟩

private def lowerSpecialLinear {R : Type*} [CommRing R] (x : R) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

private def diagonalSpecialLinear {R : Type*} [CommRing R] (a : Rˣ) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![a.val, 0; 0, (↑a⁻¹ : R)], by simp [Matrix.det_fin_two]⟩

@[local simp] private theorem map_upperSpecialLinear {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) :
    Matrix.SpecialLinearGroup.map f (upperSpecialLinear x) = upperSpecialLinear (f x) := by
  apply Subtype.ext
  change (upperScalarMatrix x : Matrix (Fin 2) (Fin 2) R).map f = upperScalarMatrix (f x)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperScalarMatrix]

@[local simp] private theorem map_lowerSpecialLinear {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : R) :
    Matrix.SpecialLinearGroup.map f (lowerSpecialLinear x) = lowerSpecialLinear (f x) := by
  apply Subtype.ext
  change (!![1, 0; x, 1] : Matrix (Fin 2) (Fin 2) R).map f = !![1, 0; f x, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperScalarMatrix]

@[local simp] private theorem map_diagonalSpecialLinear {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : Rˣ) :
    Matrix.SpecialLinearGroup.map f (diagonalSpecialLinear a) =
      diagonalSpecialLinear (Units.map f.toMonoidHom a) := by
  apply Subtype.ext
  change (!![a.val, 0; 0, (↑a⁻¹ : R)] : Matrix (Fin 2) (Fin 2) R).map f = !![(Units.map f.toMonoidHom a).val, 0; 0, (↑(Units.map f.toMonoidHom a)⁻¹ : S)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperScalarMatrix]

@[local simp] private theorem upperSpecialLinear_zero {R : Type*} [CommRing R] :
    upperSpecialLinear (0 : R) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperSpecialLinear, upperScalarMatrix]

@[local simp] private theorem lowerSpecialLinear_zero {R : Type*} [CommRing R] :
    lowerSpecialLinear (0 : R) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerSpecialLinear]

@[local simp] private theorem diagonalSpecialLinear_one {R : Type*} [CommRing R] :
    diagonalSpecialLinear (1 : Rˣ) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalSpecialLinear]

private theorem scalar_matrix_path (R : TestAlgebra F)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) (x : R) (a : Rˣ)
    (ha : a.val = M.val 0 0 + x * M.val 1 0) :
    ∃ (f : Polynomial R) (h₀ : (polynomialEvaluate R 0).hom f = 1)
      (h₁ : IsUnit ((polynomialEvaluate R 1).hom f))
      (N : Matrix.SpecialLinearGroup (Fin 2) (polynomialPath R f)),
      Matrix.SpecialLinearGroup.map (polynomialPathEval R f 0 (h₀.symm ▸ isUnit_one)).hom.toRingHom N = 1 ∧
      Matrix.SpecialLinearGroup.map (polynomialPathEval R f 1 h₁).hom.toRingHom N = M := by
  let A := upperScalarMatrix x * M.val
  let l := A 1 0 * (↑a⁻¹ : R)
  let r := (↑a⁻¹ : R) * A 0 1
  have hA : A.det = 1 := by
    change (upperScalarMatrix x * M.val).det = 1
    rw [Matrix.det_mul, upperScalarMatrix_det, M.prop, one_mul]
  have decomp : upperSpecialLinear (-x) * lowerSpecialLinear l *
      diagonalSpecialLinear a * upperSpecialLinear r = M := by
    apply Subtype.ext
    change upperScalarMatrix (-x) * !![1, 0; l, 1] *
      !![a.val, 0; 0, (↑a⁻¹ : R)] * !![1, r; 0, 1] = M.val
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (!![1, 0; l, 1] : Matrix (Fin 2) (Fin 2) R),
      two_by_two_gaussian A a (ha.trans (upperScalarMatrix_shift M.val x).symm) hA]
    change upperScalarMatrix (-x) * (upperScalarMatrix x * M.val) = _
    rw [← Matrix.mul_assoc, upperScalarMatrix_cancel, Matrix.one_mul]
  let f : Polynomial R := 1 + Polynomial.X * Polynomial.C (a.val - 1)
  have he (t : R) : (polynomialEvaluate R t).hom f = 1 + t * (a.val - 1) := by
    change (polynomialEvaluate R t).hom (1 + Polynomial.X * Polynomial.C (a.val - 1)) = _
    have hX : (polynomialEvaluate R t).hom (Polynomial.X : Polynomial R) = t :=
      Polynomial.eval₂_X _ _
    have hC (z : R) : (polynomialEvaluate R t).hom (Polynomial.C z) = z :=
      Polynomial.eval₂_C _ _
    rw [map_add, map_one, map_mul, hX, hC]
  have h₀ : (polynomialEvaluate R 0).hom f = 1 := by rw [he, zero_mul, add_zero]
  have h₁ : (polynomialEvaluate R 1).hom f = a.val := by rw [he, one_mul, add_comm, sub_add_cancel]
  let S := polynomialPath R f
  let p := polynomialPathMap R f
  let k := polynomialConstants R ≫ p
  let X := p.hom (Polynomial.X : polynomialAlgebra R)
  have hunit : IsUnit (p.hom f) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f
  let N := upperSpecialLinear (X * k.hom (-x)) * lowerSpecialLinear (X * k.hom l) *
    diagonalSpecialLinear hunit.unit * upperSpecialLinear (X * k.hom r)
  have heval (t : R) (hu : IsUnit ((polynomialEvaluate R t).hom f)) :
      let e := polynomialPathEval R f t hu
      let u := Units.map e.hom.toMonoidHom hunit.unit
      u.val = (polynomialEvaluate R t).hom f ∧
      Matrix.SpecialLinearGroup.map e.hom.toRingHom N =
        upperSpecialLinear (t * (-x)) * lowerSpecialLinear (t * l) *
          diagonalSpecialLinear u * upperSpecialLinear (t * r) := by
    let e := polynomialPathEval R f t hu
    have hh (z : Polynomial R) : e.hom (p.hom z) = (polynomialEvaluate R t).hom z :=
      congrArg (fun m : polynomialAlgebra R ⟶ R => m.hom z) (polynomialPathMap_eval R f t hu)
    have hX : e.hom X = t := (hh _).trans (Polynomial.eval₂_X _ _)
    have hk (z : R) : e.hom (k.hom z) = z := (hh (Polynomial.C z)).trans (Polynomial.eval₂_C _ _)
    refine ⟨?_, ?_⟩
    · change e.hom hunit.unit.val = _
      rw [hunit.unit_spec, hh]
    · simp only [N, map_mul, map_upperSpecialLinear, map_lowerSpecialLinear, map_diagonalSpecialLinear]
      change upperSpecialLinear (e.hom X * e.hom (k.hom (-x))) *
        lowerSpecialLinear (e.hom X * e.hom (k.hom l)) *
          diagonalSpecialLinear (Units.map e.hom.toMonoidHom hunit.unit) *
          upperSpecialLinear (e.hom X * e.hom (k.hom r)) = _
      rw [hX, hk, hk, hk]
  refine ⟨f, h₀, h₁.symm ▸ a.isUnit, N, ?_, ?_⟩
  · obtain ⟨hval, hN⟩ := heval 0 (h₀.symm ▸ isUnit_one)
    have hu : Units.map (polynomialPathEval R f 0 (h₀.symm ▸ isUnit_one)).hom.toMonoidHom
        hunit.unit = (1 : Rˣ) := Units.ext (hval.trans h₀)
    rw [hN]
    change upperSpecialLinear (0 * (-x)) * lowerSpecialLinear (0 * l) *
      diagonalSpecialLinear (Units.map (polynomialPathEval R f 0
        (h₀.symm ▸ isUnit_one)).hom.toMonoidHom hunit.unit) * upperSpecialLinear (0 * r) = _
    rw [hu]
    simp only [zero_mul, upperSpecialLinear_zero, lowerSpecialLinear_zero, diagonalSpecialLinear_one, one_mul]
  · obtain ⟨hval, hN⟩ := heval 1 (h₁.symm ▸ a.isUnit)
    have hu : Units.map (polynomialPathEval R f 1 (h₁.symm ▸ a.isUnit)).hom.toMonoidHom
        hunit.unit = a := Units.ext (hval.trans h₁)
    rw [hN]
    change upperSpecialLinear (1 * (-x)) * lowerSpecialLinear (1 * l) *
      diagonalSpecialLinear (Units.map (polynomialPathEval R f 1
        (h₁.symm ▸ a.isUnit)).hom.toMonoidHom hunit.unit) * upperSpecialLinear (1 * r) = _
    rw [hu]
    simpa only [one_mul] using decomp

private theorem cocharacter_at_one (R : TestAlgebra F) :
    cocharacterPoint c R 1 = 1 := by
  have h : unitPoint R 1 = 1 := by
    apply (unitEquiv R).injective
    rw [unitEquiv_unitPoint, map_one]
  rw [cocharacterPoint, h, map_one]

variable (hzero : ∀ (upper : Bool) (R : TestAlgebra F) (h : ShearAdmissible Q w q R 0 0),
  L.lift upper w q R 0 0 h = 1)

include hzero in
private theorem scalarTransvectionLift_zero (upper : Bool) (R : TestAlgebra F) :
    scalarTransvectionLift Q P L w q hw upper R 0 = 1 := by
  unfold scalarTransvectionLift
  cases upper
  · simpa only [Bool.false_eq_true, ite_false, neg_zero, map_zero] using
      hzero false R ⟨hw, by simp⟩
  · simpa only [ite_true, map_zero] using hzero true R ⟨hw, by simp⟩

include hzero in
private theorem scalarMatrixLift_gaussian (R : TestAlgebra F)
    (M : Matrix.SpecialLinearGroup (Fin 2) R) (a : Rˣ) (ha : a.val = M.val 0 0) :
    scalarMatrixLift Q P L w q hw h2 hc R M = gaussianSpinLift Q P L w q hw R M.val a := by
  have hU : upperScalarMatrix (0 : R) = 1 :=
    congrArg Subtype.val (upperSpecialLinear_zero (R := R))
  rw [scalarMatrixLift_chart Q P L w q hw h2 hc R M 0 a (by rw [zero_mul, add_zero, ha])]
  unfold shiftedGaussianLift
  rw [neg_zero, scalarTransvectionLift_zero Q P L w q hw hzero, hU, Matrix.one_mul]
  exact one_mul _

include hzero in
private theorem scalarMatrixLift_upper (R : TestAlgebra F) (x : R) :
    scalarMatrixLift Q P L w q hw h2 hc R (upperSpecialLinear x) =
      scalarTransvectionLift Q P L w q hw true R x := by
  rw [scalarMatrixLift_gaussian Q P L w q hw h2 hc hzero R _ 1 rfl]
  change scalarTransvectionLift Q P L w q hw false R (0 * (↑(1 : Rˣ)⁻¹ : R)) *
    (show Points G.val.X R from cocharacterPoint c R 1) *
    scalarTransvectionLift Q P L w q hw true R ((↑(1 : Rˣ)⁻¹ : R) * x) = _
  rw [zero_mul, inv_one, Units.val_one, one_mul, scalarTransvectionLift_zero Q P L w q hw hzero]
  have hone : (show Points G.val.X R from cocharacterPoint c R 1) = 1 := cocharacter_at_one R
  rw [hone, one_mul, one_mul]

include hzero in
private theorem scalarMatrixLift_lower (R : TestAlgebra F) (x : R) :
    scalarMatrixLift Q P L w q hw h2 hc R (lowerSpecialLinear x) =
      scalarTransvectionLift Q P L w q hw false R x := by
  rw [scalarMatrixLift_gaussian Q P L w q hw h2 hc hzero R _ 1 rfl]
  change scalarTransvectionLift Q P L w q hw false R (x * (↑(1 : Rˣ)⁻¹ : R)) *
    (show Points G.val.X R from cocharacterPoint c R 1) *
    scalarTransvectionLift Q P L w q hw true R ((↑(1 : Rˣ)⁻¹ : R) * 0) = _
  rw [mul_zero, inv_one, Units.val_one, mul_one, scalarTransvectionLift_zero Q P L w q hw hzero]
  have hone : (show Points G.val.X R from cocharacterPoint c R 1) = 1 := cocharacter_at_one R
  rw [hone, mul_one, mul_one]

include hzero in
private theorem scalarMatrixLift_diagonal (R : TestAlgebra F) (a : Rˣ) :
    scalarMatrixLift Q P L w q hw h2 hc R (diagonalSpecialLinear a) =
      cocharacterPoint c R a := by
  rw [scalarMatrixLift_gaussian Q P L w q hw h2 hc hzero R _ a rfl]
  change scalarTransvectionLift Q P L w q hw false R (0 * (↑a⁻¹ : R)) *
    (show Points G.val.X R from cocharacterPoint c R a) *
    scalarTransvectionLift Q P L w q hw true R ((↑a⁻¹ : R) * 0) = _
  rw [zero_mul, mul_zero, scalarTransvectionLift_zero Q P L w q hw hzero,
    scalarTransvectionLift_zero Q P L w q hw hzero, one_mul, mul_one]

include hzero in
private theorem scalarMatrixLift_one (R : TestAlgebra F) :
    scalarMatrixLift Q P L w q hw h2 hc R 1 = 1 := by
  rw [← diagonalSpecialLinear_one, scalarMatrixLift_diagonal Q P L w q hw h2 hc hzero]
  exact cocharacter_at_one (c := c) R

include hzero in
private theorem scalarMatrixLift_mul (R : TestAlgebra F)
    (M N : Matrix.SpecialLinearGroup (Fin 2) R) :
    scalarMatrixLift Q P L w q hw h2 hc R (M * N) =
      scalarMatrixLift Q P L w q hw h2 hc R M * scalarMatrixLift Q P L w q hw h2 hc R N := by
  have mul_map {S T : TestAlgebra F} (f : S ⟶ T) (x y : Points G.val.X S) :
      mapPoints f (x * y) = mapPoints f x * mapPoints f y :=
    (changeSpinPoints (G := G) f).map_mul x y
  let s (i : Fin 2) := M.val i 0
  apply principalPoints_injective R s (determinant_one_column_span _ M.prop)
  intro i
  let p := principalMap R (s i)
  let M' := Matrix.SpecialLinearGroup.map p.hom.toRingHom M
  let N' := Matrix.SpecialLinearGroup.map p.hom.toRingHom N
  rw [mul_map, scalarMatrixLift_map, scalarMatrixLift_map, scalarMatrixLift_map, map_mul]
  change scalarMatrixLift Q P L w q hw h2 hc _ (M' * N') =
    scalarMatrixLift Q P L w q hw h2 hc _ M' * scalarMatrixLift Q P L w q hw h2 hc _ N'
  let R' := principalAlgebra R (s i)
  have hi : IsUnit (M'.val i 0) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (s i)) (s i)
  obtain ⟨x, a, ha⟩ := shifted_pivot M'.val i hi
  obtain ⟨f, h₀, h₁, M₀, hM₀, hM₁⟩ := scalar_matrix_path R' M' x a ha
  let S := polynomialPath R' f
  let k := polynomialConstants R' ≫ polynomialPathMap R' f
  let N₀ := Matrix.SpecialLinearGroup.map k.hom.toRingHom N'
  let l := scalarMatrixLift Q P L w q hw h2 hc
  have heval (t : R') (hu : IsUnit ((polynomialEvaluate R' t).hom f)) :
      Matrix.SpecialLinearGroup.map (polynomialPathEval R' f t hu).hom.toRingHom N₀ = N' := by
    have he (z : R') : (polynomialPathEval R' f t hu).hom (k.hom z) = z :=
      (congrArg (fun m : polynomialAlgebra R' ⟶ R' => m.hom (Polynomial.C z))
        (polynomialPathMap_eval R' f t hu)).trans (Polynomial.eval₂_C _ _)
    apply Subtype.ext
    ext j k
    exact he (N'.val j k)
  have hvec : vectorMatrix Q P S (l S (M₀ * N₀)) =
      vectorMatrix Q P S (l S M₀ * l S N₀) := by
    simp only [l, vectorMatrix_mul, scalarMatrixLift_matrix, Matrix.SpecialLinearGroup.coe_mul]
    exact scalarPlaneBlock_mul (B := B) S d M₀.val N₀.val
  have evaluate (t : R') (hu : IsUnit ((polynomialEvaluate R' t).hom f))
      (Z : Matrix.SpecialLinearGroup (Fin 2) S) :
      let g := polynomialPathEval R' f t hu
      mapPoints g (l S Z) = l R' (Matrix.SpecialLinearGroup.map g.hom.toRingHom Z) :=
    scalarMatrixLift_map Q P L w q hw h2 hc _ _
  let hunit₀ : IsUnit ((polynomialEvaluate R' 0).hom f) := h₀.symm ▸ isUnit_one
  let g₀ := polynomialPathEval R' f 0 hunit₀
  have hone : mapPoints g₀ (l S (M₀ * N₀)) = mapPoints g₀ (l S M₀ * l S N₀) := by
    rw [mul_map g₀, evaluate 0 hunit₀ (M₀ * N₀), evaluate 0 hunit₀ M₀, evaluate 0 hunit₀ N₀,
      map_mul, hM₀, heval 0 hunit₀]
    have h : l R' 1 = 1 := scalarMatrixLift_one Q P L w q hw h2 hc hzero R'
    rw [one_mul, h, one_mul]
  have h := equal_spin_lifts_on_path Q P h2 R' f h₀ _ _ hvec hone
  let g₁ := polynomialPathEval R' f 1 h₁
  have h' : mapPoints g₁ (l S (M₀ * N₀)) = mapPoints g₁ (l S M₀ * l S N₀) :=
    congrArg (mapPoints g₁) h
  rw [mul_map g₁, evaluate 1 h₁ (M₀ * N₀), evaluate 1 h₁ M₀, evaluate 1 h₁ N₀,
    map_mul, hM₁, heval 1 h₁] at h'
  exact h'

end ScalarLiftMultiplication

section ScalarSubgroup

set_option maxHeartbeats 1500000

open Specs.StandardGroups (SLCoordinates GLCoordinates genericDeterminant genericMatrix
  determinantOneIdeal universalMatrix)
open private quotient_det specialLinearRepresentation Representation.convolutionIso
  from LinearAlgebraicGroups.Affine.StandardGroups

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)

private abbrev ScalarIndex := ULift.{u} (Fin 2)

private def scalarSpecialLinearEquiv (R : Type u) [CommRing R] :
    Matrix.SpecialLinearGroup ScalarIndex.{u} R ≃* Matrix.SpecialLinearGroup (Fin 2) R where
  toFun M := ⟨Matrix.reindex Equiv.ulift Equiv.ulift M.val,
    (Matrix.det_reindex_self Equiv.ulift M.val).trans M.prop⟩
  invFun M := ⟨Matrix.reindex Equiv.ulift.symm Equiv.ulift.symm M.val,
    (Matrix.det_reindex_self Equiv.ulift.symm M.val).trans M.prop⟩
  left_inv M := Subtype.ext rfl
  right_inv M := Subtype.ext rfl
  map_mul' M N := Subtype.ext ((Matrix.reindexRingEquiv R Equiv.ulift).map_mul M.val N.val)

private noncomputable def scalarCoefficient (R : TestAlgebra F) (l : B →ₗ[F] F) :
    R ⊗[F] B →ₗ[R] R :=
  ((Algebra.linearMap F R).comp l).liftBaseChange R

private theorem scalarCoefficient_tmul (R : TestAlgebra F) (l : B →ₗ[F] F) (r : R) (b : B) :
    scalarCoefficient R l (r ⊗ₜ[F] b) = r * algebraMap F R (l b) := rfl

private theorem scalarCoefficient_map {R S : TestAlgebra F} (f : R ⟶ S) (l : B →ₗ[F] F)
    (z : R ⊗[F] B) :
    f.hom (scalarCoefficient R l z) = scalarCoefficient S l (tensorMap B f.hom z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r b =>
    simp [scalarCoefficient_tmul, tensorMap, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem scalarSL_coordinates_surjective :
    Function.Surjective
      ((Ideal.Quotient.mkₐ F (determinantOneIdeal F ScalarIndex.{u})).comp
        (IsScalarTower.toAlgHom F (MvPolynomial (ScalarIndex.{u} × ScalarIndex.{u}) F)
          (GLCoordinates F ScalarIndex.{u}))) := by
  let J := ScalarIndex.{u}
  let V := MvPolynomial (J × J) F
  let A := GLCoordinates F J
  let q := Ideal.Quotient.mkₐ F (determinantOneIdeal F J)
  let D := genericDeterminant F J
  have hD : q (algebraMap V A D) = 1 := by
    have h : algebraMap V A D = (universalMatrix F J).det :=
      (IsScalarTower.toAlgHom F V A).map_det (genericMatrix F J)
    rw [h]
    exact quotient_det
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (S := A) D z
  refine ⟨p, ?_⟩
  have he := congrArg q hp
  rw [map_mul, map_pow, hD, one_pow, mul_one] at he
  exact he.symm

private theorem scalarSL_universal_entry (i j : ScalarIndex.{u}) :
    let R := CommAlgCat.of F (SLCoordinates F ScalarIndex.{u})
    let S := StandardGroups.specialLinearGroup F ScalarIndex.{u}
    let e := StandardGroups.specialLinearGroupPointsIso F ScalarIndex.{u}
    (e.hom.app R (show Points S.val.X R from 𝟙 S.val.X)).val i j =
      Ideal.Quotient.mkₐ F (determinantOneIdeal F ScalarIndex.{u})
        (universalMatrix F ScalarIndex.{u} i j) := by
  let J := ScalarIndex.{u}
  let C := SLCoordinates F J
  let R := CommAlgCat.of F C
  let : HopfAlgebra F C := StandardGroups.specialLinearHopf F J
  let A := CommHopfAlgCat.of F C
  let e := hopfSpecPointIso A
  let id := WithConv.toConv (AlgHom.id F C)
  let S := StandardGroups.specialLinearGroup F J
  let eS := StandardGroups.specialLinearGroupPointsIso F J
  let p : Points S.val.X R := 𝟙 S.val.X
  have h : e.hom.app R id = p := by
    apply Over.OverMorphism.ext
    exact Spec.map_id (CommRingCat.of C)
  have hInv : e.inv.app R (e.hom.app R id) = id :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.hom_inv_id_app R)) id
  let e' := Representation.convolutionIso (@specialLinearRepresentation F _ J _ _)
  change (eS.hom.app R p).val i j = _
  calc
    _ = (eS.hom.app R (e.hom.app R id)).val i j :=
      congrArg (fun y : Points S.val.X R => (eS.hom.app R y).val i j) h.symm
    _ = _ := by
      change (e'.hom.app R (e.inv.app R (e.hom.app R id))).val i j = _
      rw [hInv]
      rfl

private theorem scalar_subgroup_closed_immersion
    (j : (StandardGroups.specialLinearGroup F ScalarIndex.{u}).val ⟶ G.val)
    (h : ∀ (R : TestAlgebra F) (g : Points (StandardGroups.specialLinearGroup F ScalarIndex.{u}).val.X R),
      vectorMatrix Q P R (g ≫ j.hom.hom) =
        scalarPlaneBlock (B := B) R d
          (scalarSpecialLinearEquiv R ((StandardGroups.specialLinearGroupPointsIso F
            ScalarIndex.{u}).hom.app R g)).val) :
    IsClosedImmersion j.hom.hom.left := by
  classical
  let J := ScalarIndex.{u}
  let SL := StandardGroups.specialLinearGroup F J
  let V := MvPolynomial (J × J) F
  let C := CommAlgCat.of F (SLCoordinates F J)
  let A := (algSpec.fullyFaithful (R := CommRingCat.of F))
  obtain ⟨T, ⟨iso⟩⟩ := essImage_algSpec.mpr G.property.1
  let g := iso.hom
  let p : Points SL.val.X C := 𝟙 SL.val.X
  let a : T.unop ⟶ C := (A.preimage (p ≫ j.hom.hom ≫ iso.inv)).unop
  have ha : (testSpec F).map a.op ≫ g = p ≫ j.hom.hom := by
    change (algSpec (CommRingCat.of F)).map (A.preimage _) ≫ iso.hom = _
    rw [A.map_preimage]
    simp
  have hp : mapPoints a g = p ≫ j.hom.hom := ha
  let : FiniteDimensional F B := hB.2.2
  let b := Module.finBasis F B
  have hb : ∃ i, b.repr (1 : B) i ≠ 0 := by
    by_contra! hb
    exact (one_ne_zero : (1 : B) ≠ 0) (b.repr.injective (Finsupp.ext fun i => by simpa using hb i))
  obtain ⟨i, hi⟩ := hb
  let l : B →ₗ[F] F := (b.repr (1 : B) i)⁻¹ • b.coord i
  have hl : l 1 = 1 := by
    change (b.repr (1 : B) i)⁻¹ * b.coord i 1 = 1
    rw [Module.Basis.coord_apply, inv_mul_cancel₀ hi]
  let x (v : J × J) : T.unop :=
    scalarCoefficient T.unop l (vectorMatrix Q P T.unop g (Sum.inl v.1.down) (Sum.inl v.2.down))
  let q := (Ideal.Quotient.mkₐ F (determinantOneIdeal F J)).comp
    (IsScalarTower.toAlgHom F V (GLCoordinates F J))
  have hx (v : J × J) : a.hom (x v) = q (MvPolynomial.X v) := by
    rw [show x v = _ from rfl, scalarCoefficient_map]
    have h' := h C p
    rw [← hp, vectorMatrix_map] at h'
    have hv := congrFun (congrFun h' (Sum.inl v.1.down)) (Sum.inl v.2.down)
    change tensorMap B a.hom (vectorMatrix Q P T.unop g (Sum.inl v.1.down) (Sum.inl v.2.down)) =
      ((StandardGroups.specialLinearGroupPointsIso F J).hom.app C p).val v.1 v.2 ⊗ₜ[F] (1 : B) at hv
    rw [hv, scalarCoefficient_tmul, hl, map_one, mul_one]
    exact scalarSL_universal_entry v.1 v.2
  have hq : a.hom.comp (MvPolynomial.aeval x) = q := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, hx]
  have hsurj : Function.Surjective a.hom := by
    intro z
    obtain ⟨v, rfl⟩ := scalarSL_coordinates_surjective (F := F) z
    exact ⟨MvPolynomial.aeval x v, congrArg (fun h : V →ₐ[F] C => h v) hq⟩
  have hj : (testSpec F).map a.op ≫ iso.hom = j.hom.hom :=
    ha.trans (Category.id_comp j.hom.hom)
  have hclosed : IsClosedImmersion ((testSpec F).map a.op).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom a.hom.toRingHom) hsurj
  letI : IsIso iso.hom.left := (Over.forget _).map_isIso iso.hom
  have hclosedIso : IsClosedImmersion iso.hom.left := inferInstance
  rw [← hj, Over.comp_left]
  exact @IsClosedImmersion.comp _ _ _ _ _ hclosed hclosedIso

private theorem scalar_hyperbolic_sl2 (h2 : (2 : F) ≠ 0) (hd : degree F B = 2) (hd₀ : 0 < d)
    {c : Cocharacter G.val} (L : ShearLifts Q P c)
    (hzero : ∀ upper w q R h, L.lift upper w q R 0 0 h = 1)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t)) :
    ScalarHyperbolicSL2 Q P c := by
  let h := complementSkewPairing Q
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd₀
  obtain ⟨w, hw⟩ := exists_nonzero_self_pairing h h2 hB hd Q.canonical (show ∃ v : Fin d → B, v ≠ 0 from
    ⟨1, one_ne_zero⟩)
  let q := Units.mk0 (h.value w w) hw
  have hq : hermitianValue Q.conjugation.anti Q.complement.val w w = q.val := rfl
  let l := scalarMatrixLift Q P L w q hq h2 hc
  let S := StandardGroups.specialLinearGroup F ScalarIndex.{u}
  let e := StandardGroups.specialLinearGroupPointsIso F ScalarIndex.{u}
  let τ : Specs.StandardGroups.specialLinearPoints F ScalarIndex.{u} ⟶ (groupPointsFunctor F).obj G.val :=
    { app := fun R => GrpCat.ofHom
        { toFun := fun M => l R (scalarSpecialLinearEquiv R M)
          map_one' := by
            rw [map_one]
            exact scalarMatrixLift_one Q P L w q hq h2 hc (fun b R hb => hzero b w q R hb) R
          map_mul' := fun M N => by
            rw [map_mul]
            exact scalarMatrixLift_mul Q P L w q hq h2 hc (fun b R hb => hzero b w q R hb) R _ _ }
      naturality := by
        intro R R' f
        apply GrpCat.ext
        intro M
        change l R' (Matrix.SpecialLinearGroup.map f.hom.toRingHom (scalarSpecialLinearEquiv R M)) =
          mapPoints f (l R (scalarSpecialLinearEquiv R M))
        exact (scalarMatrixLift_map Q P L w q hq h2 hc f (scalarSpecialLinearEquiv R M)).symm }
  obtain ⟨j, hj⟩ := (groupHomComparison F S.val G.val S.property.1).surjective (e.hom ≫ τ)
  have hj' (R : TestAlgebra F) (g : Points S.val.X R) :
      g ≫ j.hom.hom = l R (scalarSpecialLinearEquiv R (e.hom.app R g)) :=
    DFunLike.congr_fun (congrArg GrpCat.Hom.hom (NatTrans.congr_app hj R)) g
  have hmatrix (R : TestAlgebra F) (g : Points S.val.X R) :
      vectorMatrix Q P R (g ≫ j.hom.hom) =
        scalarPlaneBlock (B := B) R d (scalarSpecialLinearEquiv R (e.hom.app R g)).val := by
    rw [hj']
    exact scalarMatrixLift_matrix Q P L w q hq h2 hc R _
  let point (R : TestAlgebra F) (M : Matrix.SpecialLinearGroup (Fin 2) R) : Points S.val.X R :=
    e.inv.app R ((scalarSpecialLinearEquiv R).symm M)
  have hpoint (R : TestAlgebra F) (M : Matrix.SpecialLinearGroup (Fin 2) R) :
      scalarSpecialLinearEquiv R (e.hom.app R (point R M)) = M := by
    have h := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.inv_hom_id_app R))
      ((scalarSpecialLinearEquiv R).symm M)
    change e.hom.app R (point R M) = (scalarSpecialLinearEquiv R).symm M at h
    exact (congrArg (scalarSpecialLinearEquiv R) h).trans ((scalarSpecialLinearEquiv R).apply_symm_apply M)
  refine ⟨S, e, j, scalar_subgroup_closed_immersion Q P j hmatrix, hmatrix, ?_, ?_⟩
  · intro R t
    let M := diagonalSpecialLinear t
    refine ⟨hc R t, point R M, congrArg Subtype.val (hpoint R M), ?_⟩
    rw [hj', hpoint]
    exact scalarMatrixLift_diagonal Q P L w q hq h2 hc (fun b R hb => hzero b w q R hb) R t
  · intro R x
    let M := upperSpecialLinear x
    let N := lowerSpecialLinear x
    refine ⟨point R M, point R N, congrArg Subtype.val (hpoint R M), ?_,
      congrArg Subtype.val (hpoint R N), ?_⟩
    · rw [hj', hpoint]
      change HasLimit c (scalarMatrixLift Q P L w q hq h2 hc R (upperSpecialLinear x)) 1
      rw [scalarMatrixLift_upper Q P L w q hq h2 hc (fun b R hb => hzero b w q R hb)]
      exact L.contracting true w q R 0 _ _
    · rw [hj', hpoint]
      change HasLimit (oppositeCocharacter c)
        (scalarMatrixLift Q P L w q hq h2 hc R (lowerSpecialLinear x)) 1
      rw [scalarMatrixLift_lower Q P L w q hq h2 hc (fun b R hb => hzero b w q R hb)]
      exact L.contracting false w q R 0 _ _

end ScalarSubgroup


open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (PointsIn)
open LinearAlgebraicGroups.CocharacterDynamics (existsLimitDecomposition)
open private reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private testPointSections
  from LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration
open private rationalSourceIso
  from LinearAlgebraicGroups.Relative.RationalDensity

section LocalGeneration

set_option maxHeartbeats 1500000

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} {hB : isCentralSimple F B} {d : ℕ}
  (Q : QuaternionHyperbolicPresentation D hB d) (P : SpinModel G D)
  {c : Cocharacter G.val}

private theorem map_test_subgroup (S : ClosedSubgroup G.val) :
    (SubgroupSections S ((testSpec F).obj (Opposite.op (groundAlgebra F)))).map
      (testPointSections G.val).toMonoidHom = SubgroupSections S (𝟙_ (SchemeOver F)) := by
  let e : Points G.val.X (groundAlgebra F) ≃* ((𝟙_ (SchemeOver F)) ⟶ G.val.X) :=
    testPointSections G.val
  ext g
  constructor
  · rintro ⟨x, ⟨y, hy⟩, hg⟩
    change Points S.group.X (groundAlgebra F) at y
    change y ≫ S.inclusion.hom.hom = x at hy
    change e x = g at hg
    refine ⟨testPointSections S.group y, ?_⟩
    change ((rationalSourceIso F).hom ≫ y) ≫ S.inclusion.hom.hom = g
    exact (Category.assoc _ _ _).trans ((congrArg ((rationalSourceIso F).hom ≫ ·) hy).trans hg)
  · rintro ⟨y, hy⟩
    change (𝟙_ (SchemeOver F)) ⟶ S.group.X at y
    change y ≫ S.inclusion.hom.hom = g at hy
    refine ⟨e.symm g, ⟨(testPointSections S.group).symm y, ?_⟩, e.apply_symm_apply g⟩
    change ((rationalSourceIso F).inv ≫ y) ≫ S.inclusion.hom.hom =
      (rationalSourceIso F).inv ≫ g
    exact (Category.assoc _ _ _).trans (congrArg ((rationalSourceIso F).inv ≫ ·) hy)

private theorem radicals_eq_top_of_levi [Infinite F] (hG : IsAbsolutelyAlmostSimple G)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c))
    (h : ∀ g : Points G.val.X (groundAlgebra F), Centralizes c g → g ∈ rationalRadicals U V) :
    rationalRadicals U V = ⊤ := by
  let T := 𝟙_ (SchemeOver F)
  let e : Points G.val.X (groundAlgebra F) ≃* (T ⟶ G.val.X) :=
    testPointSections G.val
  let H := rationalRadicals U V
  have hmap : H.map e.toMonoidHom = SubgroupSections U.contracting T ⊔ SubgroupSections V.contracting T := by
    change (SubgroupSections U.contracting _ ⊔ SubgroupSections V.contracting _).map e.toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (map_test_subgroup U.contracting) (map_test_subgroup V.contracting)
  have hZ : SubgroupSections U.centralizer T ≤ H.map e.toMonoidHom := by
    intro g hg
    obtain ⟨y, hy⟩ := hg
    change T ⟶ U.centralizer.group.X at y
    change y ≫ U.centralizer.inclusion.hom.hom = g at hy
    have hg' : Centralizes c (e.symm g) := by
      apply (U.centralizer_points _ _).mpr
      refine ⟨(testPointSections U.centralizer.group).symm y, ?_⟩
      change ((rationalSourceIso F).inv ≫ y) ≫ U.centralizer.inclusion.hom.hom =
        (rationalSourceIso F).inv ≫ g
      exact (Category.assoc _ _ _).trans (congrArg ((rationalSourceIso F).inv ≫ ·) hy)
    exact ⟨e.symm g, h _ hg', e.apply_symm_apply g⟩
  have ht := LinearAlgebraicGroups.Arithmetic.RelativeRayGeneration.twoRadicals_sup_centralizer
    (reductive_of_semisimple G hG.1) U V
  change (_ ⊔ _ : Subgroup (T ⟶ G.val.X)) = ⊤ at ht
  rw [← hmap, sup_eq_left.mpr hZ] at ht
  apply top_unique
  intro g hg
  have hh : e g ∈ H.map e.toMonoidHom := ht.symm ▸ Subgroup.mem_top _
  obtain ⟨x, hx, he⟩ := hh
  exact (e.injective he) ▸ hx

private theorem radicals_eq_top [Infinite F] (hG : IsAbsolutelyAlmostSimple G)
    (h2 : (2 : F) ≠ 0) (hd : degree F B = 2) (hd₀ : 0 < d) (L : ShearLifts Q P c)
    (hc : ∀ (R : TestAlgebra F) (t : Rˣ),
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t))
    (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
    (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R))
    (he : ∀ R x, (e R x).val.1 = x.val.2)
    (hn : ∀ t : (CommAlgCat.of F F ⊗[F] B)ˣ,
      (N (CommAlgCat.of F F) t : F) = reducedNorm hB (Algebra.TensorProduct.lid F B t.val))
    (hwords : NormalizedLiftedScaleWords Q P L N e)
    (U : LimitDecomposition c) (V : LimitDecomposition (oppositeCocharacter c)) :
    rationalRadicals U V = ⊤ :=
  radicals_eq_top_of_levi hG U V fun g hg => by
    obtain ⟨x, hx, t, ht⟩ := remove_perpendicular_action Q P h2 hd L hc U V g hg
    let z : spinScalePreimage P Q (groundAlgebra F) := ⟨(x⁻¹ * g, t), ht⟩
    have hz : z.val.1 ∈ rationalRadicals U V :=
      spin_scales_mem_radicals Q P h2 hd hd₀ L N e he hn hwords U V z
    change x⁻¹ * g ∈ rationalRadicals U V at hz
    simpa only [mul_inv_cancel_left] using (rationalRadicals U V).mul_mem hx hz

set_option maxHeartbeats 1200000 in
private theorem local_quaternion_generation [Infinite F] [TopologicalSpace F]
    [FiniteDimensional F K] [IsGalois F K]
    (hG : IsAbsolutelyAlmostSimple G) (hi : 4 ≤ Fintype.card I)
    (h2 : (2 : F) ≠ 0) (hd : degree F B = 2) (hd₀ : 0 < d)
    :
    LocalQuaternionGeneration Q P := by
  classical
  let : FiniteDimensional F B := hB.2.2
  let basis : Module.Basis (ULift.{u} (Fin (Module.finrank F B))) F B :=
    (Module.finBasis F B).reindex Equiv.ulift.symm
  obtain ⟨_, N, e, hN, he, hnatural, hk, _⟩ := QuaternionSpinScaleCover.spinScaleCover P hi hB hd d Q basis
  have hscalar (R : TestAlgebra F) (t : Rˣ) :
      N R (scalarParameter R t) = t ^ 2 := by
    obtain ⟨N₀, hN₀, hs⟩ := QuaternionSpinScaleCover.quaternionNormOnUnits hB hd basis R
    have hm : N R (scalarParameter R t) = N₀ (scalarParameter R t) :=
      Units.ext ((hN R _).trans (hN₀ _).symm)
    exact hm.trans (hs t)
  obtain ⟨c, hc⟩ := scalar_spin_cocharacter Q P N e hscalar he hnatural
  have hc' (R : TestAlgebra F) (t : Rˣ) :
      spinVectorProjection P R (cocharacterPoint c R t) = quaternionScale Q R (scalarParameter R t) := by
    rw [hc]
    exact scalarSpinLift_projection Q P N e hscalar he R t
  obtain ⟨L, hzero⟩ := contracting_shear_lifts Q P h2 c hc'
  have hwords := normalized_lifted_scale_words Q P L hd basis N hN e he hnatural h2 QuaternionSpinScaleCover.normalizedScaleFamilies
  let R := groundAlgebra F
  have hground (t : (R ⊗[F] B)ˣ) :
      (N R t : F) = reducedNorm hB (Algebra.TensorProduct.lid F B t.val) :=
    (hN R t).trans (normAt_ground basis t.val)
  refine ⟨c, L, scalar_cocharacter_noncentral Q P L h2 hd hd₀ hc', scalar_hyperbolic_sl2 Q P h2 hd hd₀ L hzero hc',
    liftedInterchange_formula Q P L, ⟨N, e, ⟨_, inferInstance, basis, hN⟩, he, hnatural, hk, hground,
      spin_scale_lifts_iff Q P N e he hground, hwords⟩,
    ⟨existsLimitDecomposition G c, existsLimitDecomposition G (oppositeCocharacter c)⟩, ?_⟩
  intro U V i
  let H := rationalRadicals U V
  have hall : H = ⊤ := radicals_eq_top Q P hG h2 hd hd₀ L hc' N e he hground hwords U V
  change (∀ g : Points G.val.X R, Centralizes c g → _) ∧
    (∀ x : spinScalePreimage P Q R, (show PointsIn i F from x.val.1) ∈
      closure {g : PointsIn i F | (show Points G.val.X R from g) ∈ H}) ∧
    Dense {g : PointsIn i F | (show Points G.val.X R from g) ∈ H}
  refine ⟨fun g hg => remove_perpendicular_action Q P h2 hd L hc' U V g hg, ?_, ?_⟩
  · intro x
    exact subset_closure (spin_scales_mem_radicals Q P h2 hd hd₀ L N e he hground hwords U V x)
  · have hset : {g : PointsIn i F | (show Points G.val.X R from g) ∈ H} = Set.univ := by
      rw [hall]
      exact Set.eq_univ_of_forall fun g => Subgroup.mem_top (show Points G.val.X R from g)
    rw [hset]
    exact dense_univ

end LocalGeneration

private theorem nonarchimedean_local_infinite (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] : Infinite F := by
  let v := ValuativeRel.valuation F
  obtain ⟨x, hx, hx₁⟩ := Valuation.IsNontrivial.exists_lt_one (v := v)
  have hx₀ : 0 < v x := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hx)
  apply Infinite.of_injective (fun n : ℕ => x ^ n)
  intro m n h
  apply pow_right_injective₀ hx₀ (ne_of_lt hx₁)
  simpa only [map_pow] using congrArg v h

/-- The two opposite shears preserve the skew-Hermitian form. -/
theorem shearIsometries : ShearIsometries.{u} := shear_isometries

/-- The three-shear interchange with its ordered factors. -/
theorem oppositeShearWord : OppositeShearWord.{u} := opposite_shear_word

/-- Parameters from the fixed quadratic field of a nonsingular line. -/
theorem fixedLineParameters : FixedLineParameters.{u} := fixed_line_parameters

/-- Line rotations generate the isometries of the perpendicular form. -/
theorem perpendicularRotationGeneration : PerpendicularRotationGeneration.{u} :=
  perpendicular_rotation_generation

/-- A noncentral cocharacter gives an adapted hyperbolic quaternion basis. -/
theorem quaternionPresentationAtIsotropy : QuaternionPresentationAtIsotropy.{u} :=
  quaternion_presentation_at_isotropy NontrialitarianSpinModels.quaternionSpinIsotropy

/-- Local generation for odd-characteristic quaternion spin models at finite and real places. -/
theorem localGeneration : LocalGeneration.{u} := by
  constructor
  · intro F K I B _ _ _ _ _ _ _ _ _ _ _ _ ρ G D P hG hi h₂ hB hd d hd₀ Q
    let : Infinite F := nonarchimedean_local_infinite F
    exact local_quaternion_generation Q P hG hi h₂ hd hd₀
  · intro F K I B _ _ realModel _ _ _ _ _ _ _ _ _ ρ G D P hG hi hB hd d hd₀ Q
    let : Infinite F := Infinite.of_injective realModel.symm realModel.symm.injective
    have h₂ : (2 : F) ≠ 0 := by
      intro he
      exact (two_ne_zero : (2 : ℝ) ≠ 0)
        (by simpa only [map_ofNat, map_zero] using congrArg realModel he)
    exact local_quaternion_generation Q P hG hi h₂ hd hd₀

end LinearAlgebraicGroups.Arithmetic.QuaternionSpinOddCharacteristic
