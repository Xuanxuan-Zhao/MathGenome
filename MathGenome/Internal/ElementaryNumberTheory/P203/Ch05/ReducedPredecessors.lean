import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.ReducedPredecessors
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticContinuedFractions
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

namespace P203
open Polynomial
open private minpoly_quadratic_equation from MathGenome.Internal.ElementaryNumberTheory.P203.Ch05.QuadraticContinuedFractions

/-- A monic rational quadratic equation for an irrational real identifies both
its degree and its intrinsic conjugate. -/
theorem quadratic_of_monic_equation (u : ℝ) (b c : ℚ) (hu : Irrational u)
    (he : u ^ 2 + (b : ℝ) * u + (c : ℝ) = 0) :
    P203Specs.QuadraticIrrational u ∧ P203Specs.quadraticConjugate u = -(b : ℝ) - u := by
  let p : Polynomial ℚ := C 1 * X ^ 2 + C b * X + C c
  have hd : p.natDegree = 2 := natDegree_quadratic one_ne_zero
  have hm : p.Monic := by
    change p.leadingCoeff = 1
    exact leadingCoeff_quadratic one_ne_zero
  have hp : aeval u p = 0 := by simpa [p] using he
  have ha : IsAlgebraic ℚ u := ⟨p, hm.ne_zero, hp⟩
  have hlow : 2 ≤ (minpoly ℚ u).natDegree :=
    (minpoly.two_le_natDegree_iff ha.isIntegral).mpr hu
  have hhigh : (minpoly ℚ u).natDegree ≤ 2 := by
    rw [← hd]
    exact natDegree_le_of_dvd (minpoly.dvd ℚ u hp) hm.ne_zero
  have hdegree := le_antisymm hhigh hlow
  have hpoly : p = minpoly ℚ u := by
    apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ha.isIntegral) hm
    · exact minpoly.dvd ℚ u hp
    · rw [hd, hdegree]
  refine ⟨⟨ha, hdegree⟩, ?_⟩
  change -((minpoly ℚ u).coeff 1 : ℝ) - u = _
  rw [← hpoly]
  simp [p]

/-- Sum and product of a quadratic real and its intrinsic conjugate. -/
theorem quadratic_sum_product (x : ℝ) (hx : P203Specs.QuadraticIrrational x) :
    x + P203Specs.quadraticConjugate x = -((minpoly ℚ x).coeff 1 : ℝ) ∧
    x * P203Specs.quadraticConjugate x = ((minpoly ℚ x).coeff 0 : ℝ) := by
  have he := minpoly_quadratic_equation x hx
  change x + (-((minpoly ℚ x).coeff 1 : ℝ) - x) = _ ∧
    x * (-((minpoly ℚ x).coeff 1 : ℝ) - x) = _
  constructor <;> nlinarith

/-- Rational translation preserves degree two and commutes with conjugation. -/
theorem quadratic_add_rat (x : ℝ) (hx : P203Specs.QuadraticIrrational x) (a : ℚ) :
    P203Specs.QuadraticIrrational (x + (a : ℝ)) ∧
      P203Specs.quadraticConjugate (x + (a : ℝ)) = P203Specs.quadraticConjugate x + (a : ℝ) := by
  let b := (minpoly ℚ x).coeff 1
  let c := (minpoly ℚ x).coeff 0
  have he := minpoly_quadratic_equation x hx
  have h := quadratic_of_monic_equation (x + (a : ℝ))
    (b - 2 * a) (c - b * a + a ^ 2) ((quadratic_is_irrational x hx).add_ratCast a) (by
      push_cast
      dsimp [b, c]
      nlinarith [he])
  refine ⟨h.1, ?_⟩
  rw [h.2]
  change -((b - 2 * a : ℚ) : ℝ) - (x + (a : ℝ)) =
    (-((minpoly ℚ x).coeff 1 : ℝ) - x) + (a : ℝ)
  dsimp [b]
  push_cast
  ring

/-- Nonzero inversion preserves degree two and commutes with conjugation. -/
theorem quadratic_inv (x : ℝ) (hx : P203Specs.QuadraticIrrational x) :
    P203Specs.QuadraticIrrational (1 / x) ∧
      P203Specs.quadraticConjugate (1 / x) = 1 / P203Specs.quadraticConjugate x := by
  let b := (minpoly ℚ x).coeff 1
  let c := (minpoly ℚ x).coeff 0
  have hx0 := (quadratic_is_irrational x hx).ne_zero
  have hc : c ≠ 0 := minpoly.coeff_zero_ne_zero hx.1.isIntegral hx0
  have hcr : (c : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hc
  have he := minpoly_quadratic_equation x hx
  have hi : Irrational (1 / x) := by
    simpa only [one_div] using (quadratic_is_irrational x hx).inv
  have h := quadratic_of_monic_equation (1 / x) (b / c) (1 / c) hi (by
    push_cast
    field_simp
    dsimp [b, c] at *
    nlinarith [he])
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have hs := quadratic_sum_product x hx
  have hconj0 := (quadratic_other_root x hx).1.ne_zero
  push_cast
  dsimp [b, c] at *
  field_simp
  linear_combination -((minpoly ℚ x).coeff 0 : ℝ) * hs.1 -
    ((minpoly ℚ x).coeff 1 : ℝ) * hs.2

/-- The algebraic conjugate formula for a quotient, before imposing reducedness. -/
theorem quadratic_step (x : ℝ) (hx : P203Specs.QuadraticIrrational x) :
    P203Specs.QuadraticIrrational (P203Specs.continuedFractionStep x) ∧
      P203Specs.quadraticConjugate (P203Specs.continuedFractionStep x) =
        1 / (P203Specs.quadraticConjugate x - (⌊x⌋ : ℝ)) := by
  have hs := quadratic_add_rat x hx (-((⌊x⌋ : ℤ) : ℚ))
  simp only [Rat.cast_neg, Rat.cast_intCast, ← sub_eq_add_neg] at hs
  have ht := quadratic_inv _ hs.1
  change P203Specs.QuadraticIrrational (1 / (x - (⌊x⌋ : ℝ))) ∧ _
  refine ⟨ht.1, ?_⟩
  change P203Specs.quadraticConjugate (1 / (x - (⌊x⌋ : ℝ))) = _
  rw [ht.2, hs.2]

/-- Reduced complete quotients remain reduced under the canonical quotient map. -/
theorem reduced_step : P203Specs.ReducedStep := by
  intro y hy
  obtain ⟨hq, hy1, hylo, hyhi⟩ := hy
  have hi := quadratic_is_irrational y hq
  have ha : 1 ≤ ⌊y⌋ := Int.le_floor.mpr (by simpa using hy1.le)
  have har : (1 : ℝ) ≤ (⌊y⌋ : ℝ) := by exact_mod_cast ha
  have hfrac : 0 < y - (⌊y⌋ : ℝ) :=
    sub_pos.mpr (lt_of_le_of_ne (Int.floor_le y) (Ne.symm (hi.ne_int ⌊y⌋)))
  have hfrac1 : y - (⌊y⌋ : ℝ) < 1 := by
    linarith [Int.lt_floor_add_one y]
  have ht1 : 1 < P203Specs.continuedFractionStep y := by
    change 1 < 1 / (y - (⌊y⌋ : ℝ))
    rw [one_div]
    exact (one_lt_inv₀ hfrac).mpr hfrac1
  have hd : P203Specs.quadraticConjugate y - (⌊y⌋ : ℝ) < 0 := by linarith
  have hd1 : P203Specs.quadraticConjugate y - (⌊y⌋ : ℝ) < -1 := by linarith
  have htl : -1 < 1 / (P203Specs.quadraticConjugate y - (⌊y⌋ : ℝ)) := by
    apply (lt_div_iff_of_neg hd).mpr
    linarith
  have hth : 1 / (P203Specs.quadraticConjugate y - (⌊y⌋ : ℝ)) < 0 :=
    div_neg_of_pos_of_neg zero_lt_one hd
  have ht := quadratic_step y hq
  exact ⟨ha, ⟨ht.1, ht1, ht.2.symm ▸ htl, ht.2.symm ▸ hth⟩, ht.2⟩

/-- Every reduced quadratic has the displayed, unique reduced predecessor. -/
theorem reduced_predecessor : P203Specs.ReducedPredecessor := by
  intro z hz
  dsimp only
  let t : ℝ := -1 / P203Specs.quadraticConjugate z
  let a : ℤ := ⌊t⌋
  let y : ℝ := (a : ℝ) + 1 / z
  change 1 ≤ a ∧ ⌊y⌋ = a ∧ P203Specs.ReducedQuadratic y ∧ P203Specs.continuedFractionStep y = z ∧
    P203Specs.quadraticConjugate y = (a : ℝ) + 1 / P203Specs.quadraticConjugate z ∧
    ∀ w : ℝ, P203Specs.ReducedQuadratic w → P203Specs.continuedFractionStep w = z → w = y
  obtain ⟨hq, hz1, hzlo, hzhi⟩ := hz
  have ht1 : 1 < t := by
    dsimp [t]
    apply (lt_div_iff_of_neg hzhi).mpr
    linarith
  have htI : Irrational t := by
    simpa [t, neg_div, one_div] using (quadratic_other_root z hq).1.inv.neg
  have ha : 1 ≤ a := Int.le_floor.mpr (by simpa using ht1.le)
  have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hat : (a : ℝ) < t :=
    lt_of_le_of_ne (Int.floor_le t) (Ne.symm (htI.ne_int a))
  have hta : t < (a : ℝ) + 1 := Int.lt_floor_add_one t
  have hiz : 0 < 1 / z := one_div_pos.mpr (lt_trans zero_lt_one hz1)
  have hiz1 : 1 / z < 1 := by
    rw [div_lt_one (lt_trans zero_lt_one hz1)]
    exact hz1
  have hy1 : 1 < y := by dsimp [y]; linarith
  have hfloor : ⌊y⌋ = a := Int.floor_eq_iff.mpr (by dsimp [y]; constructor <;> linarith)
  have hiq := quadratic_inv z hq
  have hya := quadratic_add_rat (1 / z) hiq.1 (a : ℚ)
  simp only [Rat.cast_intCast] at hya
  have hyq : P203Specs.QuadraticIrrational y := by
    simpa only [y, add_comm] using hya.1
  have hyconj : P203Specs.quadraticConjugate y = (a : ℝ) + 1 / P203Specs.quadraticConjugate z := by
    dsimp only [y]
    rw [add_comm (a : ℝ), hya.2, hiq.2]
    simp only [add_comm]
  have hneg : 1 / P203Specs.quadraticConjugate z = -t := by dsimp [t]; ring
  have hyred : P203Specs.ReducedQuadratic y := by
    refine ⟨hyq, hy1, ?_, ?_⟩ <;> rw [hyconj, hneg] <;> linarith
  have hstep : P203Specs.continuedFractionStep y = z := by
    change 1 / (y - (⌊y⌋ : ℝ)) = z
    rw [hfloor]
    dsimp only [y]
    rw [add_sub_cancel_left, one_div_one_div]
  refine ⟨ha, hfloor, hyred, hstep, hyconj, ?_⟩
  intro w hw hwT
  have hwq := hw.1
  have hwconj := (quadratic_step w hwq).2
  rw [hwT] at hwconj
  have hwr : w - (⌊w⌋ : ℝ) = 1 / z := by
    have h := congrArg (fun v : ℝ => 1 / v) hwT
    change 1 / (1 / (w - (⌊w⌋ : ℝ))) = 1 / z at h
    simpa only [one_div_one_div] using h
  have hwcr : P203Specs.quadraticConjugate w - (⌊w⌋ : ℝ) = 1 / P203Specs.quadraticConjugate z := by
    have h := congrArg (fun v : ℝ => 1 / v) hwconj
    simpa only [one_div_one_div] using h.symm
  have hdigit : ⌊w⌋ = a := by
    have heq : ⌊t⌋ = ⌊w⌋ := Int.floor_eq_iff.mpr (by
      rw [hneg] at hwcr
      constructor <;> linarith [hw.2.2.1, hw.2.2.2])
    exact heq.symm
  rw [hdigit] at hwr
  dsimp [y]
  linarith

end P203
