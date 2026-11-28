import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.PresentationSymmetries
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerreCrossCommutators
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

noncomputable section

namespace LieNotes.Quantum.SerreCrossCommutators

open Specs.LieNotes.Quantum.Presentation
open Specs.LieNotes.Quantum.PresentationSymmetries (InvertsCartan)
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)
open Specs.LieNotes.Quantum.SerreCrossCommutators
open LieNotes.Quantum.PresentationSymmetries

universe u v

private theorem unitPowerRecurrence {A : Type*} [CommRing A] (q : Aˣ) (n : ℤ) :
    (↑(q ^ (n + 2)) : A) - (↑q + ↑q⁻¹) * ↑(q ^ (n + 1)) + ↑(q ^ n) = 0 := by
  simp only [show n + 2 = n + 1 + 1 by omega, zpow_add, zpow_one, Units.val_mul]
  calc
    _ = (↑(q ^ n) : A) * (1 - ↑q⁻¹ * ↑q) := by ring
    _ = 0 := by rw [Units.inv_mul, sub_self, mul_zero]

private def weightDifference {A : Type*} [CommRing A] {T : Type*}
    [AddCommGroup T] [Module A T] (q : Aˣ) (x y : T) (n : ℤ) : T :=
  (↑(q ^ n) : A) • x - (↑(q⁻¹ ^ n) : A) • y

private theorem weightDifferenceRecurrence {A : Type*} [CommRing A] {T : Type*}
    [AddCommGroup T] [Module A T] (q : Aˣ) (x y : T) (n : ℤ) :
    weightDifference q x y (n + 2) -
      (↑q + ↑q⁻¹ : A) • weightDifference q x y (n + 1) +
      weightDifference q x y n = 0 := by
  calc
    _ = ((↑(q ^ (n + 2)) : A) - (↑q + ↑q⁻¹) * ↑(q ^ (n + 1)) + ↑(q ^ n)) • x -
        ((↑(q⁻¹ ^ (n + 2)) : A) - (↑q⁻¹ + ↑q) * ↑(q⁻¹ ^ (n + 1)) + ↑(q⁻¹ ^ n)) • y := by
          simp only [weightDifference, add_comm (↑q⁻¹ : A) ↑q, smul_sub, smul_smul,
            sub_smul, add_smul]
          abel
    _ = 0 := by
      have hi := unitPowerRecurrence q⁻¹ n
      simp only [inv_inv] at hi
      rw [unitPowerRecurrence, hi, zero_smul, zero_smul, sub_self]

section Commutator

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

private def commutator {B : Type*} [Ring B] (a b : B) : B :=
  a * b - b * a

private theorem commutator_mul {B : Type*} [Ring B] (a b f : B) :
    commutator (a * b) f = a * commutator b f + commutator a f * b := by
  simp only [commutator, mul_sub, sub_mul, mul_assoc]
  abel

private theorem commutator_serre {B : Type*} [Ring B] [Algebra A B] (q : Aˣ) (x y f : B) :
    commutator (serrePolynomial q x y) f =
      commutator (x * x * y) f - (↑q + ↑q⁻¹ : A) • commutator (x * y * x) f +
      commutator (y * (x * x)) f := by
  simp only [serrePolynomial, pow_two, commutator, sub_mul, add_mul, mul_sub, mul_add,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]
  abel

/-- A recurrence for translates of each basic commutator coefficient suffices
for the Serre commutators. -/
private theorem crossCommutators_of_recurrence (C : Cartan A T)
    (hc : InvertsCartan C) (d : Root → ℤ → T)
    (hd : ∀ l, d l 0 = C.D l)
    (hs : ∀ r l n, (C.tau r).symm (d l n) = d l (n - cartanMatrix l r))
    (hr : ∀ l n, d l (n + 2) - (↑C.q + ↑C.q⁻¹ : A) • d l (n + 1) + d l n = 0) :
    CrossCommutators C := by
  let c : A := ↑C.q + ↑C.q⁻¹
  have hshift (r l : Root) (n : ℤ) (b : B₀ C) :
      E₀ C r * (cartan₀ C (d l n) * b) =
        cartan₀ C (d l (n - cartanMatrix l r)) * (E₀ C r * b) := by
    rw [← mul_assoc, (Presentation.basic_relations C).eCartan, hs, mul_assoc]
  have hshift' (r l : Root) (n : ℤ) :
      E₀ C r * cartan₀ C (d l n) =
        cartan₀ C (d l (n - cartanMatrix l r)) * E₀ C r := by
    rw [(Presentation.basic_relations C).eCartan, hs]
  have hm (r l : Root) :
      commutator (E₀ C r) (F₀ C l) = if r = l then cartan₀ C (d l 0) else 0 := by
    rw [commutator, (Presentation.basic_relations C).comm]
    by_cases h : r = l
    · subst r
      simp [mixed, hd]
    · simp [mixed, h]
  intro i j hij l
  have hji := Ne.symm hij
  have pos : Commute (serrePolynomial C.q (E₀ C i) (E₀ C j)) (F₀ C l) := by
    apply sub_eq_zero.mp
    change commutator (serrePolynomial C.q (E₀ C i) (E₀ C j)) (F₀ C l) = 0
    have hl : l = i ∨ l = j := by
      have hi := i.isLt
      have hj := j.isLt
      have hl := l.isLt
      have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      by_cases h : l.val = i.val
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by omega))
    rcases hl with h | h
    · subst l
      have h₁ : d i 0 + d i (-2) - c • d i (-1) = 0 := by
        simpa [c, sub_add_eq_add_sub, add_comm] using hr i (-2)
      have h₂ : d i 1 + d i (-1) - c • d i 0 = 0 := by
        simpa [c, sub_add_eq_add_sub, add_comm] using hr i (-1)
      calc
        _ = cartan₀ C (d i 0 + d i (-2) - c • d i (-1)) * (E₀ C i * E₀ C j) +
            cartan₀ C (d i 1 + d i (-1) - c • d i 0) * (E₀ C j * E₀ C i) := by
          simp only [c, commutator_serre, commutator_mul, hm, hij, hji, ite_true,
            ite_false, mul_zero, zero_mul, add_zero, zero_add, smul_add, mul_add, add_mul,
            mul_assoc, hshift, hshift', cartanMatrix, map_sub, map_add, map_smul, sub_mul,
            Algebra.smul_mul_assoc]
          norm_num
          abel
        _ = 0 := by simp [h₁, h₂]
    · subst l
      have hh : d j 2 - c • d j 1 + d j 0 = 0 := by simpa [c] using hr j 0
      calc
        _ = cartan₀ C (d j 2 - c • d j 1 + d j 0) * (E₀ C i * E₀ C i) := by
          simp only [c, commutator_serre, commutator_mul, hm, hij, hji, ite_true, ite_false,
            mul_zero, zero_mul, add_zero, zero_add, mul_assoc, hshift, hshift', cartanMatrix,
            map_sub, map_add, map_smul, sub_mul, add_mul, Algebra.smul_mul_assoc]
          norm_num
        _ = 0 := by simp [hh]
  refine ⟨pos, ?_⟩
  have h := congrArg (omega₀ hc) pos.eq
  simpa only [commute_iff_eq, serrePolynomial, map_mul, map_pow, map_sub, map_smul, map_add,
    omega₀_E, omega₀_F] using h

end Commutator

section Generic

variable {k : Type u} [Field k] [CharZero k]

theorem generic_crossCommutators (q : kˣ) (hq : (q : k)^2 ≠ 1) :
    CrossCommutators (generic q hq) := by
  let denomInv : k := (↑q - ↑q⁻¹)⁻¹
  let d (l : Root) := weightDifference q
    (denomInv • (AddMonoidAlgebra.single (coordinate l) 1 : Laurent k))
    (denomInv • (AddMonoidAlgebra.single (-coordinate l) 1 : Laurent k))
  refine crossCommutators_of_recurrence (generic q hq) (generic_invertsCartan q hq) d ?_ ?_ ?_
  · intro l
    change d l 0 = genericD q l
    simp [d, weightDifference, genericD, denomInv, smul_sub, laurentUnit]
  · intro r l n
    change laurentScale q⁻¹ r (d l n) = d l (n - cartanMatrix l r)
    simp only [d, weightDifference, map_sub, map_smul, laurentScale_single,
      Presentation.pairing_neg, Presentation.pairing_coordinate, smul_smul]
    congr 1
    · rw [sub_eq_add_neg, zpow_add, ← inv_zpow', Units.val_mul]
      congr 1
      ring
    · rw [sub_eq_add_neg, zpow_add, Units.val_mul]
      congr 1
      ring
  · intro l n
    exact weightDifferenceRecurrence q _ _ n

end Generic

theorem indeterminate_crossCommutators (k : Type u) [Field k] [CharZero k] :
    CrossCommutators (indeterminate k) :=
  generic_crossCommutators (rationalQ k) (rationalQ_sq_ne k)

section Formal

open Presentation (cartanTruncate_map exponentialUnit_val exponentialUnit_int
  exponential_difference_mul_sinhRatio map_sinhRatio)
open Truncations (A cartanTruncate expH truncate)

/-- The recurrence can be checked after clearing the denominator in the domain
of power series, before applying any truncation. -/
private theorem sinhRatioRecurrence {S : Type u} [CommRing S] [IsDomain S]
    [CharZero S] [Algebra ℚ S] (a : S) (n : ℤ) :
    sinhRatio (a + ((n + 2 : ℤ) : S)) -
        (expH (1 : S) + expH (-1 : S)) * sinhRatio (a + ((n + 1 : ℤ) : S)) +
      sinhRatio (a + (n : S)) = 0 := by
  let q := exponentialUnit (1 : S)
  let delta := expH (1 : S) - expH (-1 : S)
  have hq : (q : PowerSeries S) = expH (1 : S) := exponentialUnit_val _
  have hqi : (↑q⁻¹ : PowerSeries S) = expH (-1 : S) := by
    simpa only [Int.cast_neg, Int.cast_one, zpow_neg_one, q, exponentialUnit_val] using
      (congrArg Units.val (exponentialUnit_int (S := S) (-1))).symm
  have hdelta : delta ≠ 0 := by
    intro h
    have h₁ := congrArg (PowerSeries.coeff 1) h
    norm_num [delta, Truncations.coeff_expH] at h₁
  have hexp (b : S) (m : ℤ) :
      expH (b + (m : S)) = (↑(q ^ m) : PowerSeries S) * expH b := by
    rw [Truncations.expH_add, ← exponentialUnit_val (m : S), exponentialUnit_int, mul_comm]
  have hdiff (m : ℤ) :
      delta * sinhRatio (a + (m : S)) = weightDifference q (expH a) (expH (-a)) m := by
    rw [exponential_difference_mul_sinhRatio, neg_add, ← Int.cast_neg, hexp, hexp]
    simp only [weightDifference, smul_eq_mul, inv_zpow']
  apply (mul_eq_zero.mp ?_).resolve_left hdelta
  rw [mul_add, mul_sub, mul_left_comm delta, hdiff, hdiff, hdiff, ← hq, ← hqi]
  exact weightDifferenceRecurrence q (expH a) (expH (-a)) n

private theorem cartanTruncate_exp_int (k : Type u) [Field k] [CharZero k]
    (N : ℕ) (n : ℤ) :
    cartanTruncate (R := k) Root N (expH (n : PolynomialCartan k)) =
      MvPolynomial.C (↑(truncatedQ k N ^ n) : A k N) := by
  rw [← map_intCast (MvPolynomial.C : k →+* PolynomialCartan k) n,
    ← Truncations.map_expH MvPolynomial.C, Truncations.cartanTruncate_scalar]
  congr 1
  rw [← exponentialUnit_val (n : k), exponentialUnit_int]
  exact congrArg Units.val (map_zpow
    (Units.map (truncate (R := k) N).toRingHom.toMonoidHom) (exponentialUnit (1 : k)) n)

theorem truncated_crossCommutators (k : Type u) [Field k] [CharZero k]
    (N : ℕ) (_hN : 1 ≤ N) : CrossCommutators (truncated k N) := by
  let tr := cartanTruncate (R := k) Root N
  let d (l : Root) (n : ℤ) := tr (sinhRatio (MvPolynomial.X l + (n : PolynomialCartan k)))
  refine crossCommutators_of_recurrence (truncated k N) (truncated_invertsCartan k N) d ?_ ?_ ?_
  · intro l
    change d l 0 = truncatedD k N l
    simp [d, tr, truncatedD]
  · intro r l n
    let s := (translation fun m => (cartanMatrix m r : k)).symm
    let t := ((truncated k N).tau r).symm
    have hcomp (m : Root) : t.toAlgHom (MvPolynomial.X m) =
        MvPolynomial.map (algebraMap k (A k N)) (s.toAlgHom (MvPolynomial.X m)) := by
      change (translation fun m => (cartanMatrix m r : A k N)).symm (MvPolynomial.X m) = _
      simp [s, translation_symm_X]
    have harg : s (MvPolynomial.X l + (n : PolynomialCartan k)) =
        MvPolynomial.X l + ((n - cartanMatrix l r : ℤ) : PolynomialCartan k) := by
      simp only [s, map_add, translation_symm_X, map_intCast, Int.cast_sub]
      ring
    change t.toAlgHom (tr (sinhRatio (MvPolynomial.X l + (n : PolynomialCartan k)))) = _
    rw [cartanTruncate_map N s.toAlgHom t.toAlgHom hcomp, map_sinhRatio]
    exact congrArg (fun x => tr (sinhRatio x)) harg
  · intro l n
    have hpos : tr (expH (1 : PolynomialCartan k)) =
        MvPolynomial.C (↑(truncatedQ k N) : A k N) := by
      simpa only [Int.cast_one, zpow_one] using cartanTruncate_exp_int k N 1
    have hneg : tr (expH (-1 : PolynomialCartan k)) =
        MvPolynomial.C (↑(truncatedQ k N)⁻¹ : A k N) := by
      simpa only [Int.cast_neg, Int.cast_one, zpow_neg_one] using cartanTruncate_exp_int k N (-1)
    have h := congrArg tr (sinhRatioRecurrence (MvPolynomial.X l : PolynomialCartan k) n)
    simp only [map_add, map_sub, map_mul, map_zero, hpos, hneg] at h
    change d l (n + 2) - (↑(truncatedQ k N) + ↑(truncatedQ k N)⁻¹ : A k N) •
      d l (n + 1) + d l n = 0
    simpa only [d, Algebra.smul_def, map_add, MvPolynomial.algebraMap_eq] using h

end Formal

end LieNotes.Quantum.SerreCrossCommutators
