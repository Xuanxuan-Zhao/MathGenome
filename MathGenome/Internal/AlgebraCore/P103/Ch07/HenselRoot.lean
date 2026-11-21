import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.HenselRoot
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

universe u
namespace P103.Ch07.HenselRoot
open Polynomial

variable {R : Type u} [CommRing R]

/-- A map on `I` which improves congruences by one power has a unique fixed point. -/
theorem adic_fixedPoint (I : Ideal R) [IsAdicComplete I R] (F : R → R)
    (hFI : ∀ x ∈ I, F x ∈ I)
    (hF : ∀ (n : ℕ) (x : R), x ∈ I → ∀ y : R, y ∈ I →
      x - y ∈ I^n → F x - F y ∈ I^(n+1)) :
    ∃! t : R, t ∈ I ∧ F t = t := by
  let s : ℕ → R := fun n => F^[n] 0
  have hs : ∀ n, s (n+1) = F (s n) := fun n => Function.iterate_succ_apply' F n 0
  have hmem : ∀ n, s n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ n ih => rw [hs]; exact hFI _ ih
  have hstep : ∀ n, s n - s (n+1) ∈ I^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hs, hs]; exact hF n _ (hmem n) _ (hmem (n+1)) ih
  have hc : ∀ {m n}, m ≤ n → s m - s n ∈ I^m := by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := Ideal.pow_le_pow_right (Nat.le_add_right m k) (hstep (m+k))
      simpa only [sub_add_sub_cancel, Nat.add_assoc] using (I^m).add_mem ih hh
  have heq : ∀ n, (I^n • (⊤ : Submodule R R)) = (I^n : Ideal R) := by
    intro n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
  obtain ⟨t, ht⟩ := IsPrecomplete.prec' (I := I) s (by
    intro m n hmn
    rw [heq, SModEq.sub_mem]
    exact hc hmn)
  have htmem : t ∈ I := by
    have hh := ht 1
    rw [heq, pow_one, SModEq.sub_mem] at hh
    have := I.sub_mem (hmem 1) hh
    simpa using this
  have hfix : F t = t := by
    apply (IsHausdorff.eq_iff_smodEq (I := I)).2
    intro n
    rw [heq, SModEq.sub_mem]
    have hn : s n - t ∈ I^n := by simpa only [heq, SModEq.sub_mem] using ht n
    have hnext : F (s n) - F t ∈ I^n :=
      Ideal.pow_le_pow_right (Nat.le_succ n) (hF n _ (hmem n) _ htmem hn)
    have hn' : s (n+1) - t ∈ I^n :=
      Ideal.pow_le_pow_right (Nat.le_succ n) (by
        simpa only [heq, SModEq.sub_mem] using ht (n+1))
    rw [hs] at hn'
    convert (I^n).sub_mem hn' hnext using 1; ring
  refine ⟨t, ⟨htmem, hfix⟩, ?_⟩
  rintro v ⟨hv, hfv⟩
  apply (IsHausdorff.eq_iff_smodEq (I := I)).2
  have hall : ∀ n, v - t ∈ I^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simpa only [hfv, hfix] using hF n v hv t htmem ih
  intro n
  rw [heq, SModEq.sub_mem]
  exact hall n

/-- The quadratic part of the polynomial is contracting on `I`. -/
theorem quadratic_contraction (I : Ideal R) (h : R[X]) (n : ℕ)
    (s : R) (hs : s ∈ I) (t : R) (ht : t ∈ I) (hst : s - t ∈ I^n) :
    s^2 * h.eval s - t^2 * h.eval t ∈ I^(n+1) := by
  obtain ⟨k, hk⟩ := sub_dvd_eval_sub s t h
  have hq : (s+t)*h.eval s + t^2*k ∈ I :=
    I.add_mem (I.mul_mem_right _ (I.add_mem hs ht))
      (I.mul_mem_right _ (by simpa only [pow_two] using I.mul_mem_left t ht))
  rw [pow_succ]
  convert Ideal.mul_mem_mul hst hq using 1; linear_combination t^2 * hk

/-- Taylor expansion with a scalar displacement; this identity does not cancel `d`. -/
theorem scaled_expansion (f : R[X]) (a c : R)
    (hc : f.eval a = (f.derivative.eval a)^2 * c) :
    ∃ h : R[X], ∀ t : R,
      f.eval (a + f.derivative.eval a * t) =
        (f.derivative.eval a)^2 * (c + t + t^2 * h.eval t) := by
  let d := f.derivative.eval a
  obtain ⟨q, hq⟩ := exists_mul_sq_add_linear_part_eq_eval_add
    (f.map (C : R →+* R[X])) (C a) (C d * X)
  rw [derivative_map] at hq
  simp only [eval_map_apply] at hq
  rw [eval_map] at hq
  change q * (C d * X)^2 + C d * (C d * X) + C (f.eval a) =
    f.comp (C a + C d * X) at hq
  refine ⟨q, ?_⟩
  intro t
  have hh := congrArg (fun p : R[X] => p.eval t) hq
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_comp, hc] at hh
  dsimp [d] at hh
  linear_combination -hh

/-- Solving the normalized equation used in the lifting argument. -/
theorem quadratic_fixedPoint (I : Ideal R) [IsAdicComplete I R]
    (c : R) (hc : c ∈ I) (h : R[X]) :
    ∃! t : R, t ∈ I ∧ c + t + t^2 * h.eval t = 0 := by
  let F : R → R := fun t => -c - t^2 * h.eval t
  have hFI : ∀ t ∈ I, F t ∈ I := by
    intro t ht
    exact I.sub_mem (I.neg_mem hc)
      (I.mul_mem_right _ (by simpa only [pow_two] using I.mul_mem_left t ht))
  have hF : ∀ (n : ℕ) (s : R), s ∈ I → ∀ t : R, t ∈ I →
      s-t ∈ I^n → F s - F t ∈ I^(n+1) := by
    intro n s hs t ht hst
    have hh := (I^(n+1)).neg_mem (quadratic_contraction I h n s hs t ht hst)
    convert hh using 1; dsimp [F]; ring
  have iff_fix (t : R) : F t = t ↔ c + t + t^2 * h.eval t = 0 := by
    dsimp [F]
    constructor <;> intro ht <;> linear_combination -ht
  obtain ⟨t, ht, hu⟩ := adic_fixedPoint I F hFI hF
  refine ⟨t, ⟨ht.1, (iff_fix t).1 ht.2⟩, ?_⟩
  rintro s ⟨hs, hse⟩
  exact hu s ⟨hs, (iff_fix s).2 hse⟩

theorem root_exists (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a : R)
    (hc : ∃ c ∈ I, f.eval a = (f.derivative.eval a)^2 * c) :
    ∃ b : R, (∃ t ∈ I, b = a + f.derivative.eval a * t) ∧ f.eval b = 0 := by
  obtain ⟨c, hcI, hc⟩ := hc
  obtain ⟨h, he⟩ := scaled_expansion f a c hc
  obtain ⟨t, ⟨htI, ht⟩, -⟩ := quadratic_fixedPoint I c hcI h
  refine ⟨a + f.derivative.eval a * t, ⟨t, htI, rfl⟩, ?_⟩
  rw [he, ht, mul_zero]

theorem root_unique (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a : R)
    (hc : ∃ c ∈ I, f.eval a = (f.derivative.eval a)^2 * c)
    (hd : Function.Injective (fun x : R => f.derivative.eval a * x)) :
    ∃! b : R, (∃ t ∈ I, b = a + f.derivative.eval a * t) ∧ f.eval b = 0 := by
  obtain ⟨c, hcI, hc⟩ := hc
  obtain ⟨h, he⟩ := scaled_expansion f a c hc
  obtain ⟨t, ⟨htI, ht⟩, hu⟩ := quadratic_fixedPoint I c hcI h
  refine ⟨a + f.derivative.eval a * t, ⟨⟨t, htI, rfl⟩, ?_⟩, ?_⟩
  · rw [he, ht, mul_zero]
  · rintro b ⟨⟨s, hsI, rfl⟩, hb⟩
    have hcan : Function.Injective (fun x : R => (f.derivative.eval a)^2 * x) := by
      intro x y hxy
      apply hd
      apply hd
      simpa only [pow_two, mul_assoc] using hxy
    have hs : c + s + s^2 * h.eval s = 0 := by
      apply hcan
      dsimp only
      rw [← he, hb, mul_zero]
    rw [hu s ⟨hsI, hs⟩]

theorem zero_derivative (R : Type u) [CommRing R] (I : Ideal R) (f : R[X]) (a : R)
    (hd : f.derivative.eval a = 0)
    (hc : ∃ c ∈ I, f.eval a = (f.derivative.eval a)^2 * c) :
    f.eval a = 0 ∧
      {b : R | ∃ t ∈ I, b = a + f.derivative.eval a * t} = {a} ∧
      ∃! b : R, (∃ t ∈ I, b = a + f.derivative.eval a * t) ∧ f.eval b = 0 := by
  obtain ⟨c, -, hc⟩ := hc
  have ha : f.eval a = 0 := by simpa only [hd, zero_pow (by decide : 2 ≠ 0), zero_mul] using hc
  have hcoset (b : R) : (∃ t ∈ I, b = a + f.derivative.eval a * t) ↔ b = a := by
    simp only [hd, zero_mul, add_zero]
    exact ⟨fun ⟨_, _, hb⟩ => hb, fun hb => ⟨0, I.zero_mem, hb⟩⟩
  refine ⟨ha, Set.ext (fun b => hcoset b), a, ⟨(hcoset a).2 rfl, ha⟩, ?_⟩
  intro b hb
  exact (hcoset b).1 hb.1

/-- Multiplication by a unit does not change the ideal coset. -/
theorem unit_coset (I : Ideal R) (u : Rˣ) (a b : R) :
    (∃ t ∈ I, b = a + (u:R)*t) ↔ b-a ∈ I := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa only [add_sub_cancel_left] using I.mul_mem_left (u:R) ht
  · intro hb
    refine ⟨(↑u⁻¹:R)*(b-a), I.mul_mem_left _ hb, ?_⟩
    rw [Units.mul_inv_cancel_left]
    ring

theorem simple_root_lift (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (f : R[X]) (x : IsLocalRing.ResidueField R)
    (hx : (f.map (IsLocalRing.residue R)).eval x = 0)
    (hd : ((f.map (IsLocalRing.residue R)).derivative).eval x ≠ 0) :
    ∃! b : R, f.eval b = 0 ∧ IsLocalRing.residue R b = x := by
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [derivative_map, eval_map_apply] at hx hd
  have haI : f.eval a ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.residue_eq_zero_iff _).1 hx
  have hdU : IsUnit (f.derivative.eval a) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hd
  obtain ⟨u, hu⟩ := hdU
  have hc : ∃ c ∈ IsLocalRing.maximalIdeal R, f.eval a = (f.derivative.eval a)^2*c := by
    refine ⟨(↑u⁻¹:R)^2 * f.eval a, (IsLocalRing.maximalIdeal R).mul_mem_left _ haI, ?_⟩
    rw [← hu]
    calc
      f.eval a = ((u:R)*(↑u⁻¹:R))^2 * f.eval a := by simp
      _ = (u:R)^2 * ((↑u⁻¹:R)^2 * f.eval a) := by ring
  have hclass (b : R) :
      (∃ t ∈ IsLocalRing.maximalIdeal R, b = a + f.derivative.eval a * t) ↔
        IsLocalRing.residue R b = IsLocalRing.residue R a := by
    rw [← hu, unit_coset, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
  obtain ⟨b, hb, huniq⟩ := root_unique R (IsLocalRing.maximalIdeal R) f a hc
    (IsUnit.mul_right_injective ⟨u, hu⟩)
  refine ⟨b, ⟨hb.2, (hclass b).1 hb.1⟩, ?_⟩
  rintro y ⟨hy, hyres⟩
  exact huniq y ⟨(hclass y).2 hyres, hy⟩

end P103.Ch07.HenselRoot

