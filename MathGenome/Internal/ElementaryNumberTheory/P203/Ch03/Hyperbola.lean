import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Hyperbola
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

namespace P203.Hyperbola

open Finset P203Specs

/-- Expanding a truncated rectangle by rows. The outer cutoff may exceed N. -/
lemma sum_rectangle_filter {R : Type*} [CommRing R] (f g : ℕ → R)
    (A B N : ℕ) (hNB : N ≤ B) :
    (∑ p ∈ (Ioc 0 A ×ˢ Ioc 0 B).filter (fun p => p.1 * p.2 ≤ N),
      f p.1 * g p.2) =
      ∑ u ∈ Ioc 0 A, f u * ∑ v ∈ Ioc 0 (N / u), g v := by
  classical
  rw [sum_filter, sum_product]
  apply sum_congr rfl
  intro u hu
  have hu0 : 0 < u := (mem_Ioc.mp hu).1
  simp only [sum_ite, sum_const_zero, add_zero, ← mul_sum]
  congr 1
  apply sum_congr
  · ext v
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hv0, _⟩, h⟩
      exact ⟨hv0, (Nat.le_div_iff_mul_le hu0).mpr (by simpa [mul_comm] using h)⟩
    · rintro ⟨hv0, h⟩
      have hprod := (Nat.le_div_iff_mul_le hu0).mp h
      have hvN : v ≤ N := by nlinarith
      exact ⟨⟨hv0, hvN.trans hNB⟩, by simpa [mul_comm] using hprod⟩
  · intros; rfl

/-- Enlarging the bounding square does not change its positive factor pairs. -/
lemma bounded_pairs (N M : ℕ) (hNM : N ≤ M) :
    (Ioc 0 M ×ˢ Ioc 0 M).filter (fun p => p.1 * p.2 ≤ N) =
    (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N) := by
  ext ⟨u,v⟩
  simp only [mem_filter, mem_product, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hu, _⟩, ⟨hv, _⟩⟩, h⟩
    exact ⟨⟨⟨hu, by nlinarith⟩, ⟨hv, by nlinarith⟩⟩, h⟩
  · rintro ⟨⟨⟨hu, huN⟩, ⟨hv, hvN⟩⟩, h⟩
    exact ⟨⟨⟨hu, huN.trans hNM⟩, ⟨hv, hvN.trans hNM⟩⟩, h⟩

/-- The finite factor-pair identity over an arbitrary commutative ring. -/
lemma integer_identity {R : Type*} [CommRing R] (f g : ArithmeticFunction R)
    (N U V : ℕ) (hl : U * V ≤ N) (hr : N < (U+1)*(V+1)) :
    (∑ n ∈ Ioc 0 N, (f*g) n) =
      (∑ u ∈ Ioc 0 U, f u * ∑ v ∈ Ioc 0 (N/u), g v) +
      (∑ v ∈ Ioc 0 V, g v * ∑ u ∈ Ioc 0 (N/v), f u) -
      (∑ u ∈ Ioc 0 U, f u) * (∑ v ∈ Ioc 0 V, g v) := by
  classical
  let M := max N (max U V)
  have hNM : N ≤ M := le_max_left _ _
  have hUM : U ≤ M := (le_max_left U V).trans (le_max_right _ _)
  have hVM : V ≤ M := (le_max_right U V).trans (le_max_right _ _)
  let A := (Ioc 0 U ×ˢ Ioc 0 M).filter (fun p => p.1*p.2 ≤ N)
  let B := (Ioc 0 M ×ˢ Ioc 0 V).filter (fun p => p.1*p.2 ≤ N)
  have hunion : A ∪ B = (Ioc 0 M ×ˢ Ioc 0 M).filter (fun p => p.1*p.2 ≤ N) := by
    ext ⟨u,v⟩
    simp only [A, B, mem_union, mem_filter, mem_product, mem_Ioc]
    constructor
    · rintro (⟨⟨⟨hu, huU⟩, hv⟩, h⟩ | ⟨⟨hu, ⟨hv, hvV⟩⟩, h⟩)
      · exact ⟨⟨⟨hu, huU.trans hUM⟩, hv⟩, h⟩
      · exact ⟨⟨hu, ⟨hv, hvV.trans hVM⟩⟩, h⟩
    · rintro ⟨⟨hu, hv⟩, h⟩
      have hor : u ≤ U ∨ v ≤ V := by
        by_contra hh
        push Not at hh
        have := Nat.mul_le_mul (show U+1 ≤ u by omega) (show V+1 ≤ v by omega)
        omega
      rcases hor with hU | hV
      · exact Or.inl ⟨⟨⟨hu.1, hU⟩, hv⟩, h⟩
      · exact Or.inr ⟨⟨hu, ⟨hv.1, hV⟩⟩, h⟩
  have hinter : A ∩ B = Ioc 0 U ×ˢ Ioc 0 V := by
    ext ⟨u,v⟩
    simp only [A, B, mem_inter, mem_filter, mem_product, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hu, _⟩, _⟩, ⟨⟨_, hv⟩, _⟩⟩
      exact ⟨hu, hv⟩
    · rintro ⟨hu, hv⟩
      have hprod : u*v ≤ N := (Nat.mul_le_mul hu.2 hv.2).trans hl
      exact ⟨⟨⟨hu, ⟨hv.1, hv.2.trans hVM⟩⟩, hprod⟩,
        ⟨⟨⟨hu.1, hu.2.trans hUM⟩, hv⟩, hprod⟩⟩
  have hA := sum_rectangle_filter (fun n => f n) (fun n => g n) U M N hNM
  have hB : (∑ p ∈ B, f p.1 * g p.2) =
      ∑ v ∈ Ioc 0 V, g v * ∑ u ∈ Ioc 0 (N/v), f u := by
    rw [show (∑ p ∈ B, f p.1 * g p.2) =
      ∑ p ∈ (Ioc 0 V ×ˢ Ioc 0 M).filter (fun p => p.1*p.2 ≤ N),
        g p.1 * f p.2 from ?_]
    · exact sum_rectangle_filter _ _ V M N hNM
    · apply sum_nbij Prod.swap
      · intro p hp
        simpa [B, mul_comm, and_comm, and_left_comm, and_assoc] using hp
      · intro p _ q _ h
        exact Prod.swap_injective h
      · intro p hp
        refine ⟨p.swap, ?_, by simp⟩
        simpa [B, mul_comm, and_comm, and_left_comm, and_assoc] using hp
      · intro p _
        exact mul_comm _ _
  have h := sum_union_inter (s₁ := A) (s₂ := B) (f := fun p => f p.1 * g p.2)
  rw [hunion, bounded_pairs N M hNM, hinter, sum_product, ← sum_mul_sum] at h
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter]
  rw [hA, hB] at h
  exact eq_sub_of_add_eq h

/-- The source's real-cutoff identity, with no positivity assumption on either cut. -/
theorem identity : P203Specs.Hyperbola.Identity := by
  intro R _ f g x U V hl hr
  have hx : 0 ≤ x := (mul_nonneg (Nat.cast_nonneg U) (Nat.cast_nonneg V)).trans hl
  have hlN : U * V ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx).mpr (by exact_mod_cast hl)
  have hrN : ⌊x⌋₊ < (U+1)*(V+1) := (Nat.floor_lt hx).mpr (by exact_mod_cast hr)
  have h := integer_identity (zeroExtend f) (zeroExtend g) ⌊x⌋₊ U V hlN hrN
  unfold P203Specs.Hyperbola.Formula summatory
  rw [Convolution.productBridge]
  simpa only [Nat.floor_natCast, Nat.floor_div_natCast] using h

/-- Both cutoff inequalities hold for floor(sqrt x), even when x=0. -/
lemma sqrt_cutoff (x : ℝ) (hx : 0 ≤ x) :
    (⌊Real.sqrt x⌋₊ : ℝ) * (⌊Real.sqrt x⌋₊ : ℝ) ≤ x ∧
    x < ((⌊Real.sqrt x⌋₊ : ℝ) + 1) * ((⌊Real.sqrt x⌋₊ : ℝ) + 1) := by
  have hs := Real.sq_sqrt hx
  have hlow := mul_self_le_mul_self (Nat.cast_nonneg (α := ℝ) ⌊Real.sqrt x⌋₊)
    (Nat.floor_le (Real.sqrt_nonneg x))
  have hhigh := mul_self_lt_mul_self (Real.sqrt_nonneg x)
    (Nat.lt_floor_add_one (Real.sqrt x))
  constructor <;> nlinarith

/-- The symmetric specialization of Theorem 3.5 for every nonnegative real x. -/
theorem symmetricIdentity : P203Specs.Hyperbola.SymmetricIdentity := by
  intro R _ f g x hx
  exact identity R f g x _ _ (sqrt_cutoff x hx).1 (sqrt_cutoff x hx).2

end P203.Hyperbola
