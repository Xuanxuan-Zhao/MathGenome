import MathGenome.Internal.Specs.D07.Ch13.AdditiveExponentCyclicity
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Additive exponent and cyclicity for any field of cardinality `p ^ n`.
The ring characteristic equals the additive exponent. For finite abelian
groups cyclicity is equivalent to equality of exponent and cardinality;
here that equality is `p = p ^ n`, which holds precisely for `n = 1`.
-/

universe u

namespace D07.Ch13.AdditiveExponentCyclicity

theorem characteristic_of_cardinality
    (F : Type u) [Field F] [Finite F] (p n : ℕ)
    (hp : p.Prime) (_hn : 1 ≤ n) (hcard : Nat.card F = p ^ n) : CharP F p := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  exact charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hcard)

theorem additive_exponent
    (F : Type u) [Field F] [Finite F] (p n : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) (hcard : Nat.card F = p ^ n) :
    AddMonoid.exponent F = p := by
  let := characteristic_of_cardinality F p n hp hn hcard
  rw [← ringChar_eq_addMonoidExponent, ringChar.eq F p]

theorem least_positive_annihilator
    (F : Type u) [Field F] [Finite F] (p n : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) (hcard : Nat.card F = p ^ n) :
    0 < p ∧ (∀ x : F, p • x = 0) ∧
      ∀ m : ℕ, 0 < m → (∀ x : F, m • x = 0) → p ≤ m := by
  have he := additive_exponent F p n hp hn hcard
  refine ⟨hp.pos, ?_, ?_⟩
  · intro x
    rw [← he]
    exact AddMonoid.exponent_nsmul_eq_zero x
  · intro m hm hann
    rw [← he]
    exact AddMonoid.exponent_min' m hm hann

theorem additive_cyclic_iff
    (F : Type u) [Field F] [Finite F] (p n : ℕ)
    (hp : p.Prime) (hn : 1 ≤ n) (hcard : Nat.card F = p ^ n) :
    IsAddCyclic F ↔ n = 1 := by
  rw [IsAddCyclic.iff_exponent_eq_card, additive_exponent F p n hp hn hcard, hcard]
  constructor
  · intro h
    apply Nat.pow_right_injective hp.two_le
    simpa only [pow_one] using h.symm
  · rintro rfl
    exact (pow_one p).symm

theorem prime_cardinality_cyclic
    (F : Type u) [Field F] [Finite F] (p : ℕ)
    (hp : p.Prime) (hcard : Nat.card F = p) : IsAddCyclic F := by
  exact (additive_cyclic_iff F p 1 hp le_rfl (by simpa only [pow_one] using hcard)).mpr rfl

theorem higher_degree_not_cyclic
    (F : Type u) [Field F] [Finite F] (p n : ℕ)
    (hp : p.Prime) (hn : 1 < n) (hcard : Nat.card F = p ^ n) : ¬ IsAddCyclic F := by
  intro h
  exact (ne_of_gt hn) ((additive_cyclic_iff F p n hp hn.le hcard).mp h)

end D07.Ch13.AdditiveExponentCyclicity
