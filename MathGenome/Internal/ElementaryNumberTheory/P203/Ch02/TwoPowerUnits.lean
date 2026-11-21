import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.TwoPowerUnits
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.FinCases

namespace P203.Ch02
open P203Specs.Ch02

theorem twoPowerFiveOrder : TwoPowerFiveOrder := by
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 2 := ⟨k - 2, by omega⟩
  exact ZMod.orderOf_five n

private theorem four_dvd_two_pow (k : ℕ) (hk : 2 ≤ k) : 4 ∣ 2 ^ k :=
  show 2 ^ 2 ∣ 2 ^ k from pow_dvd_pow 2 hk

private theorem expression_mod_four (k : ℕ) (hk : 2 ≤ k) (a b : ℕ) :
    (ZMod.cast (twoPowerExpression k a b) : ZMod 4) = (-1) ^ a := by
  change ZMod.castHom (four_dvd_two_pow k hk) (ZMod 4)
    ((-1 : ZMod (2 ^ k)) ^ a * 5 ^ b) = _
  simp only [map_mul, map_pow, map_neg, map_one, map_ofNat]
  rw [show (5 : ZMod 4) = 1 by decide, one_pow, mul_one]

private theorem expression_injective (k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (fun p : Fin 2 × Fin (2 ^ (k - 2)) =>
      twoPowerExpression k p.1.val p.2.val) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ he
  have hm := congrArg (fun x : ZMod (2 ^ k) => (ZMod.cast x : ZMod 4)) he
  rw [expression_mod_four k (by omega), expression_mod_four k (by omega)] at hm
  have ha : a = c := by
    exact (by decide : ∀ a c : Fin 2,
      (-1 : ZMod 4) ^ a.val = (-1) ^ c.val → a = c) a c hm
  subst c
  have hb : (5 : ZMod (2 ^ k)) ^ b.val = 5 ^ d.val := by
    fin_cases a <;> simpa [twoPowerExpression] using he
  have ho := twoPowerFiveOrder k hk
  have hbd : b.val = d.val := pow_injOn_Iio_orderOf
    (by simpa only [ho, Set.mem_Iio] using b.isLt) (by simpa only [ho, Set.mem_Iio] using d.isLt) hb
  exact Prod.ext rfl (Fin.ext hbd)

private def expressionUnit (k : ℕ) (p : Fin 2 × Fin (2 ^ (k - 2))) :
    (ZMod (2 ^ k))ˣ :=
  (-1) ^ p.1.val * (ZMod.unitOfCoprime 5 (by
    apply Nat.Coprime.pow_right
    decide)) ^ p.2.val

private theorem expressionUnit_val (k : ℕ) (p : Fin 2 × Fin (2 ^ (k - 2))) :
    (expressionUnit k p : ZMod (2 ^ k)) = twoPowerExpression k p.1.val p.2.val := by
  simp [expressionUnit, twoPowerExpression]

private theorem expressionUnit_bijective (k : ℕ) (hk : 3 ≤ k) :
    Function.Bijective (expressionUnit k) := by
  let : NeZero (2 ^ k) := ⟨by positivity⟩
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q h
    apply expression_injective k hk
    simpa only [expressionUnit_val] using congrArg Units.val h
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [Nat.reduceSub, mul_one]
    have h : k - 1 = k - 2 + 1 := by omega
    rw [h, pow_succ, Nat.mul_comm]

theorem twoPowerUniqueRepresentation : TwoPowerUniqueRepresentation := by
  intro k hk u
  obtain ⟨p, hp⟩ := (expressionUnit_bijective k hk).surjective u
  refine ⟨p, ?_, ?_⟩
  · simpa only [expressionUnit_val] using congrArg Units.val hp
  · intro q hq
    apply expression_injective k hk
    simpa only [expressionUnit_val] using hq.trans (congrArg Units.val hp).symm

/-- A class that is one modulo four is odd, so it is a unit modulo a power
of two. The bounded parametrization then forces its sign exponent to be zero. -/
theorem twoPowerFiveExhaustion : TwoPowerFiveExhaustion := by
  intro k hk x
  let : NeZero (2 ^ k) := ⟨by positivity⟩
  constructor
  · intro hx
    have hv : x.val % 4 = 1 := by
      have h : (x.val : ZMod 4) = 1 := by
        rw [← ZMod.cast_eq_val x]
        exact hx
      simpa only [ZMod.val_natCast, ZMod.val_one_eq_one_mod, Nat.reduceMod] using congrArg ZMod.val h
    have hunit : IsUnit x := by
      rw [← ZMod.natCast_zmod_val x,
        ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega)]
      intro hd
      have hmod := Nat.mod_eq_zero_of_dvd hd
      omega
    obtain ⟨u, hu⟩ := hunit
    obtain ⟨⟨a, b⟩, hp, _⟩ := twoPowerUniqueRepresentation k hk u
    have hm := congrArg (fun y : ZMod (2 ^ k) => (ZMod.cast y : ZMod 4)) hp
    rw [expression_mod_four k (by omega), hu, hx] at hm
    have ha : a = 0 :=
      (by decide : ∀ a : Fin 2, (-1 : ZMod 4) ^ a.val = 1 → a = 0) a hm
    refine ⟨b, ?_⟩
    simpa [ha, twoPowerExpression] using (hp.trans hu).symm
  · rintro ⟨b, rfl⟩
    simpa only [twoPowerExpression, pow_zero, one_mul] using
      expression_mod_four k (by omega) 0 b.val

end P203.Ch02
