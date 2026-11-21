import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.UniformPrimitiveRoot
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace P203.Ch02

open P203Specs.Ch02

/-- Reduction of a generator along a surjective group homomorphism. -/
lemma zpowers_image_of_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) {g : G}
    (hg : Subgroup.zpowers g = ⊤) : Subgroup.zpowers (f g) = ⊤ := by
  rw [← MonoidHom.map_zpowers, hg, Subgroup.map_top_of_surjective f hf]

/-- A unit has the same order as its underlying residue. -/
lemma residueUnit_order {m : ℕ} (u : (ZMod m)ˣ) :
    orderOf (u : ZMod m) = orderOf u := by
  exact orderOf_injective (Units.coeHom (ZMod m)) Units.coeHom_injective u

/-- An element whose order is the group cardinality generates that group. -/
lemma zpowers_eq_top_of_order_eq_card {G : Type*} [Group G] [Finite G]
    (g : G) (hg : orderOf g = Nat.card G) : Subgroup.zpowers g = ⊤ := by
  apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers g)).mp
  simpa only [Nat.card_zpowers] using hg

/-- Reduction preserves a fixed natural representative of two units. -/
lemma unitsMap_eq_of_representative {m n g : ℕ} (h : n ∣ m)
    (a : (ZMod m)ˣ) (b : (ZMod n)ˣ)
    (ha : (a : ZMod m) = (g : ZMod m))
    (hb : (b : ZMod n) = (g : ZMod n)) : ZMod.unitsMap h a = b := by
  apply Units.ext
  change ZMod.castHom h (ZMod n) (a : ZMod m) = (b : ZMod n)
  rw [ha, hb, map_natCast]

/-- Every representative of a generator modulo the square of an odd prime
is a generator modulo all its positive powers. -/
lemma primitiveRoot_all_powers_of_square (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (g : ℕ) (c : (ZMod (p ^ 2))ˣ)
    (hc : (c : ZMod (p ^ 2)) = (g : ZMod (p ^ 2)))
    (hcgen : Subgroup.zpowers c = ⊤) :
    ∀ k : ℕ, 1 ≤ k → ∃ u : ResidueUnits (p ^ k),
      (u : ZMod (p ^ k)) = (g : ZMod (p ^ k)) ∧ Subgroup.zpowers u = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hpge : 2 ≤ p := hp.two_le
  have hpm : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcop2 : g.Coprime (p ^ 2) :=
    (ZMod.isUnit_iff_coprime g (p ^ 2)).mp (hc ▸ c.isUnit)
  have hcop : g.Coprime p := hcop2.of_dvd_right (dvd_pow_self p (by decide))
  let u (k : ℕ) : (ZMod (p ^ k))ˣ :=
    ((ZMod.isUnit_iff_coprime g (p ^ k)).mpr (hcop.pow_right k)).unit
  have hu (k : ℕ) : (u k : ZMod (p ^ k)) = (g : ZMod (p ^ k)) :=
    IsUnit.unit_spec _
  let b : (ZMod p)ˣ := ZMod.unitsMap (dvd_pow_self p (by decide : 2 ≠ 0)) c
  have hb : (b : ZMod p) = (g : ZMod p) := by
    change ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p) (c : ZMod (p ^ 2)) = _
    rw [hc, map_natCast]
  have hgenb : Subgroup.zpowers b = ⊤ :=
    zpowers_image_of_surjective _ (ZMod.unitsMap_surjective _) hcgen
  have horderb : orderOf b = p - 1 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hgenb, Nat.card_eq_fintype_card, ZMod.card_units]
  have horder2 : orderOf c = p * (p - 1) := by
    rw [orderOf_eq_card_of_zpowers_eq_top hcgen, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by decide : 0 < 2)]
    simp
  have hbase : (p : ℤ) ∣ (g : ℤ) ^ (p - 1) - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have h : (b : ZMod p) ^ (p - 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← horderb, pow_orderOf_eq_one]
      rfl
    simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one,
      sub_eq_zero, hb] using h
  have hnotsquareInt : ¬ ((p : ℤ) ^ 2) ∣ (g : ℤ) ^ (p - 1) - 1 := by
    intro h
    have hz : ((g : ℕ) : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd
        ((g : ℤ) ^ (p - 1) - 1) (p ^ 2)).mpr (by simpa using h)
      simpa only [Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_one, sub_eq_zero] using hz
    have hpow : c ^ (p - 1) = 1 := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val, hc, Units.val_one] using hz
    have hdvd := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [horder2] at hdvd
    have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hdvd
    nlinarith
  obtain ⟨a, ha⟩ := hbase
  have hrepr : (g : ℤ) ^ (p - 1) = 1 + p * a := by linarith
  have ha_not : ¬ (p : ℤ) ∣ a := by
    rintro ⟨b, hb⟩
    apply hnotsquareInt
    refine ⟨b, ?_⟩
    rw [ha, hb]
    ring
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  refine ⟨u (n + 1), hu _, ?_⟩
  have hpoworder : orderOf ((u (n + 1)) ^ (p - 1)) = p ^ n := by
    rw [← residueUnit_order, Units.val_pow_eq_pow_val, hu]
    have heq : (g : ZMod (p ^ (n + 1))) ^ (p - 1) =
        1 + (p : ZMod (p ^ (n + 1))) * (a : ZMod (p ^ (n + 1))) := by
      simpa only [Int.cast_pow, Int.cast_add, Int.cast_one, Int.cast_mul,
        Int.cast_natCast] using
        congrArg (fun z : ℤ => (z : ZMod (p ^ (n + 1)))) hrepr
    rw [heq]
    exact ZMod.orderOf_one_add_mul_prime hp hp2 a ha_not n
  have hredn : ZMod.unitsMap (dvd_pow_self p (by omega : n + 1 ≠ 0)) (u (n + 1)) = b :=
    unitsMap_eq_of_representative _ _ _ (hu _) hb
  have hd1 : p - 1 ∣ orderOf (u (n + 1)) := by
    rw [← horderb, ← hredn]
    exact orderOf_map_dvd _ _
  have hdn : p ^ n ∣ orderOf (u (n + 1)) := by
    rw [← hpoworder]
    exact orderOf_pow_dvd _
  have hcoporders : (p ^ n).Coprime (p - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_self_sub_right hp.pos]
    simp
  have hcard : Nat.card (ZMod (p ^ (n + 1)))ˣ = p ^ n * (p - 1) := by
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ hp]
  apply zpowers_eq_top_of_order_eq_card
  apply Nat.dvd_antisymm (orderOf_dvd_natCard _)
  rw [hcard]
  exact hcoporders.mul_dvd_of_dvd_of_dvd hdn hd1

/-- A fixed integer primitive root for all positive powers of an odd prime,
as asserted in the second part of Theorem 2.4. -/
theorem uniformPrimitiveRoot : UniformPrimitiveRoot := by
  intro p hp hodd
  have hp2 : p ≠ 2 := hodd.ne_two_of_dvd_nat dvd_rfl
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, hc⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (ZMod.isCyclic_units_of_prime_pow p hp hp2 2)
  let g : ℕ := (c : ZMod (p ^ 2)).val
  have hrep : (c : ZMod (p ^ 2)) = (g : ZMod (p ^ 2)) := by
    simp [g]
  refine ⟨(g : ℤ), ?_⟩
  intro k hk
  obtain ⟨u, hu, hgen⟩ := primitiveRoot_all_powers_of_square p hp hp2 g c hrep hc k hk
  exact ⟨u, by simpa only [Int.cast_natCast] using hu, hgen⟩

end P203.Ch02
