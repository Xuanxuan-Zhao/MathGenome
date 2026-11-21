import MathGenome.Internal.Specs.D07.Ch07.TorsionCountInvariants
import MathGenome.Internal.D07.Ch02.OrderDivisibility
import MathGenome.Internal.D07.Ch04.DirectProducts
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

namespace D07.Ch07.TorsionCountInvariants

open Specs.D07.Ch07.TorsionCountInvariants

/-- Taking annihilated elements commutes with a Cartesian product. -/
def torsionPiEquiv (I : Type*) (A : I → Type*) [∀ i, AddCommGroup (A i)]
    (p k : ℕ) :
    torsionSubgroup (∀ i, A i) p k ≃ (∀ i, torsionSubgroup (A i) p k) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun x := ⟨fun i => (x i).val, funext fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A cyclic prime-power factor contributes `p ^ min k e` choices. -/
theorem cyclic_torsion_card (p : ℕ) (hp : p.Prime) (e k : ℕ) :
    Nat.card (torsionSubgroup (ZMod (p ^ e)) p k) = p ^ min k e := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [torsionSubgroup, IsAddCyclic.card_nsmulAddMonoidHom_ker, Nat.card_zmod]
  rcases le_total e k with h | h
  · rw [Nat.min_eq_right h, Nat.gcd_eq_left (Nat.pow_dvd_pow p h)]
  · rw [Nat.min_eq_left h, Nat.gcd_eq_right (Nat.pow_dvd_pow p h)]

theorem torsion_cardinality : TorsionCardinality := by
  intro p hp e _he k
  calc
    Nat.card (torsionSubgroup (PrimePowerProduct p e) p k) =
        Nat.card (∀ i : Fin e.length, torsionSubgroup (ZMod (p ^ e.get i)) p k) :=
      Nat.card_congr (torsionPiEquiv _ _ p k)
    _ = ∏ i : Fin e.length, Nat.card (torsionSubgroup (ZMod (p ^ e.get i)) p k) :=
      Nat.card_pi
    _ = ∏ i : Fin e.length, p ^ min k (e.get i) := by
      simp only [cyclic_torsion_card p hp]
    _ = p ^ ∑ i : Fin e.length, min k (e.get i) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = p ^ torsionExponent e k := by
      congr 1
      exact Fin.sum_univ_fun_getElem e (fun n => min k n)

/-- A forward difference of `s` is the number of exponents above the cutoff.
This elementary identity even allows zero exponents. -/
theorem exponent_step (e : List ℕ) (k : ℕ) :
    torsionExponent e (k + 1) = torsionExponent e k +
      (e.filter fun n => k + 1 ≤ n).length := by
  induction e with
  | nil => simp [torsionExponent]
  | cons a e ih =>
    simp only [torsionExponent, List.map_cons, List.sum_cons] at ih ⊢
    by_cases h : k + 1 ≤ a
    · simp only [List.filter_cons, decide_eq_true_eq, h, ↓reduceIte, List.length_cons]
      omega
    · simp only [List.filter_cons, decide_eq_true_eq, h, ↓reduceIte]
      omega

theorem successive_difference : SuccessiveDifference := by
  intro e _he k hk
  have h := exponent_step e (k - 1)
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at h
  omega

/-- Separate the exponents exactly equal to `k` from those strictly larger. -/
theorem tail_count_step (e : List ℕ) (k : ℕ) :
    (e.filter fun n => k ≤ n).length =
      e.count k + (e.filter fun n => k + 1 ≤ n).length := by
  induction e with
  | nil => simp
  | cons a e ih =>
    simp only [List.filter_cons, List.count_cons, beq_iff_eq, decide_eq_true_eq]
    by_cases h : a = k
    · subst a
      simp only [le_refl, Nat.not_succ_le_self, ↓reduceIte, List.length_cons]
      omega
    · by_cases ha : k ≤ a
      · have ha' : k + 1 ≤ a := by omega
        simp only [h, ha, ha', ↓reduceIte, List.length_cons]
        omega
      · have ha' : ¬ k + 1 ≤ a := by omega
        simpa only [h, ha, ha', ↓reduceIte, Nat.add_zero] using ih

theorem exponent_multiplicity : ExponentMultiplicity := by
  intro e he k hk
  have hnext := successive_difference e he (k + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hnext
  rw [successive_difference e he k hk, hnext]
  have h := tail_count_step e k
  omega

theorem counts_recover_exponents : CountsRecoverExponents := by
  intro p hp e f he hf hcount
  have hs : ∀ k, torsionExponent e k = torsionExponent f k := by
    intro k
    apply Nat.pow_right_injective hp.two_le
    simpa only [torsion_cardinality p hp e he k, torsion_cardinality p hp f hf k]
      using hcount k
  apply List.perm_iff_count.mpr
  intro k
  by_cases hk : k = 0
  · subst k
    have he0 : 0 ∉ e := by intro h; have := he 0 h; omega
    have hf0 : 0 ∉ f := by intro h; have := hf 0 h; omega
    simp [List.count_eq_zero.mpr he0, List.count_eq_zero.mpr hf0]
  · rw [exponent_multiplicity e he k (by omega),
      exponent_multiplicity f hf k (by omega), hs k, hs (k - 1), hs (k + 1)]

theorem boundary_counts : BoundaryCounts := by
  intro p hp
  constructor
  · intro e he
    rw [torsion_cardinality p hp e he 0]
    simp [torsionExponent]
  · intro k
    rw [torsion_cardinality p hp [] (by simp) k]
    simp [torsionExponent]

end D07.Ch07.TorsionCountInvariants
