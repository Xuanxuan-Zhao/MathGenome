import MathGenome.Internal.Specs.D07.Ch18.PgroupNilpotent
import MathGenome.Internal.D07.Ch18.NilpotenceCriteria
import MathGenome.Internal.D07.Ch06.PgroupCenter
import MathGenome.Internal.D07.Ch06.CyclicCentralQuotient
import Lean.Elab.Tactic.Omega

/-!
Finite p-groups have class at most their exponent, with the improved bound
away from exponents zero and one. We induct on the exponent after quotienting
by the center. The center is nontrivial, so the quotient exponent decreases.
A central quotient of order one or p is cyclic and forces commutativity;
otherwise the sharper inductive bound lifts through the center in one step.
-/

namespace D07.Ch18.PgroupNilpotent

open Specs.D07.Ch18.NilpotenceCriteria

universe u

theorem classAtMost_mono (P : Type u) [Group P] {c d : ℕ}
    (h : classAtMostValue P c) (hcd : c ≤ d) : classAtMostValue P d := by
  exact top_unique (h ▸ Subgroup.upperCentralSeries_mono P hcd)

/-- A bound for the central quotient lifts by one upper-series step. -/
theorem classAtMost_of_center_quotient (P : Type u) [Group P] (c : ℕ)
    (h : classAtMostValue (P ⧸ Subgroup.center P) c) :
    classAtMostValue P (c + 1) := by
  change Subgroup.upperCentralSeries P (c + 1) = ⊤
  rw [← Subgroup.comap_upperCentralSeries_quotient_center]
  rw [show Subgroup.upperCentralSeries (P ⧸ Subgroup.center P) c = ⊤ from h]
  exact Subgroup.comap_top _

/-- In a nontrivial finite p-group the central quotient has smaller exponent. -/
theorem center_quotient_smaller_exponent (P : Type u) [Group P] [Finite P]
    [Nontrivial P] (p a : ℕ) (hp : p.Prime) (hcard : Nat.card P = p ^ a) :
    ∃ b : ℕ, b < a ∧ Nat.card (P ⧸ Subgroup.center P) = p ^ b := by
  have hcenter : Nontrivial (Subgroup.center P) :=
    Ch06.PgroupCenter.center_nontrivial P p hp ⟨inferInstance, a, hcard⟩
  let := hcenter
  have hlt : Nat.card (P ⧸ Subgroup.center P) < Nat.card P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)]
    exact lt_mul_of_one_lt_right Nat.card_pos
      (Finite.one_lt_card_iff_nontrivial.mpr inferInstance)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := ((IsPGroup.of_card hcard).to_quotient (Subgroup.center P)).exists_card_eq
  exact ⟨b, (Nat.pow_lt_pow_iff_right hp.one_lt).mp (hb ▸ hcard ▸ hlt), hb⟩

theorem exponent_zero_class_zero (P : Type u) [Group P] [Finite P]
    (p : ℕ) (_hp : p.Prime) (hcard : Nat.card P = p ^ 0) :
    hasClassValue P 0 := by
  apply (NilpotenceCriteria.class_zero_iff_subsingleton P).mpr
  exact (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1

theorem prime_order_class_one (P : Type u) [Group P] [Finite P]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card P = p ^ 1) :
    hasClassValue P 1 := by
  have hc : Nat.card P = p := by simpa using hcard
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic P := isCyclic_of_prime_card hc
  apply (NilpotenceCriteria.class_one_iff_nontrivial_abelian P).mpr
  exact ⟨Finite.one_lt_card_iff_nontrivial.mp (hc ▸ hp.one_lt),
    (inferInstance : IsMulCommutative P).is_comm.comm⟩

/-- The small central quotients used in the induction are cyclic. -/
theorem abelian_of_center_quotient_small_exponent (P : Type u) [Group P]
    [Finite P] (p b : ℕ) (hp : p.Prime)
    (hcard : Nat.card (P ⧸ Subgroup.center P) = p ^ b) (hb : b ≤ 1) :
    ∀ x y : P, x * y = y * x := by
  apply Ch06.CyclicCentralQuotient.cyclic_central_quotient_abelian
  let : Fact p.Prime := ⟨hp⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · let : Subsingleton (P ⧸ Subgroup.center P) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa using hcard)).1
    infer_instance
  · exact isCyclic_of_prime_card (by simpa using hcard)

theorem sharper_class_bound (P : Type u) [Group P] [Finite P]
    (p a : ℕ) (hp : p.Prime) (hcard : Nat.card P = p ^ a) (ha : 2 ≤ a) :
    classAtMostValue P (a - 1) := by
  induction a using Nat.strong_induction_on generalizing P with
  | h a ih =>
    have hnt : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]
      exact one_lt_pow₀ hp.one_lt (by omega))
    let := hnt
    obtain ⟨b, hba, hb⟩ := center_quotient_smaller_exponent P p a hp hcard
    by_cases hsmall : b ≤ 1
    · have hcomm := abelian_of_center_quotient_small_exponent P p b hp hb hsmall
      have hone : classAtMostValue P 1 :=
        Subgroup.upperCentralSeries_one_eq_top_iff.mpr ⟨⟨hcomm⟩⟩
      exact classAtMost_mono P hone (by omega)
    · have hbound := ih b hba (P ⧸ Subgroup.center P) hb (by omega)
      have hlift := classAtMost_of_center_quotient P (b - 1) hbound
      exact classAtMost_mono P hlift (by omega)

theorem class_at_most_exponent (P : Type u) [Group P] [Finite P]
    (p a : ℕ) (hp : p.Prime) (hcard : Nat.card P = p ^ a) :
    classAtMostValue P a := by
  by_cases ha : 2 ≤ a
  · exact classAtMost_mono P (sharper_class_bound P p a hp hcard ha) (by omega)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (show a ≤ 1 by omega) with rfl | rfl
    · exact (exponent_zero_class_zero P p hp hcard).1
    · exact (prime_order_class_one P p hp hcard).1

theorem prime_power_nilpotent (P : Type u) [Group P] [Finite P]
    (p a : ℕ) (hp : p.Prime) (hcard : Nat.card P = p ^ a) :
    Group.IsNilpotent P :=
  (NilpotenceCriteria.nilpotent_iff_exists_bound P).mpr
    ⟨a, class_at_most_exponent P p a hp hcard⟩

end D07.Ch18.PgroupNilpotent
