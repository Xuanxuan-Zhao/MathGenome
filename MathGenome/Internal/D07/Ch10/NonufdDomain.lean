import MathGenome.Internal.Specs.D07.Ch10.NonufdDomain
import MathGenome.Internal.D07.Ch10.IrreducibleNonprime
import MathGenome.Internal.D07.Ch10.UfdDefinition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! The two inequivalent irreducible factorizations of six in `ℤ[√(-5)]`. -/

namespace D07.Ch10.NonufdDomain

open Specs.D07.Ch10.IrreducibleNonprime (R)
open Specs.D07.Ch10.NonufdDomain

theorem normTwoImpossible : NormTwoImpossible := by
  intro a b h
  have hb : b = 0 := by
    have hs : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    nlinarith [sq_nonneg b]
  rw [hb] at h
  have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith
  obtain ⟨ha₁, ha₂⟩ := ha
  interval_cases a <;> norm_num at h

theorem witnessIdentity : WitnessIdentity := by
  constructor
  · norm_num
  · ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem witnessNorms : WitnessNorms := by
  norm_num [WitnessNorms, Zsqrtd.norm]

/-- The only possible nonunit norm splits of four or six involve a norm
two or a norm three. Neither norm occurs in this ring. -/
theorem irreducible_of_norm_four_or_six (z : R)
    (hz : Zsqrtd.norm z = 4 ∨ Zsqrtd.norm z = 6) : Irreducible z := by
  have hnu : ¬IsUnit z := by
    intro h
    have h1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) z).mpr h
    omega
  refine ⟨hnu, ?_⟩
  intro u v huv
  by_cases hu : IsUnit u
  · exact Or.inl hu
  by_cases hv : IsUnit v
  · exact Or.inr hv
  exfalso
  have hp : Zsqrtd.norm u * Zsqrtd.norm v = Zsqrtd.norm z := by
    rw [← Zsqrtd.norm_mul, ← huv]
  have hu0 := IrreducibleNonprime.normNonnegativeAndZero.1 u
  have hv0 := IrreducibleNonprime.normNonnegativeAndZero.1 v
  have hu1 : Zsqrtd.norm u ≠ 1 :=
    fun h => hu ((Zsqrtd.norm_eq_one_iff' (by norm_num) u).mp h)
  have hv1 : Zsqrtd.norm v ≠ 1 :=
    fun h => hv ((Zsqrtd.norm_eq_one_iff' (by norm_num) v).mp h)
  have hu2 : 2 ≤ Zsqrtd.norm u := by
    have hne : Zsqrtd.norm u ≠ 0 := by
      intro h; rw [h, zero_mul] at hp; omega
    omega
  have hv2 : 2 ≤ Zsqrtd.norm v := by
    have hne : Zsqrtd.norm v ≠ 0 := by
      intro h; rw [h, mul_zero] at hp; omega
    omega
  have hu3 : Zsqrtd.norm u ≤ 3 := by
    rcases hz with hz | hz <;> nlinarith
  have hcoord := IrreducibleNonprime.normFormula u.re u.im
  rcases (by omega : Zsqrtd.norm u = 2 ∨ Zsqrtd.norm u = 3) with h | h
  · exact normTwoImpossible u.re u.im (hcoord.symm.trans h)
  · exact IrreducibleNonprime.normThreeImpossible u.re u.im (hcoord.symm.trans h)

theorem witnessIrreducible : WitnessIrreducible := by
  exact ⟨irreducible_of_norm_four_or_six 2 (Or.inl witnessNorms.1),
    IrreducibleNonprime.threeIrreducible,
    irreducible_of_norm_four_or_six _ (Or.inr witnessNorms.2.2.1),
    irreducible_of_norm_four_or_six _ (Or.inr witnessNorms.2.2.2)⟩

theorem units : Units := IrreducibleNonprime.units

theorem integerNotAssociated : IntegerNotAssociated := by
  intro n z hz h
  obtain ⟨u, hu⟩ := h
  rcases (units (u : R)).mp u.isUnit with hunit | hunit
  · rw [hunit, mul_one] at hu
    have him := congrArg Zsqrtd.im hu
    exact hz (by simpa using him.symm)
  · rw [hunit, mul_neg_one] at hu
    have him := congrArg Zsqrtd.im hu
    exact hz (by simpa using him.symm)

theorem crossNonassociated : CrossNonassociated := by
  exact ⟨integerNotAssociated 2 _ (by norm_num),
    integerNotAssociated 2 _ (by norm_num),
    integerNotAssociated 3 _ (by norm_num),
    integerNotAssociated 3 _ (by norm_num)⟩

theorem distinctIrreducibleFactorizations : DistinctIrreducibleFactorizations := by
  have hs : ∀ p ∈ ({2, 3} : Multiset R), Irreducible p := by
    intro p hp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact witnessIrreducible.1
    · exact witnessIrreducible.2.1
  have ht : ∀ p ∈ ({1 + Zsqrtd.sqrtd, 1 - Zsqrtd.sqrtd} : Multiset R),
      Irreducible p := by
    intro p hp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact witnessIrreducible.2.2.1
    · exact witnessIrreducible.2.2.2
  refine ⟨hs, ht, ?_, ?_, ?_⟩
  · simpa [Multiset.insert_eq_cons] using witnessIdentity.1.symm
  · simpa [Multiset.insert_eq_cons] using witnessIdentity.2.symm
  · intro h
    obtain ⟨q, hq, h2q⟩ :=
      Multiset.exists_mem_of_rel_of_mem h (Multiset.mem_cons_self (2 : R) {3})
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact crossNonassociated.1 h2q
    · exact crossNonassociated.2.1 h2q

theorem domainNotUfd : DomainNotUfd := by
  refine ⟨IrreducibleNonprime.domain, ?_⟩
  intro h
  let : IsDomain R := IrreducibleNonprime.domain
  have huniq := ((UfdDefinition.ufdCharacterization R).mp h).2
  obtain ⟨hs, ht, hsp, htp, hne⟩ := distinctIrreducibleFactorizations
  exact hne (huniq _ _ hs ht (Associated.of_eq (hsp.trans htp.symm)))

end D07.Ch10.NonufdDomain
