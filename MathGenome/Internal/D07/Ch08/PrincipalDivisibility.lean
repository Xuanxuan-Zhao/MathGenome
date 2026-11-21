import MathGenome.Internal.Specs.D07.Ch08.PrincipalDivisibility
import MathGenome.Internal.D07.Ch08.IdealGeneration
import Mathlib.Data.Int.Lemmas

/-! Principal ideals and divisibility, and the classification of ideals of ℤ. -/

universe u
namespace D07.Ch08.PrincipalDivisibility

open Specs.D07.Ch08.PrincipalDivisibility

/-- The upstream finite-sum formulas identify the two spans. -/
theorem commutativeSpanCompatibility : CommutativeSpanCompatibility.{u} := by
  intro R _ S
  ext x
  change x ∈ TwoSidedIdeal.span S ↔ x ∈ Ideal.span S
  exact (D07.Ch08.IdealGeneration.commutativeFormula R S x).trans
    (D07.Ch08.IdealGeneration.leftIdealFormula R S x).symm

theorem principalIdealFormula : PrincipalIdealFormula.{u} := by
  intro R _ a x
  change x ∈ (TwoSidedIdeal.span {a}).asIdeal ↔ _
  rw [commutativeSpanCompatibility R {a}, Ideal.mem_span_singleton']
  exact exists_congr fun r => eq_comm

theorem principalDivisibility : DivisibilityEquivalences.{u} := by
  intro R _ a b
  have hm : b ∈ TwoSidedIdeal.span {a} ↔ a ∣ b := by
    change b ∈ (TwoSidedIdeal.span {a}).asIdeal ↔ _
    rw [commutativeSpanCompatibility R {a}, Ideal.mem_span_singleton]
  refine ⟨hm, ?_⟩
  rw [TwoSidedIdeal.span_le, Set.singleton_subset_iff]
  exact hm.symm

/-- Well-order positive natural representatives of members of a nonzero ideal. -/
lemma exists_least_positive (I : Ideal ℤ) (hI : I ≠ ⊥) :
    ∃ d : ℤ, 0 < d ∧ d ∈ I ∧ ∀ a : ℤ, a ∈ I → 0 < a → d ≤ a := by
  classical
  obtain ⟨a, ha, ha0⟩ := I.ne_bot_iff.mp hI
  have habs : |a| ∈ I := by
    rcases le_total 0 a with h | h
    · simpa only [abs_of_nonneg h] using ha
    · simpa only [abs_of_nonpos h] using I.neg_mem ha
  have hex : ∃ n : ℕ, 0 < (n : ℤ) ∧ (n : ℤ) ∈ I :=
    ⟨a.natAbs, by simpa only [Int.natCast_natAbs] using abs_pos.mpr ha0,
      by simpa only [Int.natCast_natAbs] using habs⟩
  refine ⟨(Nat.find hex : ℤ), (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro b hb hbpos
  have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hbpos.le
  have hmin : Nat.find hex ≤ b.toNat := Nat.find_min' hex (by simpa only [hbcast] using And.intro hbpos hb)
  have hmin' : (Nat.find hex : ℤ) ≤ (b.toNat : ℤ) := by exact_mod_cast hmin
  simpa only [hbcast] using hmin'

/-- Division by a least positive member leaves a remainder in the ideal;
minimality forces that remainder to vanish. -/
lemma dvd_of_least_positive (I : Ideal ℤ) {d : ℤ} (hd : 0 < d) (hdI : d ∈ I)
    (hmin : ∀ a : ℤ, a ∈ I → 0 < a → d ≤ a) {a : ℤ} (ha : a ∈ I) : d ∣ a := by
  have hrI : a % d ∈ I := by
    rw [Int.emod_def]
    exact I.sub_mem ha (by simpa only [mul_comm] using I.mul_mem_left (a / d) hdI)
  have hr0 : 0 ≤ a % d := Int.emod_nonneg a hd.ne'
  have hrlt : a % d < d := Int.emod_lt_of_pos a hd
  have hr : a % d = 0 := by
    by_contra h
    exact (not_le_of_gt hrlt) (hmin _ hrI (lt_of_le_of_ne hr0 (Ne.symm h)))
  exact Int.dvd_of_emod_eq_zero hr

theorem integerNonzeroIdealPositiveGenerator : IntegerNonzeroIdealPositiveGenerator := by
  intro I hI
  obtain ⟨d, hd, hdI, hmin⟩ := exists_least_positive I hI
  refine ⟨d, hd, hdI, hmin, le_antisymm ?_ ?_⟩
  · intro a ha
    exact Ideal.mem_span_singleton.mpr (dvd_of_least_positive I hd hdI hmin ha)
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hdI)

theorem integerZeroIdeal : IntegerZeroIdeal := by
  refine ⟨Ideal.span_singleton_zero, ?_⟩
  apply (TwoSidedIdeal.orderIsoIdeal (R := ℤ)).injective
  change (TwoSidedIdeal.span ({0} : Set ℤ)).asIdeal = (⊥ : TwoSidedIdeal ℤ).asIdeal
  rw [commutativeSpanCompatibility ℤ {0}, Ideal.span_singleton_zero,
    TwoSidedIdeal.bot_asIdeal]

theorem positiveGeneratorUnique : PositiveGeneratorUnique := by
  intro d e hd he h
  have hde : d ∣ e := Ideal.mem_span_singleton.mp (h.symm ▸ Ideal.mem_span_singleton_self e)
  have hed : e ∣ d := Ideal.mem_span_singleton.mp (h ▸ Ideal.mem_span_singleton_self d)
  exact Int.dvd_antisymm hd.le he.le hde hed

/-- Nonnegative generators are unique also when one of them is zero. -/
lemma nonnegative_generator_unique {d e : ℤ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (h : Ideal.span {d} = Ideal.span {e}) : d = e := by
  apply Int.dvd_antisymm hd he
  · exact Ideal.span_singleton_le_span_singleton.mp h.ge
  · exact Ideal.span_singleton_le_span_singleton.mp h.le

theorem integerIdealClassification : IntegerIdealClassification := by
  intro I
  by_cases hI : I = ⊥
  · refine ⟨0, ⟨le_rfl, hI.trans Ideal.span_singleton_zero.symm⟩, ?_⟩
    intro e he
    exact nonnegative_generator_unique he.1 le_rfl (he.2.symm.trans (hI.trans Ideal.span_singleton_zero.symm))
  · obtain ⟨d, hd, _, _, hgen⟩ := integerNonzeroIdealPositiveGenerator I hI
    refine ⟨d, ⟨hd.le, hgen⟩, ?_⟩
    intro e he
    exact nonnegative_generator_unique he.1 hd.le (he.2.symm.trans hgen)

theorem integerTwoSidedIdealClassification : IntegerTwoSidedIdealClassification := by
  intro I
  obtain ⟨d, hd, huniq⟩ := integerIdealClassification I.asIdeal
  have hgen : I = TwoSidedIdeal.span {d} := by
    apply (TwoSidedIdeal.orderIsoIdeal (R := ℤ)).injective
    change I.asIdeal = (TwoSidedIdeal.span {d}).asIdeal
    rw [commutativeSpanCompatibility ℤ {d}]
    exact hd.2
  refine ⟨d, ⟨hd.1, hgen⟩, ?_⟩
  intro e he
  apply huniq e
  refine ⟨he.1, ?_⟩
  rw [he.2, commutativeSpanCompatibility ℤ {e}]

end D07.Ch08.PrincipalDivisibility
