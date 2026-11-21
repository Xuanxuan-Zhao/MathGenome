import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.ReflectionCycles
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.CycleIndex
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Intervals

namespace FiniteCombinatorics.Reflection
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev dihedralAction := ReflectionSpec.dihedralAction
abbrev pair := @ReflectionSpec.pair
abbrev pairEquiv := ReflectionSpec.pairEquiv
abbrev reflection := @ReflectionSpec.reflection
noncomputable abbrev fixedResidues := @ReflectionSpec.fixedResidues
noncomputable abbrev reflectionCount := @ReflectionSpec.reflectionCount
noncomputable abbrev solvableOffsets := ReflectionSpec.solvableOffsets
noncomputable abbrev reflectionMonomial := @ReflectionSpec.reflectionMonomial

theorem pair_mul {n : ℕ} (a b : ZMod n) (e f : Bool) :
    pair a e * pair b f = pair (a + if e then -b else b) (Bool.xor e f) := by
  cases e <;> cases f <;> simp [pair, ReflectionSpec.pair] <;> abel

theorem pair_action {n : ℕ} (a x : ZMod n) (e : Bool) :
    pair a e • x = a + if e then -x else x := by
  change ReflectionSpec.act (pair a e) x = _
  cases e <;> simp [pair, ReflectionSpec.pair, ReflectionSpec.act, sub_eq_add_neg]

theorem group_card (n : ℕ) [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n :=
  DihedralGroup.card

theorem reflection_action {n : ℕ} (a : ZMod n) :
    CycleIndexSpec.actionPermutation (DihedralGroup n) (ZMod n) (pair a true) =
      reflection a := by
  ext x
  change pair a true • x = a - x
  simp [pair_action, sub_eq_add_neg]

theorem reflection_square {n : ℕ} (a : ZMod n) : (pair a true) ^ 2 = 1 := by
  simp [pair, ReflectionSpec.pair, sq]

theorem reflection_involutive {n : ℕ} (a : ZMod n) :
    Function.Involutive (reflection a) := fun x => sub_sub_cancel a x

theorem fixed_equation {n : ℕ} (a x : ZMod n) :
    reflection a x = x ↔ 2 * x = a := by
  change a - x = x ↔ 2 * x = a
  constructor <;> intro h <;> linear_combination -h

theorem reflection_number (n : ℕ) [NeZero n] :
    (Finset.univ.image (fun a : ZMod n => pair a true)).card = n := by
  rw [Finset.card_image_of_injective, Finset.card_univ, ZMod.card]
  intro a b h
  simpa [pair, ReflectionSpec.pair] using h

/-- An involution has the complete cyclic orbit {x, σx}, including a singleton
when x is fixed. -/
theorem involution_orbit {X : Type*} [Fintype X] (σ : Equiv.Perm X)
    (hσ : Function.Involutive σ) (x : X) :
    Permutation.cyclicOrbit σ x = {x, σ x} := by
  classical
  ext y
  rw [Permutation.mem_cyclicOrbit_iff_pow]
  constructor
  · rintro ⟨k, rfl⟩
    have hk : (σ ^ k) x = x ∨ (σ ^ k) x = σ x := by
      induction k with
      | zero => exact Or.inl (by simp)
      | succ k ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · exact Or.inr (congrArg σ h)
        · exact Or.inl ((congrArg σ h).trans (hσ x))
    simpa using hk
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem involution_cycle_lengths {X : Type*} [Fintype X] (σ : Equiv.Perm X)
    (hσ : Function.Involutive σ) (C : Finset X) (hC : C ∈ Permutation.cycles σ) :
    C.card = 1 ∨ C.card = 2 := by
  classical
  obtain ⟨x, rfl⟩ := (Permutation.mem_cycles σ C).mp hC
  rw [involution_orbit σ hσ]
  by_cases hx : x = σ x
  · simp [← hx]
  · right; simp [hx]

theorem involution_count_other {X : Type*} [Fintype X] (σ : Equiv.Perm X)
    (hσ : Function.Involutive σ) (k : ℕ) (h1 : k ≠ 1) (h2 : k ≠ 2) :
    Permutation.countCyclesOfLength σ k = 0 := by
  classical
  change ((Permutation.cycles σ).filter (fun C => C.card = k)).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro C hC hk
  rcases involution_cycle_lengths σ hσ C hC with h | h
  · exact h1 (hk.symm.trans h)
  · exact h2 (hk.symm.trans h)

theorem cycle_lengths {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ)
    (h1 : k ≠ 1) (h2 : k ≠ 2) : reflectionCount a k = 0 :=
  involution_count_other (reflection a) (reflection_involutive a) k h1 h2

/-- Count the singleton and paired blocks of an involution. -/
theorem involution_count_balance {X : Type*} [Fintype X] (σ : Equiv.Perm X)
    (hσ : Function.Involutive σ) :
    Permutation.countCyclesOfLength σ 1 + 2 * Permutation.countCyclesOfLength σ 2 =
      Fintype.card X := by
  classical
  have hc : (∑ k ∈ ({1, 2} : Finset ℕ), k * Permutation.countCyclesOfLength σ k) =
      ∑ C ∈ Permutation.cycles σ, C.card := by
    calc
      _ = ∑ k ∈ ({1, 2} : Finset ℕ),
          ∑ C ∈ (Permutation.cycles σ).filter (fun C => C.card = k), C.card := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_const_nat (fun C hC => (Finset.mem_filter.mp hC).2)]
        exact Nat.mul_comm _ _
      _ = _ := by
        apply Finset.sum_fiberwise_of_maps_to
        intro C hC
        simpa using involution_cycle_lengths σ hσ C hC
  have hh := hc.trans (Permutation.sum_cycleLength σ)
  simpa using hh

@[simp] theorem mem_fixedResidues {n : ℕ} [NeZero n] (a x : ZMod n) :
    x ∈ fixedResidues a ↔ 2 * x = a := by
  simp [fixedResidues, ReflectionSpec.fixedResidues]

@[simp] theorem mem_solvableOffsets {n : ℕ} [NeZero n] (a : ZMod n) :
    a ∈ solvableOffsets n ↔ ∃ x : ZMod n, 2 * x = a := by
  simp [solvableOffsets, ReflectionSpec.solvableOffsets]

theorem fixedResidues_card_translate {n : ℕ} [NeZero n] (a x : ZMod n)
    (hx : 2 * x = a) : (fixedResidues a).card = (fixedResidues (0 : ZMod n)).card := by
  classical
  apply Finset.card_bij (fun y _ => y - x)
  · intro y hy
    rw [mem_fixedResidues] at hy ⊢
    linear_combination hy - hx
  · intro y hy z hz h
    exact sub_left_injective h
  · intro z hz
    refine ⟨z + x, ?_, by simp⟩
    rw [mem_fixedResidues] at hz ⊢
    linear_combination hz + hx

theorem fixedResidues_card_of_unsolvable {n : ℕ} [NeZero n] (a : ZMod n)
    (ha : a ∉ solvableOffsets n) : (fixedResidues a).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact ha ((mem_solvableOffsets a).mpr ⟨x, (mem_fixedResidues a x).mp hx⟩)

theorem odd_double_injective {n : ℕ} (hn : Odd n) :
    Function.Injective (fun x : ZMod n => 2 * x) := by
  intro x y h
  have hz : (x - y) + (x - y) = 0 := by linear_combination h
  have he := (ZMod.add_self_eq_zero_iff_eq_zero hn).mp hz
  exact sub_eq_zero.mp he

theorem odd_fixed_card {n : ℕ} [NeZero n] (hn : Odd n) (a : ZMod n) :
    (fixedResidues a).card = 1 := by
  classical
  obtain ⟨x, hx⟩ := (Finite.surjective_of_injective (odd_double_injective hn)) a
  apply Finset.card_eq_one.mpr
  refine ⟨x, ?_⟩
  ext y
  simp only [mem_fixedResidues, Finset.mem_singleton]
  exact ⟨fun hy => odd_double_injective hn (hy.trans hx.symm), fun hy => hy ▸ hx⟩

theorem even_kernel {n : ℕ} [NeZero n] (hn : Even n) :
    fixedResidues (0 : ZMod n) = {0, ((n / 2 : ℕ) : ZMod n)} := by
  classical
  have hn2 : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn
  ext x
  rw [mem_fixedResidues]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    have hxneg : -x = x := by linear_combination -hx
    rcases (ZMod.neg_eq_self_iff x).mp hxneg with h0 | hv
    · exact Or.inl h0
    · right
      have hval : x.val = n / 2 := by omega
      rw [← ZMod.natCast_zmod_val x, hval]
  · rintro (rfl | rfl)
    · simp
    · rw [← Nat.cast_ofNat, ← Nat.cast_mul, hn2, ZMod.natCast_self]

theorem even_kernel_card {n : ℕ} [NeZero n] (hn : Even n) :
    (fixedResidues (0 : ZMod n)).card = 2 := by
  classical
  rw [even_kernel hn]
  have hnpos := NeZero.pos n
  have hn2 : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn
  have hhalf : n / 2 < n := by omega
  have hne : (0 : ZMod n) ≠ (n / 2 : ℕ) := by
    intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hhalf] at hv
    omega
  simp [hne]

theorem even_fixed_card {n : ℕ} [NeZero n] (hn : Even n) (a : ZMod n)
    (ha : a ∈ solvableOffsets n) : (fixedResidues a).card = 2 := by
  obtain ⟨x, hx⟩ := (mem_solvableOffsets a).mp ha
  rw [fixedResidues_card_translate a x hx, even_kernel_card hn]

theorem count_one_eq_fixed {n : ℕ} [NeZero n] (a : ZMod n) :
    reflectionCount a 1 = (fixedResidues a).card := by
  rw [show reflectionCount a 1 = Permutation.countCyclesOfLength (reflection a) 1 from rfl,
    Permutation.countCyclesOfLength_one]
  congr 1
  ext x
  simp [Permutation.mem_fixedPoints, fixed_equation]

theorem reflection_count_balance {n : ℕ} [NeZero n] (a : ZMod n) :
    reflectionCount a 1 + 2 * reflectionCount a 2 = n := by
  simpa only [reflectionCount, ReflectionSpec.reflectionCount,
    Permutation.countCyclesOfLength, ZMod.card] using involution_count_balance (reflection a) (reflection_involutive a)

theorem odd_classification {n : ℕ} [NeZero n] (hn : Odd n) (a : ZMod n) :
    (fixedResidues a).card = 1 ∧ reflectionCount a 1 = 1 ∧
      reflectionCount a 2 = (n - 1) / 2 := by
  have hf := odd_fixed_card hn a
  have h1 : reflectionCount a 1 = 1 := (count_one_eq_fixed a).trans hf
  have hb := reflection_count_balance a
  exact ⟨hf, h1, by omega⟩

theorem even_classification {n : ℕ} [NeZero n] (hn : Even n) (a : ZMod n) :
    (a ∈ solvableOffsets n → (fixedResidues a).card = 2 ∧
      reflectionCount a 1 = 2 ∧ reflectionCount a 2 = (n - 2) / 2) ∧
    (a ∉ solvableOffsets n → (fixedResidues a).card = 0 ∧
      reflectionCount a 1 = 0 ∧ reflectionCount a 2 = n / 2) := by
  have hb := reflection_count_balance a
  constructor
  · intro ha
    have hf := even_fixed_card hn a ha
    have h1 : reflectionCount a 1 = 2 := (count_one_eq_fixed a).trans hf
    exact ⟨hf, h1, by omega⟩
  · intro ha
    have hf := fixedResidues_card_of_unsolvable a ha
    have h1 : reflectionCount a 1 = 0 := (count_one_eq_fixed a).trans hf
    exact ⟨hf, h1, by omega⟩

theorem even_distribution {n : ℕ} [NeZero n] (hn : Even n) :
    (solvableOffsets n).card = n / 2 ∧
      ((Finset.univ : Finset (ZMod n)) \ solvableOffsets n).card = n / 2 := by
  classical
  have hfiber : n = ∑ a ∈ solvableOffsets n, (fixedResidues a).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod n))) (t := solvableOffsets n)
      (f := fun x : ZMod n => 2 * x)
      (fun x _ => (mem_solvableOffsets (2 * x)).mpr ⟨x, rfl⟩)
    simpa only [Finset.card_univ, ZMod.card, fixedResidues,
      ReflectionSpec.fixedResidues] using h
  have he : (∑ a ∈ solvableOffsets n, (fixedResidues a).card) =
      (solvableOffsets n).card * 2 := by
    calc
      _ = ∑ _a ∈ solvableOffsets n, 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        exact even_fixed_card hn a ha
      _ = _ := by simp
  have hc : (solvableOffsets n).card = n / 2 := by omega
  refine ⟨hc, ?_⟩
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card, hc]
  have := Nat.two_mul_div_two_of_even hn
  omega

theorem reflection_count_gt {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ) (hk : n < k) :
    reflectionCount a k = 0 := by
  exact Permutation.countCyclesOfLength_eq_zero_of_gt (reflection a) k
    (by simpa only [ZMod.card] using hk)

/-- Terms of exponent zero disappear. In particular s₂ is harmless at n=1,
where it is outside the polynomial's actual variable range. -/
theorem reflection_monomial_eq {R : Type*} [CommMonoid R] {n : ℕ} [NeZero n]
    (a : ZMod n) (s : ℕ → R) :
    reflectionMonomial a s = s 1 ^ reflectionCount a 1 * s 2 ^ reflectionCount a 2 := by
  classical
  by_cases hn1 : n = 1
  · subst n
    have h2 : reflectionCount a 2 = 0 := reflection_count_gt a 2 (by decide)
    simp [reflectionMonomial, ReflectionSpec.reflectionMonomial, h2]
  · have hnpos := NeZero.pos n
    have hn2 : 2 ≤ n := by omega
    change (∏ k ∈ Finset.Icc 1 n, s k ^ reflectionCount a k) = _
    have he : (∏ k ∈ ({1, 2} : Finset ℕ), s k ^ reflectionCount a k) =
        ∏ k ∈ Finset.Icc 1 n, s k ^ reflectionCount a k := by
      apply Finset.prod_subset
      · intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simp [hn2, (by omega : 1 ≤ n)]
      · intro k hk hnot
        have hh : k ≠ 1 ∧ k ≠ 2 := by simpa using hnot
        rw [cycle_lengths a k hh.1 hh.2, pow_zero]
    rw [← he]
    simp

theorem odd_monomial {R : Type*} [CommMonoid R] {n : ℕ} [NeZero n]
    (hn : Odd n) (a : ZMod n) (s : ℕ → R) :
    reflectionMonomial a s = s 1 * s 2 ^ ((n - 1) / 2) := by
  obtain ⟨_, h1, h2⟩ := odd_classification hn a
  rw [reflection_monomial_eq, h1, h2, pow_one]

theorem even_monomial {R : Type*} [CommMonoid R] {n : ℕ} [NeZero n]
    (hn : Even n) (a : ZMod n) (s : ℕ → R) :
    reflectionMonomial a s = if a ∈ solvableOffsets n then
      s 1 ^ 2 * s 2 ^ ((n - 2) / 2) else s 2 ^ (n / 2) := by
  obtain ⟨he, ho⟩ := even_classification hn a
  rw [reflection_monomial_eq]
  split_ifs with ha
  · obtain ⟨_, h1, h2⟩ := he ha
    rw [h1, h2]
  · obtain ⟨_, h1, h2⟩ := ho ha
    rw [h1, h2, pow_zero, one_mul]

theorem action_count {n : ℕ} [NeZero n] (a : ZMod n) (k : ℕ) :
    Action.countCycles (DihedralGroup n) (ZMod n) (pair a true) k =
      reflectionCount a k := by
  change CycleIndexSpec.countCycles (DihedralGroup n) (ZMod n) (pair a true) k = _
  unfold CycleIndexSpec.countCycles
  rw [reflection_action]
  rfl

theorem monomial_bridge {n : ℕ} [NeZero n] (a : ZMod n) :
    MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
      (Action.elementMonomial (DihedralGroup n) (ZMod n) (pair a true)) =
        reflectionMonomial a (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ) := by
  classical
  change MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
    (CycleIndexSpec.elementMonomial (DihedralGroup n) (ZMod n) (pair a true)) = _
  unfold CycleIndexSpec.elementMonomial
  rw [reflection_action]
  simp only [CycleIndexSpec.permutationMonomial, map_prod, map_pow, MvPolynomial.rename_X]
  change (∏ i : Fin (Fintype.card (ZMod n)),
      (MvPolynomial.X (i.val + 1) : MvPolynomial ℕ ℚ) ^ reflectionCount a (i.val + 1)) =
    ∏ k ∈ Finset.Icc 1 n, MvPolynomial.X k ^ reflectionCount a k
  rw [Fin.prod_univ_eq_prod_range
    (fun k : ℕ => (MvPolynomial.X (k + 1) : MvPolynomial ℕ ℚ) ^ reflectionCount a (k + 1))
    (Fintype.card (ZMod n))]
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp only [ZMod.card, Nat.add_sub_cancel, add_comm 1]

theorem even_count_distribution {n : ℕ} [NeZero n] (hn : Even n) :
    (Finset.univ.filter (fun a : ZMod n => reflectionCount a 1 = 2)).card = n / 2 ∧
    (Finset.univ.filter (fun a : ZMod n => reflectionCount a 1 = 0)).card = n / 2 := by
  classical
  have h2 : Finset.univ.filter (fun a : ZMod n => reflectionCount a 1 = 2) =
      solvableOffsets n := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨he, ho⟩ := even_classification hn a
    by_cases ha : a ∈ solvableOffsets n
    · simp [ha, (he ha).2.1]
    · simp [ha, (ho ha).2.1]
  have h0 : Finset.univ.filter (fun a : ZMod n => reflectionCount a 1 = 0) =
      (Finset.univ : Finset (ZMod n)) \ solvableOffsets n := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    obtain ⟨he, ho⟩ := even_classification hn a
    by_cases ha : a ∈ solvableOffsets n
    · simp [ha, (he ha).2.1]
    · simp [ha, (ho ha).2.1]
  rw [h2, h0]
  exact even_distribution hn

theorem one_monomial {R : Type*} [CommMonoid R] (a : ZMod 1) (s : ℕ → R) :
    reflectionMonomial a s = s 1 := by
  simpa using odd_monomial (n := 1) (by decide) a s

end FiniteCombinatorics.Reflection
