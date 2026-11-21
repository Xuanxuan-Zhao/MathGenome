import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.MurnaghanNakayama
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.S4CharacterTable
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
open scoped BigOperators
namespace AdvancedFiniteGroupRepresentations

abbrev s4Shapes := Specs.AdvancedFiniteGroupRepresentations.s4Shapes
abbrev s4Cycles := Specs.AdvancedFiniteGroupRepresentations.s4Cycles
abbrev s4ClassSizes := Specs.AdvancedFiniteGroupRepresentations.s4ClassSizes
abbrev s4Centralizers := Specs.AdvancedFiniteGroupRepresentations.s4Centralizers
abbrev s4Table := Specs.AdvancedFiniteGroupRepresentations.s4Table
abbrev s4Character := Specs.AdvancedFiniteGroupRepresentations.s4Character

theorem s4_labels : Specs.AdvancedFiniteGroupRepresentations.s4_labelsType := by
  constructor
  · intro i
    change parts (s4Shapes i) = _
    rw [parts_eq_sorted_multiset (s4Shapes i)]
    fin_cases i <;>
      norm_num [s4Shapes, Specs.AdvancedFiniteGroupRepresentations.s4Shapes, Multiset.sort_cons]
  · intro j
    change parts (s4Cycles j) = _
    rw [parts_eq_sorted_multiset (s4Cycles j)]
    fin_cases j <;>
      norm_num [s4Cycles, Specs.AdvancedFiniteGroupRepresentations.s4Cycles,
        s4Shapes, Specs.AdvancedFiniteGroupRepresentations.s4Shapes, Multiset.sort_cons]

private theorem partition_eq_of_parts_eq {n : ℕ} {p q : Partition n}
    (h : parts p = parts q) : p = q := by
  apply Nat.Partition.ext
  have hm := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
  simpa only [parts_eq_sorted_multiset, Multiset.sort_eq] using hm

private theorem s4_parts_cases (p : Partition 4) : parts p = [4] ∨ parts p = [3,1] ∨ parts p = [2,2] ∨
    parts p = [2,1,1] ∨ parts p = [1,1,1,1] := by
  have hp : ∀ x ∈ parts p, 0 < x := fun x hx => parts_positive p x hx
  have hs := parts_sum p
  have ho := (List.sortedGE_iff_pairwise).mp (parts_sorted p)
  have hl := partition_length_le_size p
  change (parts p).length ≤ 4 at hl
  generalize he : parts p = l at hp hs ho hl ⊢
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  all_goals simp_all only [List.forall_mem_nil, and_true,
    List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    forall_eq, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    List.cons.injEq, List.nil_eq, or_false, reduceCtorEq]
  all_goals omega

theorem s4_shapes_bijective : Specs.AdvancedFiniteGroupRepresentations.s4_shapes_bijectiveType := by
  constructor
  · intro i j h
    have hp := congrArg (fun p : Partition 4 => parts p) h
    have hi := s4_labels.1 i
    have hj := s4_labels.1 j
    fin_cases i <;> fin_cases j <;> simp_all
  · intro p
    rcases s4_parts_cases p with h | h | h | h | h
    · exact ⟨0, partition_eq_of_parts_eq ((s4_labels.1 0).trans h.symm)⟩
    · exact ⟨1, partition_eq_of_parts_eq ((s4_labels.1 1).trans h.symm)⟩
    · exact ⟨2, partition_eq_of_parts_eq ((s4_labels.1 2).trans h.symm)⟩
    · exact ⟨3, partition_eq_of_parts_eq ((s4_labels.1 3).trans h.symm)⟩
    · exact ⟨4, partition_eq_of_parts_eq ((s4_labels.1 4).trans h.symm)⟩

theorem s4_cycles_bijective : Specs.AdvancedFiniteGroupRepresentations.s4_cycles_bijectiveType := by
  have h : s4Cycles = fun j => s4Shapes j.rev := by
    funext j
    fin_cases j <;> rfl
  change Function.Bijective s4Cycles
  rw [h]
  exact s4_shapes_bijective.comp Fin.revPerm.bijective

/-- An explicit, finite integer computation of a Vandermonde coefficient.
The colors assign each cycle to one variable. -/
def signedCycleAssignments {r k : ℕ} (a : Fin r → ℕ) (w : Fin k → ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℤ) *
    ∑ f : Fin k → Fin r,
      if ∀ i, staircase r (σ.symm i) + ∑ t, (if f t = i then w t else 0) = a i
      then 1 else 0

private theorem monomial_cycle_assignments {r k : ℕ}
    (a b : Fin r → ℕ) (w : Fin k → ℕ) :
    naturalCoefficient a
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm b) 1 *
        ∏ t, powerSum r (w t)) =
      ∑ f : Fin k → Fin r,
        if ∀ i, b i + ∑ t, (if f t = i then w t else 0) = a i then (1 : ℂ) else 0 := by
  classical
  simp only [powerSum, Specs.AdvancedFiniteGroupRepresentations.powerSum]
  rw [Fintype.prod_sum, Finset.mul_sum]
  change (∑ f : Fin k → Fin r, _ : Alphabet r).coeff _ = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [MvPolynomial.X_pow_eq_monomial, ← MvPolynomial.monomial_sum_prod,
    Finset.prod_const_one, MvPolynomial.monomial_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
  congr 1
  apply propext
  rw [Finsupp.ext_iff]
  simp only [Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rfl

private theorem naturalCoefficient_vandermonde_cycles {r k : ℕ}
    (a : Fin r → ℕ) (w : Fin k → ℕ) :
    naturalCoefficient a (vandermonde r * ∏ t, powerSum r (w t)) =
      (signedCycleAssignments a w : ℂ) := by
  classical
  rw [vandermonde_monomial_sum, Finset.sum_mul]
  change (∑ σ : Equiv.Perm (Fin r), _ : Alphabet r).coeff _ = _
  rw [MvPolynomial.coeff_sum]
  simp only [signedCycleAssignments, Int.cast_sum, Int.cast_mul, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp only [h, one_smul, Units.val_one, Int.cast_one, one_mul]
    exact monomial_cycle_assignments a _ w
  · simp only [h, Units.neg_smul, one_smul, neg_mul, MvPolynomial.coeff_neg,
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, one_mul]
    exact congrArg Neg.neg (monomial_cycle_assignments a _ w)

/-- The cycle lengths, in the order used to perform the finite coefficient computation. -/
def s4CycleWord : Fin 5 → List ℕ := ![[1,1,1,1], [2,1,1], [2,2], [3,1], [4]]

def s4RowWord : Fin 5 → List ℕ := ![[4], [3,1], [2,2], [2,1,1], [1,1,1,1]]

private theorem s4_power_sum (r : ℕ) (j : Fin 5) :
    partitionPowerSum r (s4Cycles j) =
      ∏ t : Fin (s4CycleWord j).length, powerSum r ((s4CycleWord j).get t) := by
  rw [partitionPowerSum_eq_multiset_prod]
  change _ = ∏ t : Fin (s4CycleWord j).length, powerSum r ((s4CycleWord j)[t.val])
  rw [Fin.prod_univ_fun_getElem]
  fin_cases j <;>
    simp [s4Cycles, Specs.AdvancedFiniteGroupRepresentations.s4Cycles,
      Specs.AdvancedFiniteGroupRepresentations.s4Shapes, s4CycleWord]

private theorem s4_character_coefficient (i j : Fin 5) :
    s4Character i j =
      (signedCycleAssignments (fun t : Fin 4 => (s4RowWord i).getD t.val 0 + staircase 4 t)
        (s4CycleWord j).get : ℂ) := by
  change spechtCharacterAtCycle (s4Shapes i) (s4Cycles j) = _
  rw [spechtCharacterAtCycle_eq_spechtCycleCharacter,
    ← frobeniusCoefficient_eq_spechtCycleCharacter 4 (by decide) (by decide)]
  change naturalCoefficient (shiftedPartition 4 (s4Shapes i))
    (vandermonde 4 * partitionPowerSum 4 (s4Cycles j)) = _
  rw [s4_power_sum, naturalCoefficient_vandermonde_cycles]
  congr 2
  funext t
  change rowLength (s4Shapes i) t.val + staircase 4 t = _
  rw [rowLength_eq_getD]
  exact congrArg (fun l : List ℕ => l.getD t.val 0 + staircase 4 t) (s4_labels.1 i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem s4_integer_computation (i j : Fin 5) :
    signedCycleAssignments (fun t : Fin 4 => (s4RowWord i).getD t.val 0 + staircase 4 t)
      (s4CycleWord j).get = s4Table i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem s4_character_table : Specs.AdvancedFiniteGroupRepresentations.s4_character_tableType := by
  intro i j
  exact (s4_character_coefficient i j).trans
    (congrArg (fun z : ℤ => (z : ℂ)) (s4_integer_computation i j))

private theorem s4_centralizer_factor (j : Fin 5) :
    centralizerFactor (s4Cycles j) = s4Centralizers j := by
  fin_cases j <;>
    norm_num [centralizerFactor, Specs.AdvancedFiniteGroupRepresentations.centralizerFactor,
      cycleMultiplicity, Specs.AdvancedFiniteGroupRepresentations.cycleMultiplicity,
      s4Cycles, Specs.AdvancedFiniteGroupRepresentations.s4Cycles,
      Specs.AdvancedFiniteGroupRepresentations.s4Shapes,
      s4Centralizers, Specs.AdvancedFiniteGroupRepresentations.s4Centralizers]

theorem s4_class_cardinalities :
    Specs.AdvancedFiniteGroupRepresentations.s4_class_cardinalitiesType := by
  intro j g hg
  constructor
  · exact (conjugacyClass_card_of_type (s4Cycles j) g hg).trans (by
      rw [s4_centralizer_factor]
      fin_cases j <;> norm_num [s4Centralizers, s4ClassSizes,
        Specs.AdvancedFiniteGroupRepresentations.s4Centralizers,
        Specs.AdvancedFiniteGroupRepresentations.s4ClassSizes])
  · exact (centralizer_card_of_type (s4Cycles j) g hg).trans (s4_centralizer_factor j)

theorem s4_row_gram : Specs.AdvancedFiniteGroupRepresentations.s4_row_gramType := by
  intro i k
  change (∑ j, (s4ClassSizes j : ℂ) * s4Character i j * star (s4Character k j)) = _
  have hc : ∀ i j, s4Character i j = (s4Table i j : ℂ) := s4_character_table
  simp only [hc]
  fin_cases i <;> fin_cases k <;>
    norm_num [Fin.sum_univ_succ, s4ClassSizes, Specs.AdvancedFiniteGroupRepresentations.s4ClassSizes,
      s4Table, Specs.AdvancedFiniteGroupRepresentations.s4Table, Matrix.of_apply]

theorem s4_column_gram : Specs.AdvancedFiniteGroupRepresentations.s4_column_gramType := by
  intro j k
  change (∑ i, s4Character i j * star (s4Character i k)) = _
  have hc : ∀ i j, s4Character i j = (s4Table i j : ℂ) := s4_character_table
  simp only [hc]
  fin_cases j <;> fin_cases k <;>
    norm_num [Fin.sum_univ_succ, s4Centralizers, Specs.AdvancedFiniteGroupRepresentations.s4Centralizers,
      s4Table, Specs.AdvancedFiniteGroupRepresentations.s4Table, Matrix.of_apply]

end AdvancedFiniteGroupRepresentations
