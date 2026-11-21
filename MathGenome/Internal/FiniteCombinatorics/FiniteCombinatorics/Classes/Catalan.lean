import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.Catalan

/-! The Catalan family of W21, counted by its actual words.
The library count is transported from Dyck words of the prescribed semilength;
the explicit letter bijection supplies the balanced-parenthesis interpretation.
-/

namespace FiniteCombinatorics.Classes.Catalan

open Specs.FiniteCombinatorics.Classes.Catalan

theorem path_conditions : PathConditions := by
  intro n p
  refine ⟨p.property, p.val.count_U_eq_count_D.symm.trans p.property, ?_, ?_⟩
  · rw [← p.val.two_mul_semilength_eq_length, p.property]
  · intro i
    exact sub_nonneg.mpr (Int.ofNat_le.mpr (p.val.count_D_le_count_U i))

private theorem count_letter (l : List DyckStep) (s : DyckStep) :
    (l.map parenthesisLetter).count (parenthesisLetter s) = l.count s :=
  List.count_map_of_injective l parenthesisLetter parenthesisLetter.injective s

private theorem count_step (l : List Parenthesis) (s : Parenthesis) :
    (l.map parenthesisLetter.symm).count (parenthesisLetter.symm s) = l.count s :=
  List.count_map_of_injective l parenthesisLetter.symm parenthesisLetter.symm.injective s

private def toParenthesis {n : ℕ} (p : DyckPath n) : BalancedParenthesis n :=
  ⟨p.val.toList.map parenthesisLetter, by
    refine ⟨?_, ?_, ?_⟩
    · exact (count_letter _ .U).trans p.property
    · exact (count_letter _ .D).trans (p.val.count_U_eq_count_D.symm.trans p.property)
    · intro i
      simpa only [← List.map_take, ← show parenthesisLetter DyckStep.D = Parenthesis.closing
        from rfl, ← show parenthesisLetter DyckStep.U = Parenthesis.opening from rfl,
        count_letter] using p.val.count_D_le_count_U i⟩

private def toDyck {n : ℕ} (w : BalancedParenthesis n) : DyckPath n :=
  ⟨⟨w.val.map parenthesisLetter.symm, by
      change (w.val.map parenthesisLetter.symm).count (parenthesisLetter.symm .opening) =
        (w.val.map parenthesisLetter.symm).count (parenthesisLetter.symm .closing)
      rw [count_step, count_step, w.property.1, w.property.2.1], by
      intro i
      simpa only [← List.map_take,
        ← show parenthesisLetter.symm Parenthesis.closing = DyckStep.D from rfl,
        ← show parenthesisLetter.symm Parenthesis.opening = DyckStep.U from rfl,
        count_step] using w.property.2.2 i⟩, by
    change (w.val.map parenthesisLetter.symm).count (parenthesisLetter.symm .opening) = n
    rw [count_step, w.property.1]⟩

private def wordEquiv (n : ℕ) : DyckPath n ≃ BalancedParenthesis n where
  toFun := toParenthesis
  invFun := toDyck
  left_inv p := by
    apply Subtype.ext
    apply DyckWord.ext
    simp [toDyck, toParenthesis, List.map_map]
  right_inv w := by
    apply Subtype.ext
    simp [toDyck, toParenthesis, List.map_map]

theorem parenthesis_bijection : ParenthesisBijection := by
  intro n
  exact ⟨wordEquiv n, fun _ => rfl⟩

theorem parenthesis_finite : ParenthesisFinite := by
  intro n
  exact Finite.of_equiv (DyckPath n) (wordEquiv n)

theorem common_count : CommonCount := by
  intro n
  exact Nat.card_congr (wordEquiv n)

private theorem count_eq_catalan (n : ℕ) : C n = catalan n := by
  unfold C
  rw [Nat.card_eq_fintype_card]
  exact DyckWord.card_dyckWord_semilength_eq_catalan n

theorem count_zero : CountZero := by
  change C 0 = 1
  rw [count_eq_catalan, catalan_zero]

theorem count_recurrence : CountRecurrence := by
  intro n
  simp only [count_eq_catalan]
  rw [catalan_succ]
  exact (Finset.sum_range (fun i => catalan i * catalan (n - i))).symm

theorem count_formula : CountFormula := by
  intro n
  rw [count_eq_catalan, catalan_eq_centralBinom_div, Nat.centralBinom]

theorem count_multiplication : CountMultiplication := by
  intro n
  rw [count_eq_catalan]
  exact succ_mul_catalan_eq_centralBinom n

theorem empty_words : EmptyWords := by
  have hd : ∀ p : DyckPath 0, p.val.toList = [] := by
    intro p
    apply List.length_eq_zero_iff.mp
    rw [← p.val.two_mul_semilength_eq_length, p.property, Nat.mul_zero]
  refine ⟨⟨⟨0, rfl⟩, rfl⟩, hd, ⟨⟨[], by simp⟩, rfl⟩, ?_⟩
  intro w
  have he : (wordEquiv 0 ((wordEquiv 0).symm w)).val = [] := by
    change (((wordEquiv 0).symm w).val.toList.map parenthesisLetter) = []
    rw [hd]
    rfl
  simpa using he

end FiniteCombinatorics.Classes.Catalan
