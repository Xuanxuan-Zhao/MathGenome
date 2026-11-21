import MathGenome.Internal.Specs.D05.Foundations.StarsBars
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-! The stars-and-bars count of paper.tex:352.
The multiset/tuple equivalence records the multiplicity of each coordinate index.
It counts the full solution set, allowing zero entries in every position.
-/
namespace D05.Foundations.StarsBars
open D05.Foundations

/-- A tuple is a multiset of coordinate indices, with each index repeated its entry. -/
noncomputable def tuplesEquivSym (n p : ℕ) :
    NonnegativeTuples n p ≃ Sym (Fin n) p :=
  (Sym.equivNatSumOfFintype (Fin n) p).symm

/-- The solution set is finite, even though each coordinate ranges over `ℕ`. -/
instance (n p : ℕ) : Finite (NonnegativeTuples n p) :=
  Finite.of_equiv (Sym (Fin n) p) (tuplesEquivSym n p).symm

/-- A version including the zero-variable case, with natural subtraction. -/
theorem tuples_card (n p : ℕ) :
    Nat.card (NonnegativeTuples n p) = (n + p - 1).choose p := by
  classical
  rw [Nat.card_congr (tuplesEquivSym n p), Nat.card_eq_fintype_card,
    Sym.card_sym_eq_choose, Fintype.card_fin]

theorem stars_bars : D05StarsBarsSpec.stars_bars := by
  intro n p _hn
  exact tuples_card n p

theorem zero_variables_zero : D05StarsBarsSpec.zero_variables_zero := by
  change Nat.card (NonnegativeTuples 0 0) = 1
  simpa using tuples_card 0 0

theorem zero_variables_pos : D05StarsBarsSpec.zero_variables_pos := by
  intro p hp
  rw [tuples_card]
  exact Nat.choose_eq_zero_of_lt (by omega)

end D05.Foundations.StarsBars
