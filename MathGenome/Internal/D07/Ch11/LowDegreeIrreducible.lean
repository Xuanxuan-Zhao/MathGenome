import MathGenome.Internal.Specs.D07.Ch11.LowDegreeIrreducible
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum

/-!
Small-degree irreducibility, K07.11.low_degree_irreducible.
The library criterion applies to arbitrary field polynomials, not only monic
ones. We translate its empty root multiset into nonzero evaluation at every point,
using nonvanishing from the positive degree. For the quartic example, positivity
of a rational square plus one rules out roots, while its displayed square is
a factorization into two nonunits of degree two.
-/

universe u

namespace D07.Ch11.LowDegreeIrreducible

open Polynomial
open Specs.D07.Ch11.LowDegreeIrreducible

theorem degree_one_irreducible : DegreeOneIrreducible.{u} := by
  intro F _ f hf
  exact Polynomial.irreducible_of_degree_eq_one hf

theorem degree_two_or_three_iff_no_root : DegreeTwoOrThreeIffNoRoot.{u} := by
  intro F _ f hf
  have hn : f.natDegree = 2 ∨ f.natDegree = 3 :=
    hf.imp Polynomial.natDegree_eq_of_degree_eq_some
      Polynomial.natDegree_eq_of_degree_eq_some
  have hn2 : 2 ≤ f.natDegree := hn.elim (fun h => by omega) (fun h => by omega)
  have hn3 : f.natDegree ≤ 3 := hn.elim (fun h => by omega) (fun h => by omega)
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hn2
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hn2 hn3,
    Multiset.eq_zero_iff_forall_notMem]
  simp only [Polynomial.mem_roots hf0, Polynomial.IsRoot]

theorem rational_quartic_counterexample : RationalQuarticCounterexample := by
  have hd : (X ^ 2 + 1 : Polynomial ℚ).degree = (2 : WithBot ℕ) := by
    simpa using Polynomial.degree_X_pow_add_C (R := ℚ) (by decide : 0 < 2) 1
  have hnu : ¬ IsUnit (X ^ 2 + 1 : Polynomial ℚ) := by
    intro hu
    have hzero := Polynomial.degree_eq_zero_of_isUnit hu
    rw [hd] at hzero
    norm_num at hzero
  change ((X ^ 2 + 1 : Polynomial ℚ) ^ 2).degree = (4 : WithBot ℕ) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.degree_pow, hd]
    norm_num
  · intro a
    have hpos : 0 < a ^ 2 + 1 := add_pos_of_nonneg_of_pos (sq_nonneg a) zero_lt_one
    simpa only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one] using pow_ne_zero 2 (ne_of_gt hpos)
  · intro hi
    have hu := hi.isUnit_or_isUnit (show
      (X ^ 2 + 1 : Polynomial ℚ) ^ 2 = (X ^ 2 + 1) * (X ^ 2 + 1) from pow_two _)
    exact hu.elim hnu hnu

end D07.Ch11.LowDegreeIrreducible
