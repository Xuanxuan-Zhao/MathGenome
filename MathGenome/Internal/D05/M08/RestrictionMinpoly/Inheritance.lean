import MathGenome.Internal.Specs.D05.M08.RestrictionMinpoly.Inheritance
import MathGenome.Internal.D05.M08.RestrictionMinpoly
import MathGenome.Internal.D05.M09.MinpolyCriterion
import MathGenome.Internal.D05.M10.Triangularization

/-! Inheritance under restriction and quotient, paper.tex:1236.
Minimal-polynomial divisibility transfers splitting and distinctness of roots;
the independently proved triangularization and eigenbasis criteria then apply. -/

noncomputable section

namespace D05.M08.RestrictionMinpoly.Inheritance

open Polynomial
open D05.M06.Invariant

theorem divisor_splits : Specs.D05.M08.RestrictionMinpoly.Inheritance.divisor_splits := by
  intro K _ p q hp hs hd
  exact hs.of_dvd hp hd

/-- Root multisets of divisors are submultisets. The ambient root multiset is
the finset `s`, so the divisor's roots have no repetitions, in any characteristic. -/
theorem divisor_distinct_linear_factors :
    Specs.D05.M08.RestrictionMinpoly.Inheritance.divisor_distinct_linear_factors := by
  intro K _ s q hd
  classical
  have hp : (∏ a ∈ s, (X - C a)) ≠ 0 := (monic_prod_X_sub_C id s).ne_zero
  have hs : (∏ a ∈ s, (X - C a)).Splits :=
    Splits.prod (fun a _ => Splits.X_sub_C a)
  have hr : q.roots ≤ s.val := by
    simpa only [roots_prod_X_sub_C] using roots.le_of_dvd hp hd
  have hn : q.roots.Nodup := Multiset.nodup_of_le hr s.nodup
  refine ⟨q.roots.toFinset, ?_, ?_⟩
  · intro a ha
    exact Multiset.mem_of_le hr (Multiset.mem_toFinset.mp ha)
  · simpa only [Finset.prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hn]
      using (hs.of_dvd hp hd).eq_prod_roots

theorem restriction_triangularizable :
    Specs.D05.M08.RestrictionMinpoly.Inheritance.restriction_triangularizable := by
  intro K V _ _ _ _ U T h ht
  apply M10.Triangularization.minpoly_splits_implies_triangular
  exact divisor_splits _ _ (Minpoly.ne_zero T)
    ((M10.Triangularization.triangularization T).2.mp ht)
    (restriction_minpoly_dvd U T h)

theorem quotient_triangularizable :
    Specs.D05.M08.RestrictionMinpoly.Inheritance.quotient_triangularizable := by
  intro K V _ _ _ _ U T h ht
  apply M10.Triangularization.minpoly_splits_implies_triangular
  exact divisor_splits _ _ (Minpoly.ne_zero T)
    ((M10.Triangularization.triangularization T).2.mp ht)
    (quotient_minpoly_dvd U T h)

theorem restriction_diagonalizable :
    Specs.D05.M08.RestrictionMinpoly.Inheritance.restriction_diagonalizable := by
  intro K V _ _ _ _ U T h ht
  apply (M09.MinpolyCriterion.diagonalizable_iff_distinct_linear_factors _).mpr
  obtain ⟨s, hs⟩ := (M09.MinpolyCriterion.diagonalizable_iff_distinct_linear_factors T).mp ht
  have hd := restriction_minpoly_dvd U T h
  rw [hs] at hd
  obtain ⟨t, _, he⟩ := divisor_distinct_linear_factors s _ hd
  refine ⟨t, ?_⟩
  have hm := Minpoly.monic (Specs.D05.M06.Invariant.restriction_value K V U T h)
  simpa only [hm.leadingCoeff, C_1, one_mul] using he

theorem quotient_diagonalizable :
    Specs.D05.M08.RestrictionMinpoly.Inheritance.quotient_diagonalizable := by
  intro K V _ _ _ _ U T h ht
  apply (M09.MinpolyCriterion.diagonalizable_iff_distinct_linear_factors _).mpr
  obtain ⟨s, hs⟩ := (M09.MinpolyCriterion.diagonalizable_iff_distinct_linear_factors T).mp ht
  have hd := quotient_minpoly_dvd U T h
  rw [hs] at hd
  obtain ⟨t, _, he⟩ := divisor_distinct_linear_factors s _ hd
  refine ⟨t, ?_⟩
  have hm := Minpoly.monic (Specs.D05.M06.Invariant.inducedMap_value K V U T h)
  simpa only [hm.leadingCoeff, C_1, one_mul] using he

end D05.M08.RestrictionMinpoly.Inheritance
