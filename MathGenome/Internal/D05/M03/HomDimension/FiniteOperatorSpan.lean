import MathGenome.Internal.Specs.D05.M03.HomDimension.FiniteOperatorSpan
import MathGenome.Internal.D05.M03.HomDimension
import MathGenome.Internal.D05.M02.SubspaceDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Finite selection by adjoining a generator outside the current span.
The recursion decreases the remaining span dimension. -/

namespace D05.M03.HomDimension.FiniteOperatorSpan

open Submodule

section Selection

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

/-- A new generator gives strict inclusion of spans, hence strict dimension growth. -/
theorem finrank_span_insert_gt (s : Set W) (x : W) (hx : x ∉ span K s) :
    Module.finrank K (span K s) < Module.finrank K (span K (insert x s)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (span_mono (Set.subset_insert x s)) ?_
  intro heq
  exact hx (heq ▸ subset_span (Set.mem_insert x s))

/-- Greedy completion of any partial selection whose cardinality is bounded by
its span dimension. At each recursive call the remaining dimension decreases. -/
theorem complete_finite_selection (F : Set W) (s : Finset W)
    (hsF : (s : Set W) ⊆ F)
    (hcard : s.card ≤ Module.finrank K (span K (s : Set W))) :
    ∃ t : Finset W, (t : Set W) ⊆ F ∧ span K (t : Set W) = span K F ∧
      t.card ≤ Module.finrank K (span K F) := by
  classical
  generalize hk : Module.finrank K (span K F) -
    Module.finrank K (span K (s : Set W)) = k
  induction k using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases heq : span K (s : Set W) = span K F
    · exact ⟨s, hsF, heq, heq ▸ hcard⟩
    · have hout : ∃ x ∈ F, x ∉ span K (s : Set W) := by
        by_contra! h
        exact heq (le_antisymm (span_mono hsF) (span_le.mpr h))
      obtain ⟨x, hxF, hx⟩ := hout
      have hxs : x ∉ s := fun h => hx (subset_span h)
      have hsub : (↑((insert x s : Finset W)) : Set W) ⊆ F := by
        simpa only [Finset.coe_insert] using Set.insert_subset hxF hsF
      have hgrowth := finrank_span_insert_gt (s : Set W) x hx
      have hle : Module.finrank K (span K (↑((insert x s : Finset W)) : Set W)) ≤
          Module.finrank K (span K F) := Submodule.finrank_mono (span_mono hsub)
      have hcard' : ((insert x s : Finset W)).card ≤
          Module.finrank K (span K (↑((insert x s : Finset W)) : Set W)) := by
        rw [Finset.card_insert_of_notMem hxs]
        rw [Finset.coe_insert]
        exact Nat.add_one_le_iff.mpr (lt_of_le_of_lt hcard hgrowth)
      have hdecrease : Module.finrank K (span K F) -
          Module.finrank K (span K (↑((insert x s : Finset W)) : Set W)) < k := by
        rw [Finset.coe_insert] at hle ⊢
        omega
      exact ih _ hdecrease ((insert x s : Finset W)) hsub hcard' rfl

/-- Start with no generators. The zero-span case must return the empty subfamily
because the cardinality bound then forces cardinality zero. -/
theorem exists_finite_spanning_subfamily (F : Set W) :
    ∃ s : Finset W, (s : Set W) ⊆ F ∧ span K (s : Set W) = span K F ∧
      s.card ≤ Module.finrank K (span K F) ∧ (span K F = ⊥ → s = ∅) := by
  obtain ⟨s, hsF, hs, hcard⟩ := complete_finite_selection (K := K) F ∅ (by simp) (by simp)
  refine ⟨s, hsF, hs, hcard, ?_⟩
  intro hzero
  rw [hzero, finrank_bot] at hcard
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)

end Selection

theorem span_dimension_increases :
    Specs.D05.M03.HomDimension.FiniteOperatorSpan.span_dimension_increases := by
  intro K V _ _ _ _ s T hT
  exact finrank_span_insert_gt (s : Set (Module.End K V)) T hT

theorem finite_operator_span :
    Specs.D05.M03.HomDimension.FiniteOperatorSpan.finite_operator_span := by
  intro K V _ _ _ _ n hn F
  have hend : Module.finrank K (Module.End K V) = n ^ 2 := by
    rw [D05.M03.HomDimension.hom_dimension (Module.finBasis K V) (Module.finBasis K V),
      hn, pow_two]
  obtain ⟨s, hsF, hs, hcard, hzero⟩ := exists_finite_spanning_subfamily (K := K) F
  refine ⟨s, hsF, hs, hcard, ?_, hzero⟩
  exact (D05.M02.SubspaceDimension.subspace_dimension (span K F) (n ^ 2) hend).2.2.1

end D05.M03.HomDimension.FiniteOperatorSpan
