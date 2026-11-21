import MathGenome.Internal.RealAnalysis.D11.Ch02.Caratheodory
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch02.NonadditiveOuterExample

/-! The constant-one cost on nonempty sets gives the required two-point example.
For subadditivity, a nonempty union supplies one term of cost one. For the
splitting test, every proper nonempty set and its complement both cost one,
so testing the whole space would require `1 = 2`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch02.NonadditiveOuterExample

open Specs.D11.Ch02.NonadditiveOuterExample (cost)

private theorem cost_mono : Monotone cost := by
  intro A B hAB
  classical
  by_cases hA : A = ∅
  · simp [cost, hA]
  · have hB : B ≠ ∅ := fun h => hA (subset_empty_iff.mp (h ▸ hAB))
    simp [cost, hA, hB]

private theorem cost_iUnion_le (E : ℕ → Set Bool) :
    cost (⋃ n, E n) ≤ ∑' n, cost (E n) := by
  classical
  by_cases h : (⋃ n, E n) = ∅
  · simp [cost, h]
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    have hn0 : E n ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨x, hn⟩
    calc
      cost (⋃ n, E n) = cost (E n) := by simp [cost, h, hn0]
      _ ≤ ∑' k, cost (E k) := ENNReal.le_tsum (f := fun k => cost (E k)) n

private noncomputable def exampleOuterMeasure : OuterMeasure Bool where
  measureOf := cost
  empty := by simp [cost]
  mono := fun h => cost_mono h
  iUnion_nat := fun E _ => cost_iUnion_le E

private theorem exampleOuterMeasure_apply (E : Set Bool) :
    exampleOuterMeasure E = cost E := rfl

private theorem measurable_iff (S : Set Bool) :
    Caratheodory.isMeasurable exampleOuterMeasure S ↔ S = ∅ ∨ S = univ := by
  classical
  constructor
  · intro hS
    by_contra h
    have h0 : S ≠ ∅ := fun h0 => h (Or.inl h0)
    have h1 : S ≠ univ := fun h1 => h (Or.inr h1)
    have hc : Sᶜ ≠ ∅ := by simpa using h1
    have hs := (Caratheodory.splitting_iff exampleOuterMeasure S).mp hS univ
    have hU : (univ : Set Bool) ≠ ∅ := Set.univ_nonempty.ne_empty
    rw [univ_inter, ← compl_eq_univ_sdiff] at hs
    simp only [exampleOuterMeasure_apply, cost,
      ite_eq_right hU, ite_eq_right h0, ite_eq_right hc] at hs
    norm_num at hs
  · rintro (rfl | rfl)
    · exact exampleOuterMeasure.isCaratheodory_empty
    · intro E
      simp only [inter_univ, sdiff_univ, measure_empty, add_zero]

theorem nonadditive_outer_example :
    Specs.D11.Ch02.NonadditiveOuterExample.nonadditive_outer_example := by
  classical
  refine ⟨exampleOuterMeasure, exampleOuterMeasure_apply, cost_mono,
    cost_iUnion_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · norm_num [exampleOuterMeasure_apply, cost, Set.ext_iff, Bool.forall_bool]
  · norm_num [exampleOuterMeasure_apply, cost, Set.ext_iff, Bool.forall_bool]
  · norm_num [exampleOuterMeasure_apply, cost, Set.ext_iff, Bool.forall_bool]
  · intro b
    cases b <;> norm_num [exampleOuterMeasure_apply, cost, Set.ext_iff,
      Bool.forall_bool]
  · exact measurable_iff
  · ext S
    change Caratheodory.isMeasurable exampleOuterMeasure S ↔ _
    simp only [measurable_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

end D11.Ch02.NonadditiveOuterExample
