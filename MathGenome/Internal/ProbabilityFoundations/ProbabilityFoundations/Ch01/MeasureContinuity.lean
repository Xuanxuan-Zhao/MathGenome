import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch01.MeasureContinuity
import Mathlib.Order.Interval.Set.Infinite

/-! Continuity of probability and general measures, and the counting-measure
counterexample to continuity from above without a finite member. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch01

universe u

/-- Countable subadditivity, in particular for any countable family of events. -/
theorem union_bound {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : ℕ → Set Ω) (_hs : ∀ n, MeasurableSet (s n)) :
    μ (⋃ n, s n) ≤ ∑' n, μ (s n) :=
  measure_iUnion_le s

/-- Continuity from below does not require a finite measure. -/
theorem continuity_from_below {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : ℕ → Set Ω) (A : Set Ω) (_hs : ∀ n, MeasurableSet (s n))
    (hm : Monotone s) (hA : (⋃ n, s n) = A) :
    Monotone (fun n => μ (s n)) ∧
      Tendsto (fun n => μ (s n)) atTop (𝓝 (μ A)) := by
  refine ⟨fun i j hij => measure_mono (hm hij), ?_⟩
  simpa only [hA, Function.comp_def] using
    (tendsto_measure_iUnion_atTop (μ := μ) hm)

/-- Only one member of a decreasing sequence needs to have finite measure. -/
theorem continuity_from_above {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : ℕ → Set Ω) (A : Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hm : Antitone s) (hA : (⋂ n, s n) = A) (hf : ∃ m, μ (s m) < ∞) :
    Antitone (fun n => μ (s n)) ∧
      Tendsto (fun n => μ (s n)) atTop (𝓝 (μ A)) := by
  refine ⟨fun i j hij => measure_mono (hm hij), ?_⟩
  simpa only [hA, Function.comp_def] using
    (tendsto_measure_iInter_atTop (μ := μ) (fun n => (hs n).nullMeasurableSet)
      hm (hf.imp fun _ h => h.ne))

theorem probability_union_bound {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ → Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) :
    P (⋃ n, s n) ≤ ∑' n, P (s n) :=
  union_bound P s hs

theorem probability_continuity_from_below {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ → Set Ω) (A : Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hm : Monotone s) (hA : (⋃ n, s n) = A) :
    Monotone (fun n => P (s n)) ∧
      Tendsto (fun n => P (s n)) atTop (𝓝 (P A)) :=
  continuity_from_below P s A hs hm hA

theorem probability_continuity_from_above {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : ℕ → Set Ω) (A : Set Ω)
    (hs : ∀ n, MeasurableSet (s n)) (hm : Antitone s) (hA : (⋂ n, s n) = A) :
    Antitone (fun n => P (s n)) ∧
      Tendsto (fun n => P (s n)) atTop (𝓝 (P A)) :=
  continuity_from_above P s A hs hm hA ⟨0, measure_lt_top P (s 0)⟩

/-- Every natural-number tail has infinite counting measure, although the tails
are decreasing measurable sets with empty intersection. Their measures therefore
fail to converge to the measure of that intersection. -/
theorem counting_tails_counterexample :
    (∀ n : ℕ, MeasurableSet (Set.Ici n)) ∧
    Antitone (fun n : ℕ => Set.Ici n) ∧
    (⋂ n : ℕ, Set.Ici n) = ∅ ∧
    (∀ n : ℕ, Measure.count (Set.Ici n) = ∞) ∧
    ¬ Tendsto (fun n : ℕ => Measure.count (Set.Ici n)) atTop
        (𝓝 (Measure.count (⋂ n : ℕ, Set.Ici n))) := by
  have hinter : (⋂ n : ℕ, Set.Ici n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro k hk
    exact Nat.not_succ_le_self k (Set.mem_iInter.mp hk (k + 1))
  have hcount (n : ℕ) : Measure.count (Set.Ici n) = ∞ :=
    Measure.count_apply_infinite (Set.Ici_infinite n)
  refine ⟨fun _ => Set.to_countable _ |>.measurableSet, ?_, hinter, hcount, ?_⟩
  · intro i j hij k hk
    exact hij.trans hk
  · intro hlim
    simp only [hcount, hinter, measure_empty] at hlim
    have hfalse : (∞ : ℝ≥0∞) = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
    exact ENNReal.top_ne_zero hfalse

end ProbabilityFoundations.Ch01
