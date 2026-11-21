import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.DiscontinuousModificationExample
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.Modifications
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Perfect

open MeasureTheory Set Filter
open scoped Topology

namespace ProbabilityFoundations.Ch05.DiscontinuousModificationExample

abbrev Interval := Time 1

noncomputable def X : Interval → Interval → ℝ := DiscontinuousModificationExampleSpec.spike

def Y : Interval → Interval → ℝ := DiscontinuousModificationExampleSpec.zero

theorem probability : IsProbabilityMeasure (volume : Measure Interval) := inferInstance

theorem coordinatesMeasurable :
    (∀ t, Measurable (X t)) ∧ (∀ t, Measurable (Y t)) := by
  classical
  constructor
  · intro t
    exact Measurable.ite (measurableSet_singleton t) measurable_const measurable_const
  · intro t
    exact measurable_const

theorem finiteAgreement (n : ℕ) (ts : Fin n → Interval) :
    volume (Set.range ts) = 0 ∧
    ∀ ω ∉ Set.range ts, (fun i => X (ts i) ω) = (fun i => Y (ts i) ω) := by
  classical
  refine ⟨(Set.finite_range ts).measure_zero _, ?_⟩
  intro ω hω
  funext i
  have hne : ω ≠ ts i := fun h => hω ⟨i, h.symm⟩
  simp [X, Y, DiscontinuousModificationExampleSpec.spike,
    DiscontinuousModificationExampleSpec.zero, hne]

theorem finiteDimensionalLaws (n : ℕ) (ts : Fin n → Interval) :
    Measure.map (fun ω i => X (ts i) ω) volume =
      Measure.map (fun ω i => Y (ts i) ω) volume := by
  apply Measure.map_congr
  have h : ∀ᵐ ω ∂(volume : Measure Interval), ω ∉ Set.range ts := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using (finiteAgreement n ts).1
  filter_upwards [h] with ω hω using (finiteAgreement n ts).2 ω hω

theorem pathsDiscontinuous (ω : Interval) :
    ¬ ContinuousAt (fun t => X t ω) ω := by
  classical
  have heq : (fun t => X t ω) = Function.update (fun _ : Interval => (0 : ℝ)) ω 1 := by
    funext t
    simp [X, DiscontinuousModificationExampleSpec.spike, Function.update_apply, eq_comm]
  rw [heq, continuousAt_update_same]
  intro h
  have : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds h
  exact zero_ne_one this

theorem zeroPathsContinuous (ω : Interval) : Continuous (fun t => Y t ω) :=
  continuous_const

theorem modification : IsModification (volume : Measure Interval) X Y := by
  intro t
  apply (mem_ae_iff_prob_eq_one
    (fixedTimeEqualityMeasurable X Y coordinatesMeasurable.1 coordinatesMeasurable.2 t)).1
  have h : ∀ᵐ ω ∂(volume : Measure Interval), ω ≠ t := by
    simp [ae_iff]
  filter_upwards [h] with ω hω
  simp [X, Y, DiscontinuousModificationExampleSpec.spike,
    DiscontinuousModificationExampleSpec.zero, hω]

theorem almostSurelyContinuous : HasAlmostSurelyContinuousPaths
    (volume : Measure Interval) Y := by
  exact ⟨Set.univ, MeasurableSet.univ, measure_univ, fun ω _ => zeroPathsContinuous ω⟩

theorem notIndistinguishable : ¬ Indistinguishable (volume : Measure Interval) X Y := by
  rintro ⟨G, _, hG, heq⟩
  have hEmpty : G = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have h := heq ω hω ω
    simp [X, Y, DiscontinuousModificationExampleSpec.spike,
      DiscontinuousModificationExampleSpec.zero] at h
  simp [hEmpty] at hG

end ProbabilityFoundations.Ch05.DiscontinuousModificationExample
