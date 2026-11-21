import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch02.SpikeCounterexample
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch02
open Specs.ProbabilityFoundations.Ch02.SpikeCounterexample

instance spike_probability : IsProbabilityMeasure spikeMeasure := by
  constructor
  rw [spikeMeasure, comap_subtype_coe_apply measurableSet_Ioo]
  simp only [Set.image_univ, Subtype.range_coe]
  change volume (Set.Ioo (0 : ℝ) 1) = 1
  rw [Real.volume_Ioo]
  norm_num

theorem spike_measurable : measurableType := by
  intro p n
  exact measurable_const.indicator (measurableSet_lt measurable_subtype_coe measurable_const)

theorem spike_pointwise : pointwiseType := by
  intro p hp x
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds x.property.1)
  apply tendsto_const_nhds.congr'
  filter_upwards [h] with n hn
  simp only [spike, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right (not_lt.mpr hn.le)]

theorem spike_almostSure : almostSureType := by
  intro p hp
  exact ae_of_all _ (spike_pointwise p hp)

theorem spike_in_probability : probabilityConvergenceType := by
  intro p hp hP
  exact almostSure_implies_probability spikeMeasure (spike p) (fun _ => 0)
    (spike_measurable p) measurable_const (spike_almostSure p hp)

theorem spike_memLp : memLpType := by
  intro p hp n
  exact (memLp_const (((n : ℝ) + 1) ^ (1 / p))).indicator
    ((measurableSet_lt measurable_subtype_coe measurable_const).nullMeasurableSet)

/-- The shrinking interval has its usual Lebesgue length on the subtype. -/
theorem spike_event_measure (n : ℕ) :
    spikeMeasure {x : Sample | (x : ℝ) < 1 / ((n : ℝ) + 1)} =
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hb : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one hn).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [spikeMeasure, comap_subtype_coe_apply measurableSet_Ioo]
  have he : Subtype.val '' {x : Sample | (x : ℝ) < 1 / ((n : ℝ) + 1)} =
      Set.Ioo 0 (1 / ((n : ℝ) + 1)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property.1, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1, hx.2.trans_le hb⟩, hx.2, rfl⟩
  rw [he, Real.volume_Ioo, sub_zero]

theorem spike_moment : momentType := by
  intro p hp n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm : MeasurableSet {x : Sample | (x : ℝ) < 1 / ((n : ℝ) + 1)} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have he : (fun x => |spike p n x| ^ p) =
      {x : Sample | (x : ℝ) < 1 / ((n : ℝ) + 1)}.indicator (fun _ => (n : ℝ) + 1) := by
    funext x
    by_cases hx : (x : ℝ) < 1 / ((n : ℝ) + 1)
    · simp only [spike, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hx,
        abs_of_nonneg (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le,
        one_div_mul_cancel hp.ne', Real.rpow_one]
    · simp only [spike, Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hx, abs_zero,
        Real.zero_rpow hp.ne']
  rw [he, integral_indicator hm, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, spike_event_measure,
    ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr hn)), smul_eq_mul]
  exact one_div_mul_cancel hn.ne'

theorem spike_not_lp_convergence : notLpConvergenceType := by
  intro p hp hc
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_zero, spike_moment p hp] using hc
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

end ProbabilityFoundations.Ch02
