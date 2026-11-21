import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.InfiniteCounterexample
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import Mathlib.Tactic.NormNum

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section

namespace D11.Ch07.InfiniteCounterexample

variable {𝕜 : Type} [RCLike 𝕜]

local notation "mL" => (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ volume))
local notation "μL" => Measure.completion (volume : Measure ℝ)

theorem movingInterval_measurable (n : ℕ) :
    NullMeasurableSet (movingInterval n) (volume : Measure ℝ) := by
  exact (measurableSet_Ico : MeasurableSet (Ico (n : ℝ) ((n : ℝ) + 1))).nullMeasurableSet

theorem measurable_sequence : Specs.D11.Ch07.InfiniteCounterexample.measurable_sequence := by
  intro 𝕜 _ _ n
  exact measurable_const.indicator (movingInterval_measurable n)

theorem interval_measure (n : ℕ) : μL (movingInterval n) = 1 := by
  simp [Measure.completion_apply, movingInterval, Real.volume_Ico]

theorem pointwise_convergence : Specs.D11.Ch07.InfiniteCounterexample.pointwise_convergence := by
  intro 𝕜 _ x
  obtain ⟨N, hN⟩ := exists_nat_gt x
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x ∉ movingInterval n := by
    intro hx
    exact (hN.trans_le (Nat.cast_le.mpr hn)).not_ge hx.1
  simp [movingIndicator, hx]

open D11.Ch07.ConvergenceDefinitions

theorem deviation_subset (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    deviationSet (movingIndicator (𝕜 := 𝕜) n) (fun _ => 0) ε ⊆ movingInterval n := by
  intro x hx
  by_contra h
  simp [deviationSet, movingIndicator, h, not_lt.mpr hε.le] at hx

theorem half_deviation_set (n : ℕ) :
    deviationSet (movingIndicator (𝕜 := 𝕜) n) (fun _ => 0) (1 / 2) = movingInterval n := by
  ext x
  by_cases hx : x ∈ movingInterval n <;> norm_num [deviationSet, movingIndicator, hx]

theorem half_deviation_measure : Specs.D11.Ch07.InfiniteCounterexample.half_deviation_measure := by
  intro 𝕜 _ n
  change μL (deviationSet (movingIndicator (𝕜 := 𝕜) n) (fun _ => 0) (1 / 2)) = 1
  change volume (deviationSet (movingIndicator (𝕜 := 𝕜) n) (fun _ => 0) (1 / 2)) = 1
  rw [half_deviation_set]
  exact interval_measure n

/-- Continuity from above is applied only after intersecting with the
finite-measure set; the half-lines themselves have infinite measure. -/
theorem finite_set_tail (A : Set ℝ)
    (hA : NullMeasurableSet A (volume : Measure ℝ)) (hfinite : volume A < ∞) :
    Tendsto (fun n : ℕ => volume (A ∩ Ici (n : ℝ))) atTop (𝓝 0) := by
  let T : ℕ → Set ℝ := fun n => A ∩ Ici (n : ℝ)
  have hm (n : ℕ) : NullMeasurableSet (T n) (volume : Measure ℝ) :=
    hA.inter (measurableSet_Ici.nullMeasurableSet (μ := (volume : Measure ℝ)))
  have ha : Antitone T := by
    intro n m hnm x hx
    exact ⟨hx.1, (Nat.cast_le.mpr hnm : (n : ℝ) ≤ (m : ℝ)).trans hx.2⟩
  have he : (⋂ n, T n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (x : ℝ)
    exact hn.not_ge (mem_iInter.mp hx n).2
  have hf : ∃ N, volume (T N) < ∞ :=
    ⟨0, (measure_mono inter_subset_left).trans_lt hfinite⟩
  simpa only [he, measure_empty, Function.comp_def, T] using
    tendsto_measure_iInter_atTop hm ha (hf.imp fun _ h => h.ne)

theorem local_convergence : Specs.D11.Ch07.InfiniteCounterexample.local_convergence := by
  intro 𝕜 _
  change ∀ A : Set ℝ, NullMeasurableSet A (volume : Measure ℝ) → volume A < ∞ →
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => volume (A ∩ deviationSet (movingIndicator (𝕜 := 𝕜) n) (fun _ => 0) ε))
        atTop (𝓝 0)
  intro A hA hfinite ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (finite_set_tail A hA hfinite)
  · intro n
    exact bot_le
  · intro n
    apply measure_mono
    rintro x ⟨hxA, hx⟩
    exact ⟨hxA, (deviation_subset n ε hε hx).1⟩

theorem no_global_convergence : Specs.D11.Ch07.InfiniteCounterexample.no_global_convergence := by
  intro 𝕜 _
  change ¬ @inMeasureConverges ℝ 𝕜 _ mL μL movingIndicator (fun _ => 0)
  intro h
  have hc : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 0) := by
    convert h (1 / 2) (by norm_num) using 1
    funext n
    exact (half_deviation_measure 𝕜 n).symm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)

theorem no_almost_uniform_convergence :
    Specs.D11.Ch07.InfiniteCounterexample.no_almost_uniform_convergence := by
  intro 𝕜 _
  change ¬ @almostUniformConverges ℝ 𝕜 _ mL μL movingIndicator (fun _ => 0)
  intro h
  obtain ⟨A, _, hA, hu⟩ := h (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := hu (1 / 2) (by norm_num)
  have hsub : movingInterval N ⊆ A := by
    intro x hx
    by_contra hxA
    have ht := hN N le_rfl x hxA
    norm_num [movingIndicator, hx] at ht
  have hmass : (1 : ℝ≥0∞) ≤ μL A := by
    rw [← interval_measure N]
    exact measure_mono hsub
  have hh : ENNReal.ofReal (1 / 2 : ℝ) ≤ 1 := by norm_num
  exact (not_lt_of_ge (hh.trans hmass)) hA

theorem infinite_mass : Specs.D11.Ch07.InfiniteCounterexample.infinite_mass := by
  exact Real.volume_univ

end D11.Ch07.InfiniteCounterexample
