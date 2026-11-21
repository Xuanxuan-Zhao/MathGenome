import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.FiniteStopCounterexample
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.SymmetricInfiniteMeans
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Batteries.Tactic.OpenPrivate

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-! The first counterexample in paper.tex W42. Independent fair integer moves
realize the canonical zero-started walk; translation transfers W21 to its hit of +1. -/

namespace P207.FiniteStopCounterexample
noncomputable section

open private cumulativePath integerLaw_cumulative measurable_cumulativePath
  from MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.IntegerHitting

theorem canonical_law : law.map path = Walk.integerLaw (1 / 2) (by norm_num) (by norm_num) 0 := by
  rw [integerLaw_cumulative]
  congr 1
  funext ω n
  exact (zero_add (path ω n)).symm

private theorem move_map : move.toMeasure =
    (Walk.ruinCoin (1 / 2) (by norm_num) (by norm_num)).toMeasure.map
      (fun b => if b then (1 : ℤ) else -1) := by
  simp only [move, Walk.integerKernel, zero_add, zero_sub]
  exact (PMF.toMeasure_map _ _ (by fun_prop)).symm

private theorem move_norm : ∀ᵐ (z : ℤ) ∂move.toMeasure, |(z : ℝ)| = 1 := by
  rw [move_map]
  apply (ae_map_iff (by fun_prop) (Set.to_countable _).measurableSet).mpr
  exact ae_of_all _ fun b => by cases b <;> norm_num

private theorem increment_norm (n : ℕ) : ∀ᵐ ω ∂law, |(ω n : ℝ)| = 1 := by
  have he : law.map (fun ω => ω n) = move.toMeasure := Measure.infinitePi_map_eval _ n
  have h := move_norm
  rw [← he] at h
  exact (ae_map_iff (measurable_pi_apply n).aemeasurable (Set.to_countable _).measurableSet).mp h

private theorem increment_integrable (n : ℕ) : Integrable (fun ω => (ω n : ℝ)) law := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (measurable_pi_apply n)).aestronglyMeasurable)
  filter_upwards [increment_norm n] with ω hω
  change |(ω n : ℝ)| ≤ 1
  rw [hω]

private theorem increment_mean (n : ℕ) : (∫ ω, (ω n : ℝ) ∂law) = 0 := by
  rw [← integral_map (by fun_prop : Measurable (fun ω : ℕ → ℤ => ω n)).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun z : ℤ => (z : ℝ)) (law.map (fun ω => ω n)))]
  rw [show law.map (fun ω => ω n) = move.toMeasure from Measure.infinitePi_map_eval _ n,
    move_map, integral_map (by fun_prop) (by fun_prop)]
  rw [PMF.integral_eq_sum]
  norm_num [Fintype.sum_bool, Walk.ruinCoin, PMF.ofFintype_apply]

@[instance_reducible] private def past (n : ℕ) : MeasurableSpace (ℕ → ℤ) :=
  ⨆ k ∈ {k : ℕ | k < n}, MeasurableSpace.comap (fun ω : ℕ → ℤ => ω k) inferInstance

private theorem eval_past (n k : ℕ) (hk : k < n) :
    Measurable[past n] (fun ω : ℕ → ℤ => ω k) :=
  measurable_iff_comap_le.mpr (le_iSup_of_le k (le_iSup_of_le hk le_rfl))

private theorem natural_le_past (n : ℕ) : filtration n ≤ past n := by
  apply iSup₂_le
  intro j hj
  apply Measurable.comap_le
  change Measurable[past n] (fun ω => (path ω j : ℝ))
  simp only [path, Int.cast_sum]
  apply Finset.measurable_sum
  intro k hk
  exact (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (eval_past n k (lt_of_lt_of_le (Finset.mem_range.mp hk) hj))

private theorem increment_indep (n : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → ℤ => (ω n : ℝ)) inferInstance)
      (filtration n) law := by
  have hi : iIndepFun (fun n (ω : ℕ → ℤ) => ω n) law :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint (fun k => (measurable_pi_apply k).comap_le) hi
    (S := {n}) (T := {k | k < n}) (by simp)
  simp only [iSup_singleton] at h
  apply indep_of_indep_of_le h _ (natural_le_past n)
  exact ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
    (measurable_iff_comap_le.mpr le_rfl)).comap_le

private theorem adapted_process : Adapted filtration process :=
  P207.adapted_naturalFiltration process measurable_process

private theorem process_integrable (n : ℕ) : Integrable (process n) law := by
  change Integrable (fun ω => (path ω n : ℝ)) law
  simp only [path, Int.cast_sum]
  exact integrable_finsetSum _ (fun k _ => increment_integrable k)

private theorem process_step (n : ℕ) (ω : ℕ → ℤ) :
    process (n + 1) ω = process n ω + (ω n : ℝ) := by
  simp [process, path, Finset.sum_range_succ]

theorem martingale : P207.IsMartingale process filtration law := by
  refine ⟨adapted_process, process_integrable, fun n => ?_⟩
  have hz : law[(fun ω : ℕ → ℤ => (ω n : ℝ)) | filtration n] =ᵐ[law] fun _ => (0 : ℝ) := by
    have h := condExp_indep_eq (by fun_prop : Measurable (fun ω : ℕ → ℤ => (ω n : ℝ))).comap_le
      (filtration.le n) (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable (increment_indep n)
    simpa only [increment_mean n] using h
  have he : process (n + 1) = process n + (fun ω : ℕ → ℤ => (ω n : ℝ)) := by
    funext ω; exact process_step n ω
  rw [he]
  have ha := condExp_add (process_integrable n) (increment_integrable n) (filtration n)
  have hs := condExp_of_stronglyMeasurable (filtration.le n)
    (adapted_process.stronglyAdapted n) (process_integrable n)
  filter_upwards [ha, hz] with ω hω hzω
  simpa only [Pi.add_apply, hs, hzω, add_zero] using hω

/-- Translation by minus one identifies the two first-entrance times pointwise. -/
private theorem stop_translation (ω : ℕ → ℤ) :
    stop ω = Markov.hittingTime {0} (cumulativePath (-1) ω) := by
  have he (n : ℕ) : cumulativePath (-1) ω n = 0 ↔ path ω n = 1 := by
    change -1 + path ω n = 0 ↔ path ω n = 1
    omega
  simp only [stop, Markov.hittingTime, hittingAfter, Markov.coordinate,
    Set.mem_singleton_iff, he]
  congr 1
  apply propext
  simp only [Set.mem_singleton_iff, he]

theorem stopping_time : P207.IsDiscreteStoppingTime filtration stop := by
  have he : stop = hittingAfter process {(1 : ℝ)} 0 := by
    funext ω
    have hc (n : ℕ) : process n ω = 1 ↔ path ω n = 1 := by
      unfold process
      exact_mod_cast (Iff.rfl : path ω n = 1 ↔ path ω n = 1)
    simp only [stop, Markov.hittingTime, hittingAfter, Markov.coordinate,
      Set.mem_singleton_iff, hc]
    congr 1
    apply propext
    simp only [Set.mem_singleton_iff, hc]
  rw [he]
  exact adapted_process.isStoppingTime_hittingAfter (measurableSet_singleton 1)

theorem stop_finite : ∀ᵐ ω ∂law, stop ω < ⊤ := by
  have h := (Walk.symmetric_times_almost_sure_finite (1 / 2) (by norm_num)
    (by norm_num) (by norm_num)).2.1
  rw [integerLaw_cumulative] at h
  have h' := (ae_map_iff (measurable_cumulativePath (-1)).aemeasurable
    (Markov.measurableSet_hittingTime_finite {0})).mp h
  simpa only [law, move, ← stop_translation] using h'

theorem stop_infinite_mean : (∫⁻ ω, ENat.toENNReal (stop ω) ∂law) = ⊤ := by
  have h := (Walk.symmetric_infinite_means (1 / 2) (by norm_num)
    (by norm_num) (by norm_num)).2.1
  have hm : Measurable (fun ω : ℕ → ℤ => ENat.toENNReal (Markov.hittingTime {0} ω)) := by
    simp_rw [← Markov.hittingDuration_eq_toENNReal]
    apply Measurable.tsum
    intro n
    exact Measurable.ite (Markov.measurableSet_hittingTime_gt {0} n)
      measurable_const measurable_const
  rw [integerLaw_cumulative, lintegral_map hm (measurable_cumulativePath (-1))] at h
  simpa only [law, move, ← stop_translation] using h

theorem terminal_one : ∀ᵐ ω ∂law, terminal ω = 1 := by
  filter_upwards [stop_finite] with ω hω
  have hm := hittingAfter_mem_set_of_ne_top (u := Markov.coordinate) (s := {(1 : ℤ)})
    (n := 0) (ω := path ω) (ne_of_lt hω)
  change path ω (stop ω).untopA = 1 at hm
  simp only [terminal, P207.fullStoppedValue, ne_of_lt hω, ↓reduceIte, process, hm,
    Int.cast_one]

theorem counterexample : Spec.counterexample := by
  have he : terminal =ᵐ[law] fun _ => (1 : ℝ) := terminal_one
  have ht : Integrable terminal law := (integrable_const (1 : ℝ)).congr he.symm
  have hi : (∫ ω, terminal ω ∂law) = 1 := by
    rw [integral_congr_ae terminal_one]
    simp
  have hzero : ∀ ω, process 0 ω = 0 := by intro ω; simp [process, path]
  have hz : (∫ ω, process 0 ω ∂law) = 0 := by simp only [hzero, integral_zero]
  refine ⟨canonical_law, martingale, ?_, stopping_time, stop_finite, stop_infinite_mean,
    hzero, terminal_one, ht, hi, hz, ?_⟩
  · apply ae_all_iff.mpr
    intro n
    filter_upwards [increment_norm n] with ω hω
    rw [process_step]
    simpa using hω
  · rw [hi, hz]
    norm_num

end
end P207.FiniteStopCounterexample
