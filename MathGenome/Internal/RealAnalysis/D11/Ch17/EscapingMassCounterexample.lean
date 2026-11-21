import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.EscapingMassCounterexample
import MathGenome.Internal.RealAnalysis.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch07.ConvergenceDefinitions
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic.NormNum

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace D11.Ch17.EscapingMassCounterexample
open Specs.D11.Ch17.EscapingMassCounterexample (LebesgueReal lebesgue)
open D11.Ch17.UniformControls D11.Ch07.ConvergenceDefinitions

def movingIndicator : ℕ → LebesgueReal → ℝ :=
  Specs.D11.Ch17.EscapingMassCounterexample.movingIndicator_value

private def interval (n : ℕ) : Set LebesgueReal :=
  Specs.D11.Ch17.EscapingMassCounterexample.movingInterval n

private lemma interval_measurable (n : ℕ) : MeasurableSet (interval n) :=
  (measurableSet_Icc : MeasurableSet (Icc ((n + 1 : ℕ) : ℝ)
    (((n + 1 : ℕ) : ℝ) + 1))).nullMeasurableSet

private lemma interval_measure (n : ℕ) : lebesgue (interval n) = 1 := by
  change volume (Icc ((n + 1 : ℕ) : ℝ) (((n + 1 : ℕ) : ℝ) + 1)) = 1
  rw [Real.volume_Icc]
  simp

private lemma measurable_indicator (n : ℕ) : Measurable (movingIndicator n) :=
  measurable_const.indicator (interval_measurable n)

private lemma norm_indicator (n : ℕ) :
    (fun x => ENNReal.ofReal ‖movingIndicator n x‖) =
      (interval n).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext x
  change ENNReal.ofReal ‖(interval n).indicator (fun _ : LebesgueReal => (1 : ℝ)) x‖ = _
  by_cases hx : x ∈ interval n
  · simp only [Set.indicator_of_mem hx, norm_one, ENNReal.ofReal_one]
  · simp only [Set.indicator_of_notMem hx, norm_zero, ENNReal.ofReal_zero]

theorem integral_on_set : ∀ (n : ℕ) (A : Set LebesgueReal), MeasurableSet A →
    absoluteIntegral lebesgue (movingIndicator n) A = lebesgue (A ∩ interval n) := by
  intro n A hA
  rw [absoluteIntegral_formula, norm_indicator, lintegral_indicator (interval_measurable n)]
  simp [Measure.restrict_apply (interval_measurable n), inter_comm]

theorem norm_one (n : ℕ) :
    absoluteIntegral lebesgue (movingIndicator n) univ = 1 := by
  rw [integral_on_set n univ MeasurableSet.univ, univ_inter, interval_measure]

theorem measurable_integrable : integrableFamily lebesgue movingIndicator := by
  intro n
  refine ⟨measurable_indicator n, ?_⟩
  have h := norm_one n
  simpa [absoluteIntegral, Measure.restrict_univ, h] using
    (show absoluteIntegral lebesgue (movingIndicator n) univ < ∞ by rw [h]; simp)

theorem small_set_control : uiSmall lebesgue movingIndicator := by
  refine ⟨measurable_integrable, fun ε hε => ⟨ε, hε, ?_⟩⟩
  intro A hA hμA
  apply lt_of_le_of_lt _ hμA
  apply iSup_le
  intro n
  rw [integral_on_set n A hA]
  exact measure_mono inter_subset_left

theorem pointwise_zero : pointwiseConverges movingIndicator (fun _ => 0) := by
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (show ℝ from x)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x ∉ interval n := by
    intro hx
    have hle : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    have hni : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_succ n)
    dsimp at hN
    exact (not_le.mpr hN) (hle.trans (hni.trans hx.1))
  change (0 : ℝ) = (interval n).indicator (fun _ : LebesgueReal => (1 : ℝ)) x
  exact (Set.indicator_of_notMem hx _).symm

/-- The mass of a finite-measure set in receding right half-lines vanishes. -/
private lemma finite_set_right_tail (A : Set LebesgueReal) (hA : MeasurableSet A)
    (hfin : lebesgue A < ∞) :
    Tendsto (fun n : ℕ => lebesgue (A ∩ {x | (n : ℝ) ≤ (show ℝ from x)}))
      atTop (𝓝 0) := by
  let S : ℕ → Set LebesgueReal := fun n => A ∩ {x | (n : ℝ) ≤ (show ℝ from x)}
  have hm (n : ℕ) : MeasurableSet (S n) :=
    hA.inter (measurableSet_Ici (a := (n : ℝ))).nullMeasurableSet
  have hanti : Antitone S := by
    intro i j hij x hx
    have hc : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    exact ⟨hx.1, hc.trans hx.2⟩
  have hempty : (⋂ n, S n) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt (show ℝ from x)
    exact (not_le.mpr hn) (mem_iInter.mp hx n).2
  have ht := tendsto_measure_iInter_atTop (μ := lebesgue)
    (fun n => (hm n).nullMeasurableSet) hanti
    ⟨0, ne_top_of_lt ((measure_mono inter_subset_left).trans_lt hfin)⟩
  simpa only [hempty, measure_empty, Function.comp_def] using ht

private lemma deviation_subset (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    deviationSet (movingIndicator n) (fun _ => 0) ε ⊆ interval n := by
  intro x hx
  by_contra hn
  have hz : movingIndicator n x = 0 := by
    change (interval n).indicator (fun _ : LebesgueReal => (1 : ℝ)) x = 0
    exact Set.indicator_of_notMem hn _
  have : ε < 0 := by simpa [deviationSet, hz] using hx
  exact (not_lt.mpr hε.le) this

private lemma deviation_eq (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    deviationSet (movingIndicator n) (fun _ => 0) ε = interval n := by
  apply Subset.antisymm (deviation_subset n ε hε)
  intro x hx
  have ho : movingIndicator n x = 1 := by
    change (interval n).indicator (fun _ : LebesgueReal => (1 : ℝ)) x = 1
    exact Set.indicator_of_mem hx _
  simpa [deviationSet, ho] using hε1

theorem deviation_measure_one (n : ℕ) :
    lebesgue (deviationSet (movingIndicator n) (fun _ => 0) (1/2)) = 1 := by
  rw [deviation_eq n (1/2) (by norm_num) (by norm_num), interval_measure]

theorem locally_in_measure_zero :
    locallyInMeasureConverges lebesgue movingIndicator (fun _ => 0) := by
  intro A hA hfin ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (finite_set_right_tail A hA hfin) (fun _ => bot_le)
  intro n
  apply measure_mono
  intro x hx
  have hi := deviation_subset n ε hε hx.2
  have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  exact ⟨hx.1, hn.trans hi.1⟩

theorem no_global_in_measure :
    ¬ inMeasureConverges lebesgue movingIndicator (fun _ => 0) := by
  intro h
  have ht := h (1/2) (by norm_num)
  simp_rw [deviation_measure_one] at ht
  have h10 : (1 : ℝ≥0∞) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact one_ne_zero h10

theorem no_L1_convergence :
    ¬ lpConverges lebesgue 1 movingIndicator (fun _ => 0) := by
  intro h
  have ht := h.2.2.2
  have heq (n : ℕ) : powerIntegral lebesgue 1 (fun x => movingIndicator n x - 0) = 1 := by
    simpa only [powerIntegral, Real.rpow_one, sub_zero, absoluteIntegral,
      Measure.restrict_univ] using norm_one n
  simp_rw [heq] at ht
  have h10 : (1 : ℝ≥0∞) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact one_ne_zero h10

theorem no_spatial_tails : ¬ spatialTails lebesgue movingIndicator := by
  intro h
  obtain ⟨E, hE, hfin, htail⟩ := h.2 (1/2) (by norm_num)
  have ht := finite_set_right_tail E hE hfin
  have hev : ∀ᶠ n : ℕ in atTop,
      lebesgue (E ∩ {x | (n : ℝ) ≤ (show ℝ from x)}) < (1/2 : ℝ≥0∞) :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n, hn⟩ := hev.exists
  have hin : lebesgue (interval n ∩ E) < (1/2 : ℝ≥0∞) := by
    apply lt_of_le_of_lt (measure_mono ?_) hn
    intro x hx
    have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
    exact ⟨hx.2, hnle.trans hx.1.1⟩
  have hout : lebesgue (interval n \ E) < (1/2 : ℝ≥0∞) := by
    have hle : absoluteIntegral lebesgue (movingIndicator n) Eᶜ ≤
        integralSup lebesgue movingIndicator Eᶜ := by
      exact le_iSup (fun i => absoluteIntegral lebesgue (movingIndicator i) Eᶜ) n
    have hlt := hle.trans_lt htail
    rw [integral_on_set n Eᶜ hE.compl] at hlt
    simpa only [inter_comm, sdiff_eq_compl_inter, ENNReal.ofReal_div_of_pos
      (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hlt
  have hsum := ENNReal.add_lt_add hin hout
  rw [measure_inter_add_sdiff _ hE, interval_measure] at hsum
  have hhalf : (1/2 : ℝ≥0∞) + (1/2 : ℝ≥0∞) = 1 := ENNReal.add_halves 1
  rw [hhalf] at hsum
  exact (lt_irrefl (1 : ℝ≥0∞)) hsum

end D11.Ch17.EscapingMassCounterexample
