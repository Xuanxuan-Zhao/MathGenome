import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.DoublingExample
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.UniformIntegrability
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory

noncomputable section
namespace P207.Doubling

instance probability : IsProbabilityMeasure μ := by
  unfold μ
  infer_instance

theorem toss_law (k : ℕ) : Measure.map (toss k) μ = coinMeasure :=
  Measure.infinitePi_map_eval _ _

theorem independent_tosses : ProbabilityTheory.iIndepFun toss μ :=
  iIndepFun_infinitePi (P := fun _ : ℕ => coinMeasure)
    (X := fun (_ : ℕ) (b : Bool) => b) (fun _ => measurable_id)

theorem fair_coin : coinMeasure {true} = (2 : ℝ≥0∞)⁻¹ ∧
    coinMeasure {false} = (2 : ℝ≥0∞)⁻¹ := by
  unfold coinMeasure
  constructor
  · rw [bernoulliMeasure_apply_of_mem_of_notMem _
      (measurableSet_singleton _) (Set.mem_singleton _) (by decide : false ∉ ({true} : Set Bool))]
    apply (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (by norm_num)).mp
    norm_num
  · rw [bernoulliMeasure_apply_of_notMem_of_mem _
      (measurableSet_singleton _) (by decide : true ∉ ({false} : Set Bool)) (Set.mem_singleton _)]
    apply (ENNReal.toReal_eq_toReal_iff' ENNReal.coe_ne_top (by norm_num)).mp
    norm_num [unitInterval.coe_symm_eq]

theorem filtration_eq (n : ℕ) : filtration n =
    ⨆ k < n, MeasurableSpace.comap (toss k) inferInstance := rfl

@[simp] theorem allHeads_zero : allHeads 0 = Set.univ := by
  ext ω
  simp [allHeads]

@[simp] theorem M_zero (ω : Ω) : M 0 ω = 1 := by simp [M]

theorem M_nonneg (n : ℕ) (ω : Ω) : 0 ≤ M n ω := by
  exact Set.indicator_nonneg (fun _ _ => by positivity) ω

theorem measurable_toss {k n : ℕ} (hk : k < n) :
    Measurable[filtration n] (toss k) := by
  exact measurable_iff_comap_le.mpr (le_iSup₂_of_le k hk le_rfl)

theorem measurableSet_allHeads (n : ℕ) : MeasurableSet[filtration n] (allHeads n) := by
  simp only [allHeads, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  exact (measurable_toss hk) (measurableSet_singleton true)

theorem adapted : Adapted filtration M := by
  intro n
  exact measurable_const.indicator (measurableSet_allHeads n)

theorem integrable (n : ℕ) : Integrable (M n) μ := by
  exact (integrable_const _).indicator (filtration.le n _ (measurableSet_allHeads n))

theorem allHeads_measure (n : ℕ) : μ (allHeads n) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  have heq : allHeads n = Set.pi (Finset.range n) (fun _ => {true}) := by
    ext ω
    simp [allHeads, Set.pi, toss]
  rw [heq, μ, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  simp [fair_coin.1]

theorem expectation (n : ℕ) : (∫ ω, M n ω ∂μ) = 1 := by
  rw [M, integral_indicator (filtration.le n _ (measurableSet_allHeads n)),
    setIntegral_const, measureReal_def, allHeads_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [← mul_pow]
  norm_num

theorem abs_expectation (n : ℕ) : (∫ ω, |M n ω| ∂μ) = 1 := by
  simp_rw [abs_of_nonneg (M_nonneg n _)]
  exact expectation n

theorem allHeads_succ (n : ℕ) :
    allHeads (n + 1) = allHeads n ∩ {ω | toss n ω = true} := by
  ext ω
  simp only [allHeads, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h n (by omega)⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases hkn : k < n
    · exact h k hkn
    · have : k = n := by omega
      simpa [this] using hn

theorem measurable_toss_ambient (n : ℕ) : Measurable (toss n) := measurable_pi_apply n

theorem measure_toss_true (n : ℕ) : μ {ω | toss n ω = true} = (2 : ℝ≥0∞)⁻¹ := by
  change μ (toss n ⁻¹' {true}) = _
  rw [← Measure.map_apply (measurable_toss_ambient n) (measurableSet_singleton true),
    toss_law, fair_coin.1]

theorem indep_toss_past (n : ℕ) :
    Indep (MeasurableSpace.comap (toss n) inferInstance) (filtration n) μ := by
  have hdis : Disjoint ({n} : Set ℕ) {k | k < n} := by
    simp
  have hle : ∀ k : ℕ, MeasurableSpace.comap (toss k) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := fun k => (measurable_toss_ambient k).comap_le
  have h := indep_iSup_of_disjoint hle
    (show iIndep (fun k => MeasurableSpace.comap (toss k) inferInstance) μ from
      independent_tosses) hdis
  simpa [filtration, toss] using h

def headPayoff (n : ℕ) : Ω → ℝ :=
  {ω | toss n ω = true}.indicator (fun _ => 2)

theorem integrable_headPayoff (n : ℕ) : Integrable (headPayoff n) μ := by
  exact (integrable_const _).indicator
    ((measurable_toss_ambient n) (measurableSet_singleton true))

theorem expectation_headPayoff (n : ℕ) : (∫ ω, headPayoff n ω ∂μ) = 1 := by
  have hm : MeasurableSet {ω : Ω | toss n ω = true} :=
    (measurable_toss_ambient n) (measurableSet_singleton true)
  rw [headPayoff, integral_indicator hm, setIntegral_const,
    measureReal_def, measure_toss_true]
  norm_num

theorem condExp_headPayoff (n : ℕ) : μ[headPayoff n | filtration n] =ᵐ[μ] fun _ => 1 := by
  have hm : Measurable[MeasurableSpace.comap (toss n) inferInstance] (toss n) :=
    measurable_iff_comap_le.mpr le_rfl
  have hs : Measurable[MeasurableSpace.comap (toss n) inferInstance] (headPayoff n) :=
    measurable_const.indicator (hm (measurableSet_singleton true))
  have h := condExp_indep_eq (measurable_toss_ambient n).comap_le (filtration.le n)
    hs.stronglyMeasurable (indep_toss_past n)
  simpa only [expectation_headPayoff] using h

theorem M_succ (n : ℕ) : M (n + 1) = M n * headPayoff n := by
  ext ω
  rw [M, allHeads_succ]
  by_cases ha : ω ∈ allHeads n <;> by_cases hb : toss n ω = true <;>
    simp [M, headPayoff, ha, hb, pow_succ]

theorem martingale : P207.IsMartingale M filtration μ := by
  refine ⟨adapted, integrable, fun n => ?_⟩
  rw [M_succ]
  have h := condExp_mul_of_stronglyMeasurable_left (adapted.stronglyAdapted n)
    (by rw [← M_succ]; exact integrable (n + 1)) (integrable_headPayoff n)
  filter_upwards [h, condExp_headPayoff n] with ω hω hpω
  simpa only [Pi.mul_apply, hpω, mul_one] using hω

theorem allHeads_forever_null : μ (⋂ n, allHeads n) = 0 := by
  have ht : Tendsto (fun n => μ (allHeads n)) atTop (𝓝 0) := by
    simp_rw [allHeads_measure]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  apply le_antisymm _ bot_le
  exact ge_of_tendsto ht (Eventually.of_forall fun n =>
    measure_mono (Set.iInter_subset (fun n => allHeads n) n))

theorem ae_tendsto_zero : ∀ᵐ ω ∂μ, Tendsto (fun n => M n ω) atTop (𝓝 0) := by
  have hgood : ∀ᵐ ω ∂μ, ω ∉ ⋂ n, allHeads n := by
    rw [ae_iff]
    convert allHeads_forever_null using 1
    congr 1
    ext ω
    simp
  filter_upwards [hgood] with ω hω
  simp only [Set.mem_iInter, not_forall] at hω
  obtain ⟨n, hn⟩ := hω
  have he : (fun k => M k ω) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop n] with k hnk
    apply Set.indicator_of_notMem
    intro hk
    exact hn (fun i hi => hk i (hi.trans_le hnk))
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem tail_expectation_of_lt (n : ℕ) (R : ℝ) (hR : R < (2 : ℝ) ^ n) :
    (∫ ω, {ω | R < M n ω}.indicator (M n) ω ∂μ) = 1 := by
  have heq : {ω | R < M n ω}.indicator (M n) = M n := by
    ext ω
    by_cases ha : ω ∈ allHeads n
    · simp [M, ha, hR]
    · simp [M, ha]
  rw [heq, expectation]

theorem tail_expectation (R : ℝ) : ∃ n : ℕ, R < (2 : ℝ) ^ n ∧
    (∫ ω, {ω | R < M n ω}.indicator (M n) ω ∂μ) = 1 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
  exact ⟨n, hn, tail_expectation_of_lt n R hn⟩

theorem tailIntegral_eq_one (n : ℕ) (R : ℝ) (hR : R < (2 : ℝ) ^ n) :
    P207.Martingale.tailIntegral μ (M n) R = 1 := by
  rw [P207.Martingale.tailIntegral_eq_ofReal_integral μ (M n) (integrable n)]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (M_nonneg n _)]
  rw [tail_expectation_of_lt n R hR, ENNReal.ofReal_one]

theorem not_uniformIntegrable : ¬ P207.Martingale.SourceUniformIntegrable μ M := by
  intro h
  obtain ⟨R, hR⟩ := ENNReal.tendsto_atTop_zero.mp h.2 (2 : ℝ≥0∞)⁻¹ (by norm_num)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
  have hb : P207.Martingale.tailIntegral μ (M n) R ≤ (2 : ℝ≥0∞)⁻¹ :=
    (le_iSup (fun k => P207.Martingale.tailIntegral μ (M k) R) n).trans (hR R le_rfl)
  rw [tailIntegral_eq_one n R hn] at hb
  norm_num at hb

theorem not_tendsto_L1 (Y : Ω → ℝ) (hY : Integrable Y μ) :
    ¬ Tendsto (fun n => ∫ ω, |M n ω - Y ω| ∂μ) atTop (𝓝 0) := by
  intro ht
  have heq (n : ℕ) : eLpNorm (M n - Y) 1 μ =
      ENNReal.ofReal (∫ ω, |M n ω - Y ω| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm ((integrable n).sub hY).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((integrable n).sub hY)]
    rfl
  have htLp : Tendsto (fun n => eLpNorm (M n - Y) 1 μ) atTop (𝓝 0) := by
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  have hmY : TendstoInMeasure μ M atTop Y :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero htLp
  have hm0 : TendstoInMeasure μ M atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (integrable n).aestronglyMeasurable)
      ae_tendsto_zero
  have hY0 : Y =ᵐ[μ] fun _ => (0 : ℝ) := tendstoInMeasure_ae_unique hmY hm0
  have hdist (n : ℕ) : (∫ ω, |M n ω - Y ω| ∂μ) = 1 := by
    calc
      (∫ ω, |M n ω - Y ω| ∂μ) = ∫ ω, |M n ω| ∂μ := by
        apply integral_congr_ae
        filter_upwards [hY0] with ω hω
        simp only [hω, sub_zero]
      _ = 1 := abs_expectation n
  simp_rw [hdist] at ht
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  norm_num at this

end P207.Doubling
