import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.WaldSecond
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.WaldFirst
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.L2SummabilityConvergence

open MeasureTheory Filter
open scoped MeasureTheory Topology ENNReal
universe u
namespace P207.WaldSecond
variable {Ω : Type u} [m : MeasurableSpace Ω]

/-- Finite sums of the predictable masked increments. -/
noncomputable def maskedSum (M : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, ControlledIncrement.stoppedIncrement M τ k ω

omit m in
theorem maskedSum_increment (M : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ)
    (k : ℕ) :
    (fun ω => maskedSum M τ (k + 1) ω - maskedSum M τ k ω) =
      ControlledIncrement.stoppedIncrement M τ k := by
  funext ω
  simp [maskedSum, Finset.sum_range_succ]

theorem maskedSum_martingale (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ P)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ) :
    IsMartingale (maskedSum M τ) ℱ P := by
  have ha : Adapted ℱ (maskedSum M τ) := by
    intro n
    apply Finset.measurable_sum
    intro k hk
    have hkn := (Finset.mem_range.mp hk)
    exact (((hM.1 (k + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hkn)) le_rfl).sub
      ((hM.1 k).mono (ℱ.mono hkn.le) le_rfl)).indicator
      (ℱ.mono hkn.le _ (ControlledIncrement.tail_measurable hτ k))
  have hi : ∀ n, Integrable (maskedSum M τ n) P := fun n =>
    integrable_finsetSum _ fun k _ =>
      ControlledIncrement.integrable_stoppedIncrement P ℱ M τ hτ hM.2.1 k
  apply (martingale_iff_library P ℱ _).mpr
  apply martingale_of_condExp_sub_eq_zero_nat ha.stronglyAdapted hi
  intro k
  change P[(fun ω => maskedSum M τ (k + 1) ω - maskedSum M τ k ω) | ℱ k] =ᵐ[P] 0
  rw [maskedSum_increment]
  have hc := condExp_indicator ((hM.2.1 (k + 1)).sub (hM.2.1 k))
    (ControlledIncrement.tail_measurable hτ k)
  have hz := L2OrthogonalIncrements.increment_condExp_zero P ℱ M hM k
  filter_upwards [hc, hz] with ω hc hz
  change P[{ω | (k : WithTop ℕ) < τ ω}.indicator (M (k + 1) - M k) | ℱ k] ω = 0
  rw [hc]
  change P[M (k + 1) - M k | ℱ k] ω = 0 at hz
  simp only [Set.indicator_apply]
  split
  · exact hz
  · rfl

theorem maskedSum_memLp (P : Measure Ω) (ℱ : Filtration ℕ m)
    (M : ℕ → Ω → ℝ) (hL : ∀ n, MemLp (M n) 2 P)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ) (n : ℕ) :
    MemLp (maskedSum M τ n) 2 P := by
  apply memLp_finsetSum
  intro k hk
  exact ((hL (k + 1)).sub (hL k)).indicator
    (ℱ.le k _ (ControlledIncrement.tail_measurable hτ k)).nullMeasurableSet

/-- Identical distribution transfers the finite centered second moment. -/
theorem centered_memLp (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (Y k))
    (hd : ∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P)
    (hq : Integrable (fun ω => (Y 1 ω - waldMean P Y) ^ 2) P) :
    ∀ n, MemLp (waldCenteredSum P Y n) 2 P := by
  have h1 : MemLp (fun ω => Y 1 ω - waldMean P Y) 2 P :=
    (memLp_two_iff_integrable_sq
      ((((ha 1 le_rfl).mono (ℱ.le 1) le_rfl).sub measurable_const).aestronglyMeasurable)).mpr hq
  have hk (k : ℕ) : MemLp (fun ω => Y (k + 1) ω - waldMean P Y) 2 P :=
    ((hd (k + 1) (by omega)).comp
      (measurable_id.sub measurable_const : Measurable (fun x : ℝ => x - waldMean P Y))).memLp_iff.mpr h1
  intro n
  have he : waldCenteredSum P Y n =
      fun ω => ∑ k ∈ Finset.range n, (Y (k + 1) ω - waldMean P Y) :=
    funext (waldCenteredSum_eq_sum P Y n)
  rw [he]
  exact memLp_finsetSum _ fun k _ => hk k

/-- The conditional second moment is the common increment variance. -/
theorem square_condExp (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (Y k))
    (hd : ∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P)
    (hind : ∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P) (k : ℕ) :
    P[(fun ω => (Y (k + 1) ω - waldMean P Y) ^ 2) | ℱ k] =ᵐ[P]
      fun _ => ∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P := by
  have hm : Measurable (Y (k + 1)) :=
    (ha (k + 1) (by omega)).mono (ℱ.le _) le_rfl
  have hbase : Measurable[MeasurableSpace.comap (Y (k + 1)) inferInstance]
      (Y (k + 1)) := measurable_iff_comap_le.mpr le_rfl
  have hsq : Measurable[MeasurableSpace.comap (Y (k + 1)) inferInstance]
      (fun ω => (Y (k + 1) ω - waldMean P Y) ^ 2) :=
    (hbase.sub measurable_const).pow_const 2
  have hc := condExp_indep_eq hm.comap_le (ℱ.le k) hsq.stronglyMeasurable
    (by simpa using hind (k + 1) (by omega))
  have he : (∫ ω, (Y (k + 1) ω - waldMean P Y) ^ 2 ∂P) =
      ∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P :=
    ((hd (k + 1) (by omega)).comp
      ((measurable_id.sub measurable_const).pow_const 2 :
        Measurable (fun x : ℝ => (x - waldMean P Y) ^ 2))).integral_eq
  simpa only [he] using hc

/-- The retained increment has energy `v P(τ > k)`. -/
theorem masked_increment_energy (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (Y : ℕ → Ω → ℝ)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (Y k))
    (hd : ∀ k, 1 ≤ k → ProbabilityTheory.IdentDistrib (Y k) (Y 1) P P)
    (hind : ∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (Y k) inferInstance) (ℱ (k - 1)) P)
    (hq : Integrable (fun ω => (Y 1 ω - waldMean P Y) ^ 2) P)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ) (k : ℕ) :
    (∫ ω, ControlledIncrement.stoppedIncrement (waldCenteredSum P Y) τ k ω ^ 2 ∂P) =
      (∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P) *
        (P {ω | (k : WithTop ℕ) < τ ω}).toReal := by
  have hs := ControlledIncrement.tail_measurable hτ k
  have hs' := ℱ.le k _ hs
  have hL := centered_memLp P ℱ Y ha hd hq
  have hqk : Integrable (fun ω => (Y (k + 1) ω - waldMean P Y) ^ 2) P := by
    simpa only [Pi.sub_apply, waldCenteredSum_increment] using ((hL (k + 1)).sub (hL k)).integrable_sq
  calc
    _ = ∫ ω in {ω | (k : WithTop ℕ) < τ ω}, (Y (k + 1) ω - waldMean P Y) ^ 2 ∂P := by
      rw [← integral_indicator hs']
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by
        simp only [ControlledIncrement.stoppedIncrement, Set.indicator_apply,
          waldCenteredSum_increment]
        split <;> simp
    _ = ∫ ω in {ω | (k : WithTop ℕ) < τ ω},
        P[(fun ω => (Y (k + 1) ω - waldMean P Y) ^ 2) | ℱ k] ω ∂P :=
      (setIntegral_condExp (ℱ.le k) hqk hs).symm
    _ = ∫ _ in {ω | (k : WithTop ℕ) < τ ω},
        (∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P) ∂P := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (square_condExp P ℱ Y ha hd hind k)
    _ = _ := by simp [measureReal_def, mul_comm]

/-- Summable masked energies identify the L² terminal with the actual stopped
value. This uses finite-mean stopping only to identify the pathwise limit. -/
theorem stopped_energy_of_summable (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ P)
    (hL : ∀ n, MemLp (M n) 2 P) (hzero : ∀ ω, M 0 ω = 0)
    (τ : Ω → WithTop ℕ) (hτ : IsDiscreteStoppingTime ℱ τ)
    (hmean : (∫⁻ ω, ENat.toENNReal (τ ω) ∂P) < ⊤)
    (hs : Summable (fun k => ∫ ω,
      (maskedSum M τ (k + 1) ω - maskedSum M τ k ω) ^ 2 ∂P)) (A : Ω → ℝ) :
    MemLp (fullStoppedValue M τ A) 2 P ∧
    (∫ ω, fullStoppedValue M τ A ω ^ 2 ∂P) =
      ∑' k, ∫ ω, (maskedSum M τ (k + 1) ω - maskedSum M τ k ω) ^ 2 ∂P := by
  have hN := maskedSum_martingale P ℱ M hM τ hτ
  have hNL := maskedSum_memLp P ℱ M hL τ hτ
  obtain ⟨_, hlim, _, hae, _, _, he, _⟩ :=
    L2SummabilityConvergence.convergence_and_energy P ℱ (maskedSum M τ) hN hNL hs
  have hfinite := stopping_time_ae_finite_of_mean P ℱ τ hτ hmean
  have heq : ℱ.limitProcess (maskedSum M τ) P =ᵐ[P] fullStoppedValue M τ A := by
    filter_upwards [hae, hfinite] with ω hω hf
    cases ht : τ ω with
    | top => simp [ht] at hf
    | coe n =>
      have hh := ControlledIncrement.hasSum_stoppedIncrement_of_finite M τ ω n ht
      have hh' : HasSum (fun k => ControlledIncrement.stoppedIncrement M τ k ω)
          (fullStoppedValue M τ A ω) := by
        simpa only [fullStoppedValue_at_finite M τ (fun _ => 0) n ω ht,
          fullStoppedValue_at_finite M τ A n ω ht, hzero ω, sub_zero] using hh
      exact tendsto_nhds_unique hω hh'.tendsto_sum_nat
  refine ⟨MemLp.ae_eq heq hlim, ?_⟩
  calc
    _ = ∫ ω, ℱ.limitProcess (maskedSum M τ) P ω ^ 2 ∂P :=
      integral_congr_ae (heq.symm.fun_comp (fun x : ℝ => x ^ 2))
    _ = _ := by simpa [maskedSum] using he

end P207.WaldSecond

namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]
open WaldSecond

/-- Wald's second identity, with an arbitrary assignment at the null infinite stop. -/
theorem wald_second_centered : WaldSecondSpec.wald_second_centered.{u} := by
  intro Ω m P _ ℱ Y hi ha hd hind hq τ hτ hmean A
  have hM := wald_centered_sum_martingale P ℱ Y hi ha hd hind
  have hL := centered_memLp P ℱ Y ha hd hq
  have he (k : ℕ) : (∫ ω,
      (maskedSum (waldCenteredSum P Y) τ (k + 1) ω -
        maskedSum (waldCenteredSum P Y) τ k ω) ^ 2 ∂P) =
      (∫ ω, (Y 1 ω - waldMean P Y) ^ 2 ∂P) *
        (P {ω | (k : WithTop ℕ) < τ ω}).toReal := by
    have hh := maskedSum_increment (waldCenteredSum P Y) τ k
    simpa only [← hh] using masked_increment_energy P ℱ Y ha hd hind hq τ hτ k
  have htail : (∑' k : ℕ, P {ω | (k : WithTop ℕ) < τ ω}) ≠ ⊤ := by
    rw [stopping_time_tail_expectation P ℱ τ hτ]
    exact hmean.ne
  have hs : Summable (fun k => ∫ ω,
      (maskedSum (waldCenteredSum P Y) τ (k + 1) ω -
        maskedSum (waldCenteredSum P Y) τ k ω) ^ 2 ∂P) := by
    simp_rw [he]
    exact (ENNReal.summable_toReal htail).mul_left _
  obtain ⟨hstop, henergy⟩ := stopped_energy_of_summable P ℱ (waldCenteredSum P Y)
    hM hL (fun ω => by simp [waldCenteredSum, waldSum]) τ hτ hmean hs A
  refine ⟨hstop, ?_⟩
  rw [henergy]
  simp_rw [he]
  rw [tsum_mul_left, ← ENNReal.tsum_toReal_eq (fun k => measure_ne_top P _),
    stopping_time_tail_expectation P ℱ τ hτ]

/-- The centered stopped sum is square integrable and has energy `v Eτ`. -/
theorem wald_second : WaldSecondSpec.wald_second.{u} := by
  intro Ω m P _ ℱ Y hi ha hd hind hq τ hτ hmean A
  obtain ⟨hL, he⟩ := wald_second_centered P ℱ Y hi ha hd hind hq τ hτ hmean A
  have hf := stopping_time_ae_finite_of_mean P ℱ τ hτ hmean
  have heq : fullStoppedValue (waldCenteredSum P Y) τ A =ᵐ[P]
      (fun ω => fullStoppedValue (waldSum Y) τ A ω -
        waldMean P Y * waldTimeReal τ ω) := by
    filter_upwards [hf] with ω hω
    cases ht : τ ω with
    | top => simp [ht] at hω
    | coe n =>
      rw [fullStoppedValue_at_finite _ _ _ n ω ht,
        fullStoppedValue_at_finite _ _ _ n ω ht]
      have htime : waldTimeReal τ ω = n := by
        unfold waldTimeReal
        rw [ht]
        change (n : ℝ≥0∞).toReal = n
        exact ENNReal.toReal_natCast n
      rw [htime]
      rfl
  refine ⟨MemLp.ae_eq heq hL, ?_⟩
  calc
    _ = ∫ ω, fullStoppedValue (waldCenteredSum P Y) τ A ω ^ 2 ∂P :=
      integral_congr_ae (heq.symm.fun_comp (fun x : ℝ => x ^ 2))
    _ = _ := he

end P207
