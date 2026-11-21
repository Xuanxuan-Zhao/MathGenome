import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.ProcessInterfaces
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Foundation.TwoTimeAndExamples

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

variable {Ω : Type u} [m : MeasurableSpace Ω]

theorem martingale_iff_library (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) :
    IsMartingale X ℱ μ ↔ Martingale X ℱ μ := by
  constructor
  · rintro ⟨ha, hi, hs⟩
    exact martingale_nat ha.stronglyAdapted hi (fun n => (hs n).symm)
  · intro h
    exact ⟨h.stronglyAdapted.adapted, h.integrable, fun n => h.condExp_ae_eq n.le_succ⟩

theorem submartingale_iff_library (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) :
    IsSubmartingale X ℱ μ ↔ Submartingale X ℱ μ := by
  constructor
  · rintro ⟨ha, hi, hs⟩
    exact submartingale_nat ha.stronglyAdapted hi hs
  · intro h
    exact ⟨h.stronglyAdapted.adapted, h.integrable, fun n => h.ae_le_condExp n.le_succ⟩

theorem martingale_two_time (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (ha : Adapted ℱ X) (hi : ∀ n, Integrable (X n) μ) :
    (∀ n, μ[X (n + 1) | ℱ n] =ᵐ[μ] X n) ↔
      ∀ i j, i ≤ j → μ[X j | ℱ i] =ᵐ[μ] X i := by
  constructor
  · intro hs
    exact ((martingale_iff_library μ ℱ X).mp ⟨ha, hi, hs⟩).2
  · intro hs n
    exact hs n (n + 1) n.le_succ

theorem submartingale_two_time (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (ha : Adapted ℱ X) (hi : ∀ n, Integrable (X n) μ) :
    (∀ n, X n ≤ᵐ[μ] μ[X (n + 1) | ℱ n]) ↔
      ∀ i j, i ≤ j → X i ≤ᵐ[μ] μ[X j | ℱ i] := by
  constructor
  · intro hs
    exact ((submartingale_iff_library μ ℱ X).mp ⟨ha, hi, hs⟩).2.1
  · intro hs n
    exact hs n (n + 1) n.le_succ

theorem martingale_simultaneous (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (h : IsMartingale X ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ i j, i ≤ j → μ[X j | ℱ i] ω = X i ω := by
  have hall := ((martingale_iff_library μ ℱ X).mp h).2
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    ae_all_iff.mpr fun hij => hall i j hij

theorem submartingale_simultaneous (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (h : IsSubmartingale X ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ i j, i ≤ j → X i ω ≤ μ[X j | ℱ i] ω := by
  have hall := ((submartingale_iff_library μ ℱ X).mp h).2.1
  exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun j =>
    ae_all_iff.mpr fun hij => hall i j hij

theorem centered_independent_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (ξ : ℕ → Ω → ℝ)
    (hi : ∀ k, 1 ≤ k → Integrable (ξ k) μ)
    (ha : ∀ k, 1 ≤ k → Measurable[ℱ k] (ξ k))
    (hz : ∀ k, 1 ≤ k → (∫ ω, ξ k ω ∂μ) = 0)
    (hind : ∀ k, 1 ≤ k → ProbabilityTheory.Indep
      (MeasurableSpace.comap (ξ k) inferInstance) (ℱ (k - 1)) μ) :
    IsMartingale (fun n ω => ∑ k ∈ Finset.range n, ξ (k + 1) ω) ℱ μ := by
  have hadp : Adapted ℱ (fun n ω => ∑ k ∈ Finset.range n, ξ (k + 1) ω) := by
    intro n
    apply Finset.measurable_sum
    intro k hk
    exact (ha (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).mono
      (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hk))) le_rfl
  have hint : ∀ n, Integrable (fun ω => ∑ k ∈ Finset.range n, ξ (k + 1) ω) μ := by
    intro n
    exact integrable_finsetSum _ fun k _ => hi (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  refine ⟨hadp, hint, fun n => ?_⟩
  have hmeas : Measurable (ξ (n + 1)) :=
    (ha (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).mono (ℱ.le _) le_rfl
  have hce : μ[ξ (n + 1) | ℱ n] =ᵐ[μ] fun _ => (0 : ℝ) := by
    have h := condExp_indep_eq hmeas.comap_le (ℱ.le n)
      (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
      (by simpa using hind (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    simpa only [hz (n + 1) (Nat.succ_le_succ (Nat.zero_le n))] using h
  simp only [Finset.sum_range_succ]
  have hadd := condExp_add (hint n) (hi (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) (ℱ n)
  have hself := condExp_of_stronglyMeasurable (ℱ.le n) (hadp.stronglyAdapted n) (hint n)
  filter_upwards [hadd, hce] with ω hω hzω
  change μ[(fun ω => ∑ k ∈ Finset.range n, ξ (k + 1) ω) + ξ (n + 1) | ℱ n] ω = _
  rw [hω]
  change μ[(fun ω => ∑ k ∈ Finset.range n, ξ (k + 1) ω) | ℱ n] ω + μ[ξ (n + 1) | ℱ n] ω = _
  rw [hself, hzω, add_zero]

theorem conditional_expectation_process (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (Y : Ω → ℝ) (_hY : Integrable Y μ) :
    IsMartingale (fun n => μ[Y | ℱ n]) ℱ μ := by
  exact (martingale_iff_library μ ℱ _).mpr (martingale_condExp Y ℱ μ)

end P207
