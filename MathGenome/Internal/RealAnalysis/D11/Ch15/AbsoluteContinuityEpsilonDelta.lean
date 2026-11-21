import MathGenome.Internal.RealAnalysis.D11.Ch15.AbsoluteContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuityEpsilonDelta
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic

open Set MeasureTheory Filter
open scoped ENNReal Topology

universe u v

namespace D11.Ch15.AbsoluteContinuityEpsilonDelta

/-- The small-set bound for a finite positive target; the reference is arbitrary. -/
theorem finite_positive_small_sets {α : Type u} [MeasurableSpace α]
    (ρ μ : Measure α) [IsFiniteMeasure ρ] (h : ρ ≪ μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ E : Set α, MeasurableSet E →
      μ E < ENNReal.ofReal δ → ρ E < ENNReal.ofReal ε := by
  classical
  by_contra! hfail
  have hchoose : ∀ n : ℕ, ∃ E : Set α, MeasurableSet E ∧
      μ E < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) ∧ ENNReal.ofReal ε ≤ ρ E := by
    intro n
    exact hfail _ (pow_pos (by norm_num) _)
  choose E hE hμ hρ using hchoose
  have hsum : ∑' n, μ (E n) ≠ ∞ := by
    apply ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n)
    · simp
    · apply ENNReal.tsum_le_tsum
      intro n
      simpa only [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)⁻¹),
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
        using (hμ n).le
  let H : ℕ → Set α := fun j => ⋃ k ≥ j, E k
  have hH : ∀ j, MeasurableSet (H j) := fun j =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hE k
  have hanti : Antitone H := fun i j hij =>
    iUnion₂_subset fun k hk => subset_iUnion₂_of_subset k (hij.trans hk) subset_rfl
  have hnull : μ (⋂ j, H j) = 0 := by
    change μ (⋂ j, ⋃ k ≥ j, E k) = 0
    simpa only [limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
      using measure_limsup_atTop_eq_zero hsum
  have hzero : ρ (⋂ j, H j) = 0 := h hnull
  have hle : ENNReal.ofReal ε ≤ ρ (⋂ j, H j) := by
    rw [hanti.measure_iInter (fun j => (hH j).nullMeasurableSet)
      ⟨0, measure_ne_top ρ _⟩]
    apply le_iInf
    intro j
    exact (hρ j).trans (measure_mono (subset_iUnion₂_of_subset j le_rfl subset_rfl))
  exact (ENNReal.ofReal_pos.mpr hε).not_ge (hzero ▸ hle)

open D11.Ch14.TotalVariation D11.Ch15.AbsoluteContinuity

/-- Small scalar values on reference-small sets force the original null-set test. -/
theorem scalar_ac_of_small_values {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α)
    (h : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖ν E‖ < ε) :
    scalarAbsolutelyContinuous ν μ := by
  apply (scalar_iff ν μ).mpr
  intro E hE hz
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := h ε hε
  exact (hbound E hE (hz ▸ ENNReal.ofReal_pos.mpr hδ)).le

/-- Both criteria for any vector measure whose variation is finite. The scalar
specializations below discharge this finiteness using the upstream theorem. -/
theorem scalar_small_set_criteria {α : Type u} [MeasurableSpace α]
    {K : Type v} [NormedAddCommGroup K] (ν : VectorMeasure α K) (μ : Measure α)
    [IsFiniteMeasure (totalVariation ν)] :
    (scalarAbsolutelyContinuous ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation ν E < ENNReal.ofReal ε) ∧
    (scalarAbsolutelyContinuous ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖ν E‖ < ε) := by
  have hforward : scalarAbsolutelyContinuous ν μ →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation ν E < ENNReal.ofReal ε := by
    intro h ε hε
    exact finite_positive_small_sets (totalVariation ν) μ h ε hε
  have hvalues :
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation ν E < ENNReal.ofReal ε) →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖ν E‖ < ε) := by
    intro h ε hε
    obtain ⟨δ, hδ, hbound⟩ := h ε hε
    refine ⟨δ, hδ, fun E hE hsmall => ?_⟩
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
      ((norm_le_totalVariation ν E).trans_lt (hbound E hE hsmall))
  exact ⟨⟨hforward, fun h => scalar_ac_of_small_values ν μ (hvalues h)⟩,
    ⟨fun h => hvalues (hforward h), scalar_ac_of_small_values ν μ⟩⟩

theorem signed_variation_iff {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) (μ : Measure α) :
    scalarAbsolutelyContinuous ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation ν E < ENNReal.ofReal ε := by
  letI := signed_finite ν
  exact (scalar_small_set_criteria ν μ).1

theorem signed_value_iff {α : Type u} [MeasurableSpace α]
    (ν : SignedMeasure α) (μ : Measure α) :
    scalarAbsolutelyContinuous ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖ν E‖ < ε := by
  letI := signed_finite ν
  exact (scalar_small_set_criteria ν μ).2

theorem complex_variation_iff {α : Type u} [MeasurableSpace α]
    (ν : ComplexMeasure α) (μ : Measure α) :
    scalarAbsolutelyContinuous ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ →
          totalVariation ν E < ENNReal.ofReal ε := by
  letI := complex_finite ν
  exact (scalar_small_set_criteria ν μ).1

theorem complex_value_iff {α : Type u} [MeasurableSpace α]
    (ν : ComplexMeasure α) (μ : Measure α) :
    scalarAbsolutelyContinuous ν μ ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ E : Set α, MeasurableSet E → μ E < ENNReal.ofReal δ → ‖ν E‖ < ε := by
  letI := complex_finite ν
  exact (scalar_small_set_criteria ν μ).2

end D11.Ch15.AbsoluteContinuityEpsilonDelta
