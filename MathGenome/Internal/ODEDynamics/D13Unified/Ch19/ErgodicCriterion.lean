import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.ErgodicCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.Birkhoff

namespace D13Unified.Ch19.ErgodicCriterion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators symmDiff
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable (T : X → X)

/-- The null symmetric-difference condition propagates without invertibility. -/
theorem invariantModNull_iterate :
    Specs.D13Unified.Ch19.ErgodicCriterion.invariantModNull_iterateStatement.{u} := by
  intro X _ T μ hT E hi n
  apply (MeasureDefinitions.invariantModNull_iff_ae (T^[n]) μ E).mpr
  exact hT.quasiMeasurePreserving.preimage_iterate_ae_eq n
    ((MeasureDefinitions.invariantModNull_iff_ae T μ E).mp hi)

/-- On one full-measure set, all positive averages of an invariant indicator
are that indicator. This uses only a countable intersection over iterates. -/
lemma average_indicator_invariant {𝕜 : Type} [RCLike 𝕜]
    (hT : MeasurePreserving T μ μ) (E : Set X)
    (hi : MeasureDefinitions.InvariantModNull T μ E) :
    ∀ᵐ x ∂μ, ∀ n : ℕ, n ≠ 0 →
      MeasureDefinitions.ergodicAverage T (E.indicator (fun _ => (1 : 𝕜))) n x =
        E.indicator (fun _ => (1 : 𝕜)) x := by
  have hn : ∀ n : ℕ, (T^[n] ⁻¹' E) =ᵐ[μ] E := fun n =>
    (MeasureDefinitions.invariantModNull_iff_ae (T^[n]) μ E).mp
      (invariantModNull_iterate T μ hT E hi n)
  filter_upwards [ae_all_iff.mpr hn] with x hx
  intro n hn
  have he : ∀ j : ℕ, E.indicator (fun _ => (1 : 𝕜)) (T^[j] x) =
      E.indicator (fun _ => (1 : 𝕜)) x := by
    intro j
    have hj : T^[j] x ∈ E ↔ x ∈ E := Iff.of_eq (hx j)
    by_cases hxE : x ∈ E
    · rw [indicator_of_mem (hj.mpr hxE), indicator_of_mem hxE]
    · rw [indicator_of_notMem (mt hj.mp hxE), indicator_of_notMem hxE]
  rw [MeasureDefinitions.ergodicAverage_eq_sum]
  simp only [he, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul]

/-- Constant limits for all integrable observables force the zero-one law. -/
lemma ergodic_of_averages {𝕜 : Type} [RCLike 𝕜] [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ)
    (ha : ∀ f : X → 𝕜, Integrable f μ → ∀ᵐ x ∂μ,
      Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
        atTop (𝓝 (∫ y, f y ∂μ))) : MeasureDefinitions.IsErgodic T μ := by
  intro E hE hi
  let f : X → 𝕜 := E.indicator (fun _ => 1)
  have hf : Integrable f μ := (integrable_const (1 : 𝕜)).indicator hE
  have heq : f =ᵐ[μ] fun _ => ∫ y, f y ∂μ := by
    filter_upwards [ha f hf, average_indicator_invariant (𝕜 := 𝕜) T hT E hi] with x hx hiX
    have hc : Tendsto (fun n => MeasureDefinitions.ergodicAverage T f n x)
        atTop (𝓝 (f x)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact (hiX n hn).symm
    exact tendsto_nhds_unique hc hx
  by_cases hz : (∫ y, f y ∂μ) = 0
  · left
    apply ae_eq_empty.mp
    filter_upwards [heq] with x hx
    apply propext
    simp only [mem_empty_iff_false, iff_false]
    intro hxE
    have hx1 : f x = 1 := indicator_of_mem hxE _
    exact one_ne_zero (hx1.symm.trans (hx.trans hz))
  · right
    have hu : E =ᵐ[μ] univ := by
      filter_upwards [heq] with x hx
      apply propext
      simp only [mem_univ, iff_true]
      by_contra hxE
      have : (0 : 𝕜) = ∫ y, f y ∂μ := by
        simpa only [f, indicator_of_notMem hxE] using hx
      exact hz this.symm
    simpa using measure_congr hu

/-- Real L¹ time averages characterize ergodicity, observable by observable. -/
theorem real_ergodic_criterion :
    Specs.D13Unified.Ch19.ErgodicCriterion.real_ergodic_criterionStatement.{u} := by
  intro X _ T μ _ hT
  constructor
  · intro he f hf
    obtain ⟨g, _, ha, _, _, _, _, hg⟩ := Birkhoff.real_birkhoff T μ hT f hf
    filter_upwards [ha, hg he] with x hx heq
    simpa only [heq] using hx
  · exact ergodic_of_averages T hT

/-- The same equivalence for complex L¹ observables. -/
theorem complex_ergodic_criterion :
    Specs.D13Unified.Ch19.ErgodicCriterion.complex_ergodic_criterionStatement.{u} := by
  intro X _ T μ _ hT
  constructor
  · intro he f hf
    obtain ⟨g, _, ha, _, _, _, _, hg⟩ := Birkhoff.complex_birkhoff T μ hT f hf
    filter_upwards [ha, hg he] with x hx heq
    simpa only [heq] using hx
  · exact ergodic_of_averages T hT

/-- Mixing tests an almost-invariant set against itself. -/
theorem mixing_implies_ergodic :
    Specs.D13Unified.Ch19.ErgodicCriterion.mixing_implies_ergodicStatement.{u} := by
  intro X _ T μ _ hT hm E hE hi
  have hn : ∀ n : ℕ, μ (E ∩ (T^[n] ⁻¹' E)) = μ E := by
    intro n
    have he := (MeasureDefinitions.invariantModNull_iff_ae (T^[n]) μ E).mp
      (invariantModNull_iterate T μ hT E hi n)
    simpa only [inter_self] using measure_congr (EventuallyEqSet.inter (s := E) .rfl he)
  have hl := hm E E hE hE
  change Tendsto (fun n : ℕ => μ (E ∩ (T^[n] ⁻¹' E))) atTop (𝓝 (μ E * μ E)) at hl
  simp only [hn] at hl
  have hid : μ E = μ E * μ E := tendsto_nhds_unique tendsto_const_nhds hl
  have hr : (μ E).toReal = (μ E).toReal * (μ E).toReal := by
    simpa only [ENNReal.toReal_mul] using congrArg ENNReal.toReal hid
  by_cases hz : (μ E).toReal = 0
  · left
    exact ((ENNReal.toReal_eq_zero_iff (μ E)).mp hz).resolve_right (measure_ne_top μ E)
  · right
    exact (ENNReal.toReal_eq_one_iff (μ E)).mp ((mul_eq_left₀ hz).mp hr.symm)

end
end D13Unified.Ch19.ErgodicCriterion
