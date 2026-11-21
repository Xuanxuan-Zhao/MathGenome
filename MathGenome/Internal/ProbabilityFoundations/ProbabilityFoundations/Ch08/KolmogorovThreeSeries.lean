import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.KolmogorovThreeSeries
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.SummableVarianceSeries
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.ThreeSeriesVarianceNecessity
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.PairwiseBorelCantelliRatio

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace ProbabilityFoundations.Ch08

namespace ThreeSeries

open ThreeSeriesVarianceNecessity

theorem orderedSeriesConverges_add {f g : ℕ → ℝ}
    (hf : OrderedSeriesConverges f) (hg : OrderedSeriesConverges g) :
    OrderedSeriesConverges (fun k => f k + g k) := by
  obtain ⟨l, hl⟩ := hf
  obtain ⟨m, hm⟩ := hg
  exact ⟨l + m, by simpa only [Finset.sum_add_distrib] using hl.add hm⟩

theorem orderedSeriesConverges_sub {f g : ℕ → ℝ}
    (hf : OrderedSeriesConverges f) (hg : OrderedSeriesConverges g) :
    OrderedSeriesConverges (fun k => f k - g k) := by
  obtain ⟨l, hl⟩ := hf
  obtain ⟨m, hm⟩ := hg
  exact ⟨l - m, by simpa only [Finset.sum_sub_distrib] using hl.sub hm⟩

/-- Centering preserves independence and variance, so the variance-series
theorem applies without any condition on convergence of the means. -/
theorem ae_centered_orderedSeriesConverges
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (hI : iIndepFun Y P)
    (h2 : ∀ k, MemLp (Y k) 2 P)
    (hs : Summable (fun k => variance (Y k) P)) :
    ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => Y k ω - ∫ x, Y k x ∂P) := by
  let C : ℕ → Ω → ℝ := fun k ω => Y k ω - ∫ x, Y k x ∂P
  have hC (k : ℕ) : Measurable (C k) := (hY k).sub_const _
  have hCI : iIndepFun C P := hI.comp (fun k x => x - ∫ ω, Y k ω ∂P)
    (fun _ => measurable_id.sub_const _)
  have hC2 (k : ℕ) : MemLp (C k) 2 P := (h2 k).sub (memLp_const _)
  have hCmean (k : ℕ) : (∫ ω, C k ω ∂P) = 0 := by
    change (∫ ω, Y k ω - ∫ x, Y k x ∂P ∂P) = 0
    rw [integral_sub ((h2 k).integrable (by norm_num)) (integrable_const _)]
    simp
  have hv (k : ℕ) : Ch01.realVariance P (C k) = variance (Y k) P := by
    change (∫ ω, (C k ω - ∫ x, C k x ∂P) ^ 2 ∂P) = _
    rw [← variance_eq_integral (hC k).aemeasurable]
    exact variance_sub_const (hY k).aestronglyMeasurable _
  have hsC : Summable (fun k => Ch01.realVariance P (C k)) := by
    simpa only [hv] using hs
  obtain ⟨Z, _, _, hZ, _⟩ := summable_variance_series P C hC
    ((Ch02.independentRandomElements_iff_iIndepFun P C).mpr hCI) hC2 hCmean hsC
  filter_upwards [hZ] with ω hω
  exact ⟨Z ω, hω⟩

/-- Convergence makes the independent large-term events summable by the
second Borel–Cantelli lemma. No integrability of X is used. -/
theorem tail_probabilities_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (hI : iIndepFun X P)
    (a : ℝ) (ha : 0 < a)
    (hc : ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => X k ω)) :
    (∑' k, P {ω | a < |X k ω|}) < ∞ := by
  let A : ℕ → Set Ω := fun k => {ω | a < |X k ω|}
  have hB : MeasurableSet {x : ℝ | a < |x|} := by
    simpa only [Real.norm_eq_abs, id_eq] using
      measurableSet_lt (measurable_const (a := a)) (measurable_id (α := ℝ)).norm
  have hA (k : ℕ) : MeasurableSet (A k) := (hX k) hB
  have hAI : Ch02.PairwiseIndependentEvents P A := by
    apply (Ch02.pairwiseIndependentEvents_iff P A).mpr
    intro i j hij
    exact (indepFun_iff_indepSet_preimage (hX i) (hX j)).mp
      (hI.indepFun hij) _ _ hB hB
  have hz : P (Ch02.infinitelyOftenEvent A) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hc] with ω hω
    have ht : Tendsto (fun k => |X k ω|) atTop (𝓝 0) := by
      simpa only [abs_zero] using (OrderedSeriesConverges.tendsto_zero hω).abs
    rw [Ch02.infinitelyOftenEvent_eq_limsup, mem_limsup_iff_frequently_mem]
    apply not_frequently.mpr
    filter_upwards [(tendsto_order.mp ht).2 a ha] with k hk
    exact not_lt.mpr hk.le
  by_contra h
  have ht : (∑' k, P (A k)) = ∞ := top_unique (le_of_not_gt h)
  have ho := Ch02.second_borel_cantelli P A hA hAI ht
  exact zero_ne_one (hz.symm.trans ho)

end ThreeSeries

/-- Kolmogorov's three-series theorem for each fixed positive cutoff.
The expectation series is ordinary ordered convergence, including the
conditionally convergent case. -/
theorem kolmogorov_three_series :
    Specs.ProbabilityFoundations.Ch08.KolmogorovThreeSeries.kolmogorovThreeSeriesType := by
  intro Ω mΩ P hP X hX hI a ha
  let Y := symmetricTruncation a X
  have hY (k : ℕ) : Measurable (Y k) :=
    ThreeSeriesVarianceNecessity.measurable_symmetricTruncation X hX a k
  have hY2 (k : ℕ) : MemLp (Y k) 2 P :=
    ThreeSeriesVarianceNecessity.memLp_symmetricTruncation P X hX ha.le k 2
  have hYI : iIndepFun Y P :=
    ThreeSeriesVarianceNecessity.iIndepFun_symmetricTruncation P X hI a
  constructor
  · intro hc
    have hs := summable_variance_symmetricTruncation P X hX hI a ha hc
    have hcenter := ThreeSeries.ae_centered_orderedSeriesConverges P Y hY hYI hY2 hs
    have huncenter :=
      ThreeSeriesVarianceNecessity.ae_orderedSeriesConverges_symmetricTruncation P X ha hc
    obtain ⟨ω, hω, hωc⟩ := (huncenter.and hcenter).exists
    have hm := ThreeSeries.orderedSeriesConverges_sub hω hωc
    have hmeans : OrderedSeriesConverges (fun k => ∫ x, Y k x ∂P) := by
      convert hm using 1
      funext k
      dsimp [Y]
      ring
    exact ⟨ThreeSeries.tail_probabilities_finite P X hX hI a ha hc, hmeans, hs⟩
  · rintro ⟨htail, hmeans, hs⟩
    have hcenter := ThreeSeries.ae_centered_orderedSeriesConverges P Y hY hYI hY2 hs
    have hevent : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∉ {x | a < |X k x|} :=
      ae_eventually_notMem htail.ne
    filter_upwards [hcenter, hevent] with ω hω heq
    have hYc : OrderedSeriesConverges (fun k => Y k ω) := by
      simpa only [Y, sub_add_cancel] using ThreeSeries.orderedSeriesConverges_add hω hmeans
    apply ThreeSeriesVarianceNecessity.OrderedSeriesConverges.congr_eventually hYc
    filter_upwards [heq] with k hk
    have hk' : |X k ω| ≤ a := le_of_not_gt hk
    simp [Y, symmetricTruncation, hk']

end ProbabilityFoundations.Ch08
