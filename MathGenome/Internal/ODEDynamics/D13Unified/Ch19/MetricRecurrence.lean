import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.PoincareRecurrence
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.MetricRecurrence
import Mathlib.Topology.Bases

/-! Metric recurrence, obtained from measurable-set recurrence on a countable
basis. All neighborhoods share the same exceptional null set. -/

namespace D13Unified.Ch19.MetricRecurrence

universe u
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
open D13Unified.Ch19.MeasureDefinitions

/-- `paper.tex`, Corollary `d13:19:metric-recurrence`. -/
theorem metric_recurrence :
    ∀ {X : Type u} [MetricSpace X] [SecondCountableTopology X]
      [MeasurableSpace X] [BorelSpace X] (T : X → X) (μ : Measure X)
      [IsProbabilityMeasure μ],
      PreservesMeasure T μ →
      ∀ᵐ x ∂μ, ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ k, 0 < n k) ∧
        Tendsto n atTop atTop ∧
        Tendsto (fun k => T^[n k] x) atTop (𝓝 x) := by
  intro X _ _ _ _ T μ _ hT
  have hb : ∀ s ∈ countableBasis X,
      ∀ᵐ x ∂μ, x ∈ s → Set.Infinite {n : ℕ | 1 ≤ n ∧ T^[n] x ∈ s} := by
    intro s hs
    exact PoincareRecurrence.poincare_recurrence T μ hT s
      (isOpen_of_mem_countableBasis hs).measurableSet
  -- Countable intersection here fixes one full-measure set before choosing
  -- the point's neighborhoods or subsequence.
  refine ((ae_ball_iff (countable_countableBasis X)).2 hb).mono ?_
  intro x hx
  have hreturn : ∀ s ∈ 𝓝 x, ∃ᶠ n in atTop, T^[n] x ∈ s := by
    intro s hs
    obtain ⟨b, hb, hxb, hbs⟩ :=
      (isBasis_countableBasis X).mem_nhds_iff.mp hs
    exact (Nat.frequently_atTop_iff_infinite.mpr (hx b hb hxb)).mono
      (fun n hn => hbs hn.2)
  have hcluster : MapClusterPt x atTop (fun n : ℕ => T^[n] x) :=
    mapClusterPt_iff_frequently.mpr hreturn
  obtain ⟨n, hn, hlim⟩ := hcluster.tendsto_subseq
  -- Discard the first time to make every time positive, including at k = 0.
  have hn' : StrictMono (fun k => n (k + 1)) :=
    fun a b hab => hn (Nat.add_lt_add_right hab 1)
  refine ⟨fun k => n (k + 1), hn', ?_, hn'.tendsto_atTop, ?_⟩
  · intro k
    exact lt_of_lt_of_le (Nat.succ_pos k) (hn.id_le (k + 1))
  · exact hlim.comp (tendsto_add_atTop_nat 1)

end D13Unified.Ch19.MetricRecurrence
