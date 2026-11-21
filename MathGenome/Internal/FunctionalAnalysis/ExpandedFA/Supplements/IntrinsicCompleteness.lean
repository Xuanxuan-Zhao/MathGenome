import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.IntrinsicCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Supplements.NetTests
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecialFunctions.Exp

open Set Filter Topology
universe u v

namespace ExpandedFA.IntrinsicCompleteness

/-- The tail criterion for arbitrary directed preorders, without requiring suprema. -/
theorem metric_tail_iff_cauchy {E : Type u} [MetricSpace E]
    {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] (a : ι → E) :
    (∀ ε > (0 : ℝ), ∃ i, ∀ j, i ≤ j → ∀ k, i ≤ k → dist (a j) (a k) < ε) ↔
      Cauchy (map a atTop) := by
  rw [Metric.cauchy_iff]
  constructor
  · intro h
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨i, hi⟩ := h ε hε
    refine ⟨a '' Ici i, ?_, ?_⟩
    · exact eventually_atTop.2 ⟨i, fun j hj => ⟨j, hj, rfl⟩⟩
    · rintro x ⟨j, hj, rfl⟩ y ⟨k, hk, rfl⟩
      exact hi j hj k hk
  · rintro ⟨_, h⟩ ε hε
    obtain ⟨s, hs, hdist⟩ := h ε hε
    obtain ⟨i, hi⟩ := eventually_atTop.1 hs
    exact ⟨i, fun j hj k hk => hdist _ (hi j hj) _ (hi k hk)⟩

theorem cauchyCriterion :
    Specs.ExpandedFA.IntrinsicCompleteness.cauchyCriterion.{u,v} := by
  intro E _ t d ι _ a
  rcases d with ⟨m, hm, hinv⟩
  cases hm
  let := m
  have hdist (x y : E) : dist (x - y) 0 = dist x y := by
    simpa only [sub_eq_add_neg, add_neg_cancel] using hinv x y (-y)
  constructor
  · intro h ε hε
    obtain ⟨i, hi⟩ := h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
    refine ⟨i, fun j hj k hk => ?_⟩
    have := hi j hj k hk
    change dist (a j - a k) 0 < ε at this
    rwa [hdist] at this
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨i, hi⟩ := h ε hε
    refine ⟨i, fun j hj k hk => hball ?_⟩
    change dist (a j - a k) 0 < ε
    rw [hdist]
    exact hi j hj k hk

theorem metricIndependence :
    Specs.ExpandedFA.IntrinsicCompleteness.metricIndependence.{u,v} := by
  intro E _ _ d e ι _ a
  exact (cauchyCriterion E d ι a).symm.trans (cauchyCriterion E e ι a)

/-- Relate the intrinsic definition directly to the metric's Cauchy filters. -/
theorem zeroCauchy_iff_cauchy_map {E : Type u} [AddCommGroup E] [t : TopologicalSpace E]
    (d : CompatibleInvariantMetric E) {ι : Type v} [Preorder ι]
    [Nonempty ι] [IsDirectedOrder ι] (a : ι → E) :
    ZeroCauchy a ↔ @Cauchy E d.metric.toUniformSpace (map a atTop) := by
  rw [cauchyCriterion E d ι a]
  let := d.metric
  exact metric_tail_iff_cauchy a

theorem completeMetricNets :
    Specs.ExpandedFA.IntrinsicCompleteness.completeMetricNets.{u,v} := by
  intro E _ t d hc ι _ _ _ a ha
  have hca := (zeroCauchy_iff_cauchy_map d a).1 ha
  rcases d with ⟨m, hm, hinv⟩
  cases hm
  let := m
  let := hc
  exact cauchy_map_iff_exists_tendsto.1 hca

theorem completeMetricIffNet :
    Specs.ExpandedFA.IntrinsicCompleteness.completeMetricIffNet.{u} := by
  intro E _ t d
  constructor
  · intro hc
    exact completeMetricNets E d hc
  · intro hn
    rcases d with ⟨m, hm, hinv⟩
    cases hm
    let := m
    constructor
    intro F hF
    let := hF.1
    let d : CompatibleInvariantMetric E := ⟨m, rfl, hinv⟩
    have ha : ZeroCauchy (fun p : NetTests.FilterIndex F => p.val.2) := by
      apply (zeroCauchy_iff_cauchy_map d _).2
      rwa [NetTests.map_filterIndex]
    obtain ⟨x, hx⟩ := hn (NetTests.FilterIndex F) (fun p => p.val.2) ha
    refine ⟨x, ?_⟩
    change map _ atTop ≤ 𝓝 x at hx
    rwa [NetTests.map_filterIndex] at hx

theorem completeMetricIffSequence :
    Specs.ExpandedFA.IntrinsicCompleteness.completeMetricIffSequence.{u} := by
  intro E _ t d
  constructor
  · intro hc a ha
    exact completeMetricNets E d hc ℕ a ha
  · intro hs
    rcases d with ⟨m, hm, hinv⟩
    cases hm
    let := m
    apply Metric.complete_of_cauchySeq_tendsto
    intro a ha
    apply hs a
    exact (zeroCauchy_iff_cauchy_map ⟨m, rfl, hinv⟩ a).2 ha

theorem sequenceIffNet :
    Specs.ExpandedFA.IntrinsicCompleteness.sequenceIffNet.{u} := by
  intro E _ _ d
  exact (completeMetricIffSequence E d).symm.trans (completeMetricIffNet E d)

theorem completeMetricIndependence :
    Specs.ExpandedFA.IntrinsicCompleteness.completeMetricIndependence.{u} := by
  intro E _ _ d e
  exact (completeMetricIffNet E d).trans (completeMetricIffNet E e).symm

/-- Pulling the real metric back along exp preserves the topology but loses
completeness: its isometric image is the nonclosed positive half-line. -/
theorem nonInvariantCounterexample :
    Specs.ExpandedFA.IntrinsicCompleteness.nonInvariantCounterexample := by
  refine ⟨inferInstance,
    MetricSpace.induced Real.exp Real.exp_injective inferInstance, ?_, ?_⟩
  · exact Real.isOpenEmbedding_exp.isEmbedding.eq_induced.symm
  · intro hc
    have hi := MetricSpace.isometry_induced Real.exp Real.exp_injective
    have hui := @Isometry.isUniformInducing ℝ ℝ
      (MetricSpace.induced Real.exp Real.exp_injective Real.metricSpace).toPseudoEMetricSpace
      (inferInstance : PseudoEMetricSpace ℝ) Real.exp hi
    have hrange : IsComplete (range Real.exp) :=
      (@completeSpace_iff_isComplete_range ℝ ℝ
        (MetricSpace.induced Real.exp Real.exp_injective Real.metricSpace).toUniformSpace
        (inferInstance : UniformSpace ℝ) Real.exp hui).1 hc
    have hclosed : IsClosed (range Real.exp) := hrange.isClosed
    have hz : (0 : ℝ) ∈ range Real.exp := hclosed.mem_of_tendsto
      Real.tendsto_exp_atBot (Eventually.of_forall (fun x => mem_range_self x))
    obtain ⟨x, hx⟩ := hz
    exact Real.exp_ne_zero x hx

end ExpandedFA.IntrinsicCompleteness
