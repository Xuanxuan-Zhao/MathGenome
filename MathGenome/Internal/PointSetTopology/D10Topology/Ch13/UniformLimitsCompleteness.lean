import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.UniformLimitsCompleteness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.MetricFilterCompleteness

noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v w
namespace D10Topology.Ch13
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]

theorem uniform_limit_continuous_filter {I : Type w} (l : Filter I) [l.NeBot]
    (F : I → X → Y) (f : X → Y) (hF : ∀ i, Continuous (F i))
    (hlim : Tendsto F l (@nhds (X → Y) uniformTopology f)) : Continuous f := by
  have hu : Tendsto (fun i => UniformFun.ofFun (F i)) l
      (𝓝 (UniformFun.ofFun f)) := by
    change Tendsto F l (@nhds (X → Y) (TopologicalSpace.induced UniformFun.ofFun _) f) at hlim
    rw [nhds_induced] at hlim
    exact tendsto_comap_iff.mp hlim
  exact (UniformFun.tendsto_iff_tendstoUniformly.mp hu).continuous
    (Eventually.of_forall hF).frequently

theorem uniform_limit_continuous_net {I : Type w} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] (F : I → X → Y) (f : X → Y)
    (hF : ∀ i, Continuous (F i))
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ i₀, ∀ i, i₀ ≤ i → uniformDistance (F i) f < ε) :
    Continuous f := by
  apply uniform_limit_continuous_filter atTop F f hF
  apply (uniform_nhds_hasBasis f).tendsto_right_iff.mpr
  intro ε hε
  obtain ⟨i₀, hi₀⟩ := hlim ε hε
  exact eventually_atTop.2 ⟨i₀, fun i hi => by
    change uniformDistance f (F i) < ε
    rw [uniformDistance_comm]
    exact hi₀ i hi⟩

theorem uniform_limit_continuous_sequence (F : ℕ → X → Y) (f : X → Y)
    (hF : ∀ n, Continuous (F n))
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → uniformDistance (F n) f < ε) :
    Continuous f :=
  uniform_limit_continuous_net F f hF hlim

/-- Embed the continuous maps, with the specified metric D, into the complete
space of all maps with its uniform convergence structure. The range is closed
because a uniform limit of continuous maps is continuous. -/
theorem uniformContinuousMetric_complete [CompleteSpace Y] :
    @CompleteSpace (ContinuousMaps X Y) uniformContinuousMetric.toUniformSpace := by
  let : MetricSpace (ContinuousMaps X Y) := uniformContinuousMetric
  let e : ContinuousMaps X Y → UniformFun X Y := fun f => UniformFun.ofFun (f : X → Y)
  have he : IsUniformInducing e := by
    constructor
    change comap _ _ = @uniformity (ContinuousMaps X Y) uniformContinuousMetric.toUniformSpace
    change comap _ _ = comap _ (@uniformity (X → Y) uniformMetric.toUniformSpace)
    rw [← uniformUniformity_eq_metric]
    change comap _ _ = comap _ (comap _ _)
    rw [comap_comap]
    rfl
  apply he.completeSpace
  have hr : range e = {f : UniformFun X Y | Continuous (UniformFun.toFun f)} := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact g.continuous
    · intro hf
      exact ⟨⟨UniformFun.toFun f, hf⟩, UniformFun.ofFun_toFun f⟩
  rw [hr]
  exact (UniformFun.isClosed_setOfPred_continuous (α := X) (β := Y)).isComplete

theorem uniform_continuous_complete
    (hY : Ch09.SequentiallyComplete (inferInstance : MetricSpace Y).toPseudoMetricSpace) :
    ∃ m : MetricSpace (ContinuousMaps X Y),
      (∀ f g, @dist _ m.toDist f g = uniformDistance (f : X → Y) (g : X → Y)) ∧
      m.toUniformSpace.toTopologicalSpace = uniformContinuousTopology ∧
      Ch09.SequentiallyComplete m.toPseudoMetricSpace ∧
      @Ch12.Complete (ContinuousMaps X Y) m.toUniformSpace := by
  let : CompleteSpace Y := (Ch09.sequentiallyComplete_iff_mathlib _).mp hY
  have hc := uniformContinuousMetric_complete (X := X) (Y := Y)
  have hs : Ch09.SequentiallyComplete
      (uniformContinuousMetric (X := X) (Y := Y)).toPseudoMetricSpace :=
    (Ch09.sequentiallyComplete_iff_mathlib _).mpr hc
  refine ⟨uniformContinuousMetric, fun _ _ => rfl, ?_,
    hs, (Ch12.metric_complete_iff_sequentiallyComplete _).mpr hs⟩
  change TopologicalSpace.induced _ uniformMetric.toUniformSpace.toTopologicalSpace =
    TopologicalSpace.induced _ uniformTopology
  rw [uniformTopology_eq_metric]

end D10Topology.Ch13
