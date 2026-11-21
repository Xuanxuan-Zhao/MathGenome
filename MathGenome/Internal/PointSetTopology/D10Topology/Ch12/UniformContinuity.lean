import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformContinuity
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions

/-! Uniform continuity calculus and the arctangent counterexample.
The pullback metric is kept explicit throughout, so no global instance changes
can identify its uniformity with the usual real uniformity accidentally. -/

open Set Filter
open scoped Topology Uniformity
universe u v w

namespace D10Topology.Ch12

@[instance_reducible] noncomputable def usualRealMetric : MetricSpace ℝ :=
  Specs.D10Topology.Ch12.UniformContinuity.usualRealMetric
@[instance_reducible] noncomputable def arctanMetric : MetricSpace ℝ :=
  Specs.D10Topology.Ch12.UniformContinuity.arctanMetric

theorem entourageContinuous_continuous {X : Type u} {Y : Type v}
    [UniformSpace X] [UniformSpace Y] (f : X → Y) (hf : EntourageContinuous f) :
    @Continuous X Y uniformTopology uniformTopology f := by
  rw [uniformTopology_eq_canonical, uniformTopology_eq_canonical]
  exact ((entourageContinuous_iff_mathlib f).mp hf).continuous

theorem entourageContinuous_id {X : Type u} [UniformSpace X] :
    EntourageContinuous (id : X → X) :=
  (entourageContinuous_iff_mathlib id).mpr uniformContinuous_id

theorem entourageContinuous_comp {X : Type u} {Y : Type v} {Z : Type w}
    [UniformSpace X] [UniformSpace Y] [UniformSpace Z] (f : X → Y) (g : Y → Z)
    (hf : EntourageContinuous f) (hg : EntourageContinuous g) :
    EntourageContinuous (g ∘ f) :=
  (entourageContinuous_iff_mathlib _).mpr
    (((entourageContinuous_iff_mathlib g).mp hg).comp
      ((entourageContinuous_iff_mathlib f).mp hf))

theorem usualRealMetric_distance (x y : ℝ) :
    Ch09.distance usualRealMetric.toPseudoMetricSpace x y = |x - y| := rfl

theorem arctanMetric_distance (x y : ℝ) :
    Ch09.distance arctanMetric.toPseudoMetricSpace x y =
      |Real.arctan x - Real.arctan y| := rfl

theorem arctanMetric_topology :
    Ch09.metricTopology arctanMetric.toPseudoMetricSpace =
      Ch09.metricTopology usualRealMetric.toPseudoMetricSpace := by
  exact (Real.arctan_strictMono.isEmbedding_of_ordConnected
    (by rw [Real.range_arctan]; infer_instance)).isInducing.eq_induced.symm

theorem usualRealMetric_complete : @Complete ℝ usualRealMetric.toUniformSpace :=
  complete_iff_mathlib.mpr inferInstance

private theorem arctan_nat_tendsto :
    Tendsto (fun n : ℕ => Real.arctan (n : ℝ)) atTop (𝓝 (Real.pi / 2)) :=
  (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp tendsto_natCast_atTop_atTop

theorem arctanMetric_nat_cauchy :
    Ch09.CauchySequence arctanMetric.toPseudoMetricSpace (fun n : ℕ => (n : ℝ)) := by
  exact (Ch09.cauchySequence_iff_mathlib usualRealMetric.toPseudoMetricSpace
    (fun n : ℕ => Real.arctan (n : ℝ))).mpr arctan_nat_tendsto.cauchySeq

theorem arctanMetric_nat_no_limit :
    ¬ ∃ x : ℝ, Ch09.SequenceConverges arctanMetric.toPseudoMetricSpace
      (fun n : ℕ => (n : ℝ)) x := by
  rintro ⟨x, hx⟩
  have ht := (Ch09.sequenceConverges_iff_mathlib usualRealMetric.toPseudoMetricSpace
    (fun n : ℕ => Real.arctan (n : ℝ)) (Real.arctan x)).mp hx
  change Tendsto (fun n : ℕ => Real.arctan (n : ℝ)) atTop (𝓝 (Real.arctan x)) at ht
  have he := tendsto_nhds_unique ht arctan_nat_tendsto
  exact (Real.arctan_lt_pi_div_two x).ne he

theorem arctanMetric_incomplete : ¬ @Complete ℝ arctanMetric.toUniformSpace := by
  intro h
  have hc := (Ch09.sequentiallyComplete_iff_mathlib arctanMetric.toPseudoMetricSpace).mpr
    ((@complete_iff_mathlib ℝ arctanMetric.toUniformSpace).mp h)
  exact arctanMetric_nat_no_limit (hc _ arctanMetric_nat_cauchy)

theorem arctanMetric_adjacent_tendsto :
    Tendsto (fun n : ℕ => Ch09.distance arctanMetric.toPseudoMetricSpace
      (n : ℝ) ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun n : ℕ => Real.arctan ((n : ℝ) + 1)) atTop
      (𝓝 (Real.pi / 2)) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      arctan_nat_tendsto.comp (tendsto_add_atTop_nat 1)
  simpa only [arctanMetric_distance, sub_self, abs_zero] using
    (arctan_nat_tendsto.sub hs).abs

theorem usualRealMetric_adjacent (n : ℕ) :
    Ch09.distance usualRealMetric.toPseudoMetricSpace (n : ℝ) ((n : ℝ) + 1) = 1 := by
  rw [usualRealMetric_distance]
  norm_num

theorem arctanMetric_id_not_uniform :
    ¬ @EntourageContinuous ℝ ℝ arctanMetric.toUniformSpace
      usualRealMetric.toUniformSpace id := by
  intro h
  have hm := (Ch09.uniformlyContinuous_iff_mathlib arctanMetric.toPseudoMetricSpace
    usualRealMetric.toPseudoMetricSpace id).mpr
      ((@entourageContinuous_iff_mathlib ℝ ℝ arctanMetric.toUniformSpace
        usualRealMetric.toUniformSpace id).mp h)
  obtain ⟨δ, hδ, hh⟩ := hm 1 zero_lt_one
  have hev := arctanMetric_adjacent_tendsto.eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  have hn' := hh (n : ℝ) ((n : ℝ) + 1) hn
  have : (1 : ℝ) < 1 := by simpa only [id_eq, usualRealMetric_adjacent] using hn'
  exact (lt_irrefl (1 : ℝ)) this

theorem arctanMetric_uniformity_ne :
    arctanMetric.toUniformSpace ≠ usualRealMetric.toUniformSpace := by
  intro h
  apply arctanMetric_id_not_uniform
  rw [h]
  exact entourageContinuous_id

end D10Topology.Ch12
