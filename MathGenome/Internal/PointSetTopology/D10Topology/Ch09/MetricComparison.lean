import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricComparison
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CauchyBasics
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.TotalBoundedPermanence
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CompactEquivalences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

open Set Filter
open scoped Topology
universe u v
namespace D10Topology.Ch09

private theorem refinement_opens {X : Type u} (d e : MetricSpace X)
    (h : ∀ x ε, 0 < ε → ∃ δ > 0,
      ball d.toPseudoMetricSpace x δ ⊆ ball e.toPseudoMetricSpace x ε)
    {U : Set X} (hU : IsOpen[metricTopology e.toPseudoMetricSpace] U) :
    IsOpen[metricTopology d.toPseudoMetricSpace] U := by
  rw [metricTopology_open_iff] at hU ⊢
  intro x hx
  obtain ⟨ε, hε, he⟩ := hU x hx
  obtain ⟨δ, hδ, hd⟩ := h x ε hε
  exact ⟨δ, hδ, hd.trans he⟩

theorem topology_comparison {X : Type u} (d e : MetricSpace X) :
    TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace ↔
      (∀ x ε, 0 < ε → ∃ δ > 0, ball d.toPseudoMetricSpace x δ ⊆ ball e.toPseudoMetricSpace x ε) ∧
      (∀ x ε, 0 < ε → ∃ δ > 0, ball e.toPseudoMetricSpace x δ ⊆ ball d.toPseudoMetricSpace x ε) := by
  have one_direction (d e : MetricSpace X)
      (h : TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace) :
      ∀ x ε, 0 < ε → ∃ δ > 0, ball d.toPseudoMetricSpace x δ ⊆ ball e.toPseudoMetricSpace x ε := by
    intro x ε hε
    have he : IsOpen[metricTopology e.toPseudoMetricSpace] (ball e.toPseudoMetricSpace x ε) := by
      let := e
      rw [ball_eq_mathlib]
      exact Metric.isOpen_ball
    have hd := (h _).mpr he
    apply (metricTopology_open_iff _ _).mp hd x
    simpa only [ball, mem_ofPred_eq, distance, @dist_self X e.toPseudoMetricSpace] using hε
  constructor
  · intro h
    exact ⟨one_direction d e h, one_direction e d (fun U => (h U).symm)⟩
  · rintro ⟨hde, hed⟩ U
    exact ⟨refinement_opens e d hed, refinement_opens d e hde⟩

theorem bilipschitz_implies_uniform {X : Type u} (d e : MetricSpace X)
    (h : BilipschitzEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace) :
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace := by
  obtain ⟨c, C, hc, hC, h⟩ := h
  constructor
  · intro ε hε
    refine ⟨ε / C, div_pos hε hC, ?_⟩
    intro x y hxy
    have := (lt_div_iff₀ hC).mp hxy
    exact (h x y).2.trans_lt (by nlinarith)
  · intro ε hε
    refine ⟨c * ε, mul_pos hc hε, ?_⟩
    intro x y hxy
    have := (h x y).1.trans_lt hxy
    exact (mul_lt_mul_iff_right₀ hc).mp this

theorem uniform_implies_topological {X : Type u} (d e : MetricSpace X)
    (h : UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace) :
    TopologicallyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace := by
  apply (topology_comparison d e).mpr
  constructor
  · intro x ε hε
    obtain ⟨δ, hδ, hd⟩ := h.1 ε hε
    exact ⟨δ, hδ, fun y hy => hd x y hy⟩
  · intro x ε hε
    obtain ⟨δ, hδ, hd⟩ := h.2 ε hε
    exact ⟨δ, hδ, fun y hy => hd x y hy⟩

theorem truncated_metric {X : Type u} (d : MetricSpace X) : ∃ e : MetricSpace X,
    (∀ x y, distance e.toPseudoMetricSpace x y = min 1 (distance d.toPseudoMetricSpace x y)) ∧
    UniformlyEquivalent d.toPseudoMetricSpace e.toPseudoMetricSpace := by
  let := d
  let e : MetricSpace X :=
    { dist x y := min 1 (dist x y)
      dist_self x := by simp
      dist_comm x y := by rw [dist_comm]
      dist_triangle x y z := by
        have ht := dist_triangle x y z
        have hxy : 0 ≤ dist x y := dist_nonneg
        have hyz : 0 ≤ dist y z := dist_nonneg
        simp only [min_def]
        split_ifs <;> linarith
      eq_of_dist_eq_zero := by
        intro x y h
        have hd : dist x y = 0 := by
          by_cases hh : (1 : ℝ) ≤ dist x y
          · rw [min_eq_left hh] at h
            norm_num at h
          · rwa [min_eq_right (le_of_not_ge hh)] at h
        exact dist_eq_zero.mp hd }
  let := d
  refine ⟨e, fun _ _ => rfl, ?_, ?_⟩
  · intro ε hε
    exact ⟨ε, hε, fun x y hxy => (min_le_right _ _).trans_lt hxy⟩
  · intro ε hε
    refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
    intro x y hxy
    change min 1 (dist x y) < min 1 ε at hxy
    have hdist : dist x y < 1 := by
      by_contra hn
      rw [min_eq_left (le_of_not_gt hn)] at hxy
      exact (not_lt_of_ge (min_le_left _ _)) hxy
    rw [min_eq_right hdist.le] at hxy
    exact hxy.trans_le (min_le_right _ _)

theorem real_truncation_counterexample : ∃ e : MetricSpace ℝ,
    (∀ x y, distance e.toPseudoMetricSpace x y = min 1 |x-y|) ∧
    UniformlyEquivalent Real.metricSpace.toPseudoMetricSpace e.toPseudoMetricSpace ∧
    ¬ BilipschitzEquivalent Real.metricSpace.toPseudoMetricSpace e.toPseudoMetricSpace := by
  obtain ⟨e, he, hu⟩ := truncated_metric (inferInstance : MetricSpace ℝ)
  refine ⟨e, ?_, hu, ?_⟩
  · simpa only [distance, Real.dist_eq] using he
  · rintro ⟨c, C, hc, _, hb⟩
    have h := (hb 0 (2 / c)).1
    rw [he] at h
    have hnonneg : 0 ≤ 2 / c := (div_pos (by norm_num) hc).le
    change c * |0 - 2 / c| ≤ min 1 |0 - 2 / c| at h
    rw [zero_sub, abs_neg, abs_of_nonneg hnonneg] at h
    have hmul : c * (2 / c) = 2 := by field_simp
    have := h.trans (min_le_left _ _)
    linarith

theorem euclidean_complete (n : ℕ) :
    SequentiallyComplete (inferInstance : MetricSpace (EuclideanSpace ℝ (Fin n))).toPseudoMetricSpace := by
  apply (sequentiallyComplete_iff_mathlib _).mpr
  infer_instance

namespace MetricComparison
abbrev OpenUnitInterval := Specs.D10Topology.Ch09.MetricComparison.OpenUnitInterval
noncomputable abbrev tangentMap := Specs.D10Topology.Ch09.MetricComparison.tangentMap
noncomputable abbrev reciprocalSequence := Specs.D10Topology.Ch09.MetricComparison.reciprocalSequence

/-- The affine change of variable used before applying tangent. -/
noncomputable def angleOrderIso :
    OpenUnitInterval ≃o Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) where
  toFun x := ⟨Real.pi * (x.val - 1 / 2), by
    have hx0 := x.property.1
    have hx1 := x.property.2
    have hp := Real.pi_pos
    constructor <;> nlinarith⟩
  invFun y := ⟨y.val / Real.pi + 1 / 2, by
    have hy0 := y.property.1
    have hy1 := y.property.2
    have hp := Real.pi_pos
    constructor
    · have h : -(1 / 2 : ℝ) < y.val / Real.pi := (lt_div_iff₀ hp).mpr (by linarith)
      linarith
    · have h : y.val / Real.pi < (1 / 2 : ℝ) := (div_lt_iff₀ hp).mpr (by linarith)
      linarith⟩
  left_inv x := by ext; dsimp; field_simp; ring
  right_inv y := by ext; dsimp; field_simp; ring
  map_rel_iff' := by
    intro x y
    change Real.pi * (x.val - 1 / 2) ≤ Real.pi * (y.val - 1 / 2) ↔ x.val ≤ y.val
    rw [mul_le_mul_iff_right₀ Real.pi_pos]
    exact sub_le_sub_iff_right _

noncomputable def tangentHomeomorph : OpenUnitInterval ≃ₜ ℝ :=
  (angleOrderIso.trans Real.tanOrderIso).toHomeomorph

@[simp] theorem tangentHomeomorph_apply (x : OpenUnitInterval) :
    tangentHomeomorph x = tangentMap x := rfl

@[instance_reducible] noncomputable def tangentMetric : MetricSpace OpenUnitInterval :=
  MetricSpace.induced tangentHomeomorph tangentHomeomorph.injective inferInstance

@[simp] theorem tangentMetric_distance (x y : OpenUnitInterval) :
    distance tangentMetric.toPseudoMetricSpace x y = |tangentMap x - tangentMap y| := rfl

theorem tangent_topology :
    TopologicallyEquivalent (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace
      tangentMetric.toPseudoMetricSpace := by
  apply (topologicallyEquivalent_iff_topology_eq _ _).mpr
  exact tangentHomeomorph.isInducing.eq_induced

theorem tangent_complete : SequentiallyComplete tangentMetric.toPseudoMetricSpace := by
  apply (sequentiallyComplete_iff_mathlib _).mpr
  let : PseudoEMetricSpace OpenUnitInterval :=
    tangentMetric.toPseudoMetricSpace.toPseudoEMetricSpace
  let e : @IsometryEquiv OpenUnitInterval ℝ
      tangentMetric.toPseudoMetricSpace.toPseudoEMetricSpace
      Real.metricSpace.toPseudoMetricSpace.toPseudoEMetricSpace :=
    { tangentHomeomorph.toEquiv with
      isometry_toFun := (@isometry_iff_dist_eq _ _ tangentMetric.toPseudoMetricSpace
        Real.metricSpace.toPseudoMetricSpace _).mpr (fun _ _ => rfl) }
  exact e.completeSpace

/-- Its values in ℝ converge to the missing endpoint zero. -/
theorem reciprocal_tendsto_zero :
    Tendsto (fun n => (reciprocalSequence n).val) atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ))
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)

theorem reciprocal_usual_cauchy :
    CauchySequence (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace reciprocalSequence := by
  apply (cauchySequence_iff_mathlib _ _).mpr
  have hc : CauchySeq (fun n => (reciprocalSequence n).val) := reciprocal_tendsto_zero.cauchySeq
  have he := Metric.cauchySeq_iff.mp hc
  exact Metric.cauchySeq_iff.mpr he

private theorem reciprocal_no_usual_limit (x : OpenUnitInterval) :
    ¬ SequenceConverges (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace reciprocalSequence x := by
  intro hx
  have hx' := (sequenceConverges_iff_mathlib _ _ _).mp hx
  have heq := tendsto_nhds_unique
    (continuous_subtype_val.continuousAt.tendsto.comp hx') reciprocal_tendsto_zero
  exact (ne_of_gt x.property.1) heq

theorem usual_interval_incomplete :
    ¬ SequentiallyComplete (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace := by
  intro hc
  obtain ⟨x, hx⟩ := hc reciprocalSequence reciprocal_usual_cauchy
  exact reciprocal_no_usual_limit x hx

theorem reciprocal_tangent_not_cauchy :
    ¬ CauchySequence tangentMetric.toPseudoMetricSpace reciprocalSequence := by
  intro hc
  obtain ⟨x, hx⟩ := tangent_complete reciprocalSequence hc
  apply reciprocal_no_usual_limit x
  apply (sequenceConverges_iff_mathlib _ _ _).mpr
  have ht := (topologicallyEquivalent_iff_topology_eq _ _).mp tangent_topology
  rw [ht]
  exact (sequenceConverges_iff_mathlib _ _ _).mp hx

theorem tangent_not_uniformlyEquivalent :
    ¬ UniformlyEquivalent (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace
      tangentMetric.toPseudoMetricSpace := by
  intro hu
  exact reciprocal_tangent_not_cauchy
    (uniformlyContinuous_cauchy _ tangentMetric id reciprocalSequence hu.1 reciprocal_usual_cauchy)

theorem usual_interval_totallyBounded :
    TotallyBounded (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace := by
  apply (totallyBounded_subspace_iff _).mpr
  exact isCompact_Icc.totallyBounded.subset Ioo_subset_Icc_self

theorem tangent_not_totallyBounded : ¬ TotallyBounded tangentMetric.toPseudoMetricSpace := by
  intro ht
  have hc := (coverCompact_iff_complete_totallyBounded tangentMetric).mpr ⟨tangent_complete, ht⟩
  have hk : @IsCompact OpenUnitInterval
      (metricTopology tangentMetric.toPseudoMetricSpace) univ :=
    (@Ch05.coverCompact_iff_isCompact_univ _
      (metricTopology tangentMetric.toPseudoMetricSpace)).mp hc
  have heq := (topologicallyEquivalent_iff_topology_eq _ _).mp tangent_topology
  rw [← heq] at hk
  have himage := hk.image continuous_subtype_val
  have he : (Subtype.val : OpenUnitInterval → ℝ) '' univ = Set.Ioo (0 : ℝ) 1 := by ext x; simp
  rw [he] at himage
  have := isCompact_Ioo_iff.mp himage
  norm_num at this


/-- A concrete embedding into the compact one-dimensional cube. -/
noncomputable def cubeContraction (x : OpenUnitInterval) : Set.Icc (0 : ℝ) 1 :=
  ⟨x.val / 2, by have hx0 := x.property.1; have hx1 := x.property.2; constructor <;> linarith⟩

theorem cubeContraction_embedding : Topology.IsEmbedding cubeContraction := by
  apply (Topology.IsEmbedding.of_comp_iff
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))).mp
  have h := (Homeomorph.mulRight₀ (1 / 2 : ℝ) (by norm_num)).isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : OpenUnitInterval → ℝ))
  simpa only [Homeomorph.coe_mulRight₀, Function.comp_def, cubeContraction, div_eq_mul_inv,
    one_mul] using h

theorem cubeContraction_not_closed : ¬ IsClosed (range cubeContraction) := by
  intro hc
  have hi := (isClosed_Icc.isClosedEmbedding_subtypeVal).isClosedMap _ hc
  have hr : (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) '' range cubeContraction =
      Set.Ioo (0 : ℝ) (1 / 2) := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      have hx0 := x.property.1
      have hx1 := x.property.2
      change 0 < x.val / 2 ∧ x.val / 2 < 1 / 2
      constructor <;> linarith
    · rintro ⟨hz0, hz1⟩
      let x : OpenUnitInterval := ⟨2 * z, by constructor <;> linarith⟩
      refine ⟨cubeContraction x, ⟨x, rfl⟩, ?_⟩
      change 2 * z / 2 = z
      ring
  rw [hr, isClosed_Ioo_iff] at hi
  norm_num at hi

theorem cubeContraction_not_isometry :
    ¬ Isometry (inferInstance : MetricSpace OpenUnitInterval).toPseudoMetricSpace
      (inferInstance : MetricSpace (Set.Icc (0 : ℝ) 1)).toPseudoMetricSpace cubeContraction := by
  intro hi
  let x : OpenUnitInterval := ⟨1 / 4, by constructor <;> norm_num⟩
  let y : OpenUnitInterval := ⟨3 / 4, by constructor <;> norm_num⟩
  have h := hi x y
  change |(1 / 4 : ℝ) / 2 - (3 / 4 : ℝ) / 2| = |(1 / 4 : ℝ) - 3 / 4| at h
  norm_num at h

end MetricComparison

/-- All the properties concern the very same tangent pullback metric. -/
theorem interval_counterexample : Specs.D10Topology.Ch09.MetricComparison.interval_counterexample := by
  exact ⟨MetricComparison.tangentMetric, MetricComparison.tangentMetric_distance,
    MetricComparison.tangent_topology, MetricComparison.tangent_not_uniformlyEquivalent,
    MetricComparison.reciprocal_usual_cauchy, MetricComparison.reciprocal_tangent_not_cauchy,
    MetricComparison.usual_interval_incomplete, MetricComparison.tangent_complete,
    MetricComparison.usual_interval_totallyBounded, MetricComparison.tangent_not_totallyBounded⟩

theorem cube_embedding_counterexample :
    Specs.D10Topology.Ch09.MetricComparison.cube_embedding_counterexample := by
  exact ⟨MetricComparison.cubeContraction, MetricComparison.cubeContraction_embedding,
    MetricComparison.cubeContraction_not_closed, MetricComparison.cubeContraction_not_isometry,
    MetricComparison.usual_interval_incomplete⟩


theorem cube_cauchy_counterexample :
    Specs.D10Topology.Ch09.MetricComparison.cube_cauchy_counterexample := by
  refine ⟨MetricComparison.tangentMetric, MetricComparison.cubeContraction,
    MetricComparison.tangentMetric_distance, MetricComparison.tangent_topology,
    ?_, MetricComparison.reciprocal_tangent_not_cauchy, ?_⟩
  · change @Topology.IsEmbedding _ _
      (metricTopology MetricComparison.tangentMetric.toPseudoMetricSpace)
      (metricTopology (inferInstance : MetricSpace (Set.Icc (0 : ℝ) 1)).toPseudoMetricSpace)
      MetricComparison.cubeContraction
    have ht := (topologicallyEquivalent_iff_topology_eq _ _).mp MetricComparison.tangent_topology
    exact ht ▸ MetricComparison.cubeContraction_embedding
  · apply (cauchySequence_iff_mathlib _ _).mpr
    have hc : CauchySeq (fun n => (MetricComparison.reciprocalSequence n).val / 2) :=
      (MetricComparison.reciprocal_tendsto_zero.div_const 2).cauchySeq
    have he := Metric.cauchySeq_iff.mp hc
    exact Metric.cauchySeq_iff.mpr he


theorem incomplete_embedding_not_closed {X : Type u} {Y : Type v} (d : MetricSpace X)
    [t : TopologicalSpace Y] [CompactSpace Y] (f : X → Y)
    (hf : @Topology.IsEmbedding X Y (metricTopology d.toPseudoMetricSpace) t f)
    (hn : ¬ SequentiallyComplete d.toPseudoMetricSpace) : ¬ IsClosed (range f) := by
  intro hc
  let := d
  have hk : IsCompact (univ : Set X) := hf.isCompact_iff.mpr (by
    simpa only [image_univ] using hc.isCompact)
  have hcover := (Ch05.coverCompact_iff_isCompact_univ X).mpr hk
  exact hn ((coverCompact_iff_complete_totallyBounded d).mp hcover).1

end D10Topology.Ch09
