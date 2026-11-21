import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricCompletion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.PseudometricQuotient
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.PseudometricFamilies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.MetricFilterCompleteness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CompletionUniversal

/-! Separated completion of a specified pseudometric, paper.tex 12.18.
We complete the actual zero-distance quotient. Distance preservation proves
both uniform induction and the exact kernel. Uniformly continuous maps identify
that kernel, descend to the quotient, and extend by the metric universal property.
All constructions and arguments allow empty types. -/
open Set Filter
open scoped Uniformity
universe u v
namespace D10Topology.Ch12

abbrev PseudometricCompletion := @Specs.D10Topology.Ch12.PseudometricCompletion.Completion
noncomputable abbrev pseudometricCompletionMetric :=
  @Specs.D10Topology.Ch12.PseudometricCompletion.completionMetric
abbrev pseudometricCompletionMap := @Specs.D10Topology.Ch12.PseudometricCompletion.completionMap

theorem pseudometricCompletion_distance :
    Specs.D10Topology.Ch12.PseudometricCompletion.map_distance := by
  intro X q x y
  exact (Ch09.completion_isometry (metricQuotientMetric q)
    (metricQuotientMap q x) (metricQuotientMap q y)).trans
    (metricQuotient_distance_formula q x y)

theorem pseudometricCompletion_dense :
    Specs.D10Topology.Ch12.PseudometricCompletion.map_dense := by
  intro X q
  let := q
  let := metricQuotientMetric q
  let := pseudometricCompletionMetric q
  have hr : Set.range (pseudometricCompletionMap q) =
      Set.range (Ch09.completionEmbedding (metricQuotientMetric q)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨metricQuotientMap q x, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨x, rfl⟩ := metricQuotient_map_surjective q a
      exact ⟨x, rfl⟩
  change Dense (Set.range (pseudometricCompletionMap q))
  rw [hr]
  exact Ch09.completion_dense (metricQuotientMetric q)

/-- An isometry of pseudometric spaces induces the exact uniformity, even
when it identifies points at distance zero. -/
theorem pseudometricCompletion_isUniformInducing {X : Type u} (q : PseudoMetricSpace X) :
    @IsUniformInducing X (PseudometricCompletion q) q.toUniformSpace
      (pseudometricCompletionMetric q).toUniformSpace (pseudometricCompletionMap q) := by
  let := q
  let := pseudometricCompletionMetric q
  exact (_root_.Isometry.of_dist_eq (pseudometricCompletion_distance q)).isUniformInducing

theorem pseudometricCompletion_inverse_image_uniformity :
    Specs.D10Topology.Ch12.PseudometricCompletion.inverse_image_uniformity := by
  intro X q
  let := q
  let := metricQuotientMetric q
  let := pseudometricCompletionMetric q
  exact (pseudometricCompletion_isUniformInducing q).comap_uniformSpace

theorem pseudometricCompletion_inverse_image_entourages :
    Specs.D10Topology.Ch12.PseudometricCompletion.inverse_image_entourages := by
  intro X q
  let := q
  let := metricQuotientMetric q
  let := pseudometricCompletionMetric q
  exact (pseudometricCompletion_isUniformInducing q).comap_uniformity

theorem pseudometricCompletion_map_eq_iff :
    Specs.D10Topology.Ch12.PseudometricCompletion.map_eq_iff := by
  intro X q x y
  let := q
  let := pseudometricCompletionMetric q
  rw [← dist_eq_zero, pseudometricCompletion_distance q]

theorem pseudometricCompletion_uniformEmbedding_iff :
    Specs.D10Topology.Ch12.PseudometricCompletion.uniformEmbedding_iff := by
  intro X q
  let := q
  let := metricQuotientMetric q
  let := pseudometricCompletionMetric q
  constructor
  · intro h x y hxy
    exact h.injective ((pseudometricCompletion_map_eq_iff q x y).mpr hxy)
  · intro h
    exact ⟨pseudometricCompletion_isUniformInducing q,
      fun x y hxy => h x y ((pseudometricCompletion_map_eq_iff q x y).mp hxy)⟩

theorem pseudometricCompletion_embedding_iff :
    Specs.D10Topology.Ch12.PseudometricCompletion.embedding_iff := by
  intro X q
  let := q
  let := metricQuotientMetric q
  let := pseudometricCompletionMetric q
  constructor
  · intro h x y hxy
    exact h.injective ((pseudometricCompletion_map_eq_iff q x y).mpr hxy)
  · intro h
    exact ((pseudometricCompletion_uniformEmbedding_iff q).mpr h).isEmbedding

theorem pseudometricCompletion_complete_separated :
    Specs.D10Topology.Ch12.PseudometricCompletion.complete_separated := by
  intro X q
  let := pseudometricCompletionMetric q
  exact ⟨(metric_complete_iff_sequentiallyComplete _).mpr
    (Ch09.completion_complete (metricQuotientMetric q)),
    separated_iff_mathlib.mpr inferInstance⟩

theorem pseudometricCompletion_empty :
    Specs.D10Topology.Ch12.PseudometricCompletion.completion_empty := by
  intro X hX q
  let := metricQuotient_empty q
  exact Ch09.completion_empty (metricQuotientMetric q)

/-- Epsilon-delta uniform continuity forces the image distance to be zero. -/
theorem uniformlyContinuous_identifies_zero :
    Specs.D10Topology.Ch12.PseudometricCompletion.zero_identification := by
  intro X Y q e f hf x y hxy
  let := e
  apply dist_eq_zero.mp
  by_contra hne
  have hpos : 0 < dist (f x) (f y) := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  obtain ⟨δ, hδ, hm⟩ := hf _ hpos
  have hsmall : Specs.D10Topology.Ch09.MetricConventions.distance q x y < δ := by
    change @dist X q.toDist x y < δ
    rw [hxy]
    exact hδ
  exact lt_irrefl _ (hm x y hsmall)

theorem pseudometricQuotient_factorization :
    Specs.D10Topology.Ch12.PseudometricCompletion.quotient_factorization := by
  intro X Y q e f hf
  let := q
  let := e
  let := metricQuotientMetric q
  have hrespect : ∀ a b : X, Inseparable a b → f a = f b :=
    fun a b h => uniformlyContinuous_identifies_zero q e f hf a b
      (Metric.inseparable_iff.mp h)
  let f₀ : MetricQuotient q → Y := SeparationQuotient.lift f hrespect
  have hf₀ : Ch09.UniformlyContinuous (metricQuotientMetric q).toPseudoMetricSpace
      e.toPseudoMetricSpace f₀ := by
    apply (Ch09.uniformlyContinuous_iff_mathlib _ _ _).mpr
    exact (SeparationQuotient.uniformContinuous_lift hrespect).mpr
      ((Ch09.uniformlyContinuous_iff_mathlib _ _ _).mp hf)
  have heq : f₀ ∘ metricQuotientMap q = f := by
    funext x
    exact SeparationQuotient.lift_mk hrespect x
  refine ⟨f₀, ⟨hf₀, heq⟩, ?_⟩
  intro g hg
  funext a
  obtain ⟨x, rfl⟩ := metricQuotient_map_surjective q a
  exact (congrFun hg.2 x).trans (congrFun heq x).symm

theorem pseudometricCompletion_extension :
    Specs.D10Topology.Ch12.PseudometricCompletion.extension := by
  intro X Y q e f hc hf
  obtain ⟨f₀, hf₀, _⟩ := pseudometricQuotient_factorization q e f hf
  obtain ⟨g, hg, huniq⟩ := Ch09.completion_extension (metricQuotientMetric q) e f₀ hc hf₀.1
  refine ⟨g, ⟨hg.1, ?_⟩, ?_⟩
  · exact (congrArg (fun h => h ∘ metricQuotientMap q) hg.2).trans hf₀.2
  · intro h hh
    apply huniq h
    refine ⟨hh.1, ?_⟩
    funext a
    obtain ⟨x, rfl⟩ := metricQuotient_map_surjective q a
    exact (congrFun hh.2 x).trans (congrFun hf₀.2 x).symm

theorem countable_pseudometric_completion :
    Specs.D10Topology.Ch12.PseudometricCompletion.countable_family_completion := by
  intro X p
  obtain ⟨q, hd, hu⟩ := weighted_uniformity p
  have hsep : (∀ x y, @dist X q.toDist x y = 0 → x = y) ↔ SeparatesPairs p := by
    change (∀ x y, @dist X q.toDist x y = 0 → x = y) ↔
      Specs.D10Topology.Ch12.PseudometricFamilies.SeparatesPairs p
    rw [← weighted_metric_iff p]
    constructor
    · intro h
      refine ⟨weighted_pseudometric_axioms p, fun x y => ⟨?_, ?_⟩⟩
      · intro hxy
        exact h x y (by rw [hd]; exact hxy)
      · rintro rfl
        exact (weighted_pseudometric_axioms p).2.1 x
    · intro h x y hxy
      exact (h.2 x y).mp (by rw [← hd]; exact hxy)
  refine ⟨q, hd, hu, (pseudometricCompletion_inverse_image_uniformity q).trans hu, ?_, ?_, ?_⟩
  · rw [← hu]
    exact (pseudometricCompletion_uniformEmbedding_iff q).trans hsep
  · rw [← hu]
    exact (pseudometricCompletion_embedding_iff q).trans hsep
  · intro Y e f hc hf
    rw [← hu] at hf
    obtain ⟨g, hg, huniq⟩ := pseudometricCompletion_extension q e f hc
      ((Ch09.uniformlyContinuous_iff_mathlib _ _ _).mpr hf)
    refine ⟨g, ⟨(Ch09.uniformlyContinuous_iff_mathlib _ _ _).mp hg.1, hg.2⟩, ?_⟩
    intro h hh
    exact huniq h ⟨(Ch09.uniformlyContinuous_iff_mathlib _ _ _).mpr hh.1, hh.2⟩

end D10Topology.Ch12
