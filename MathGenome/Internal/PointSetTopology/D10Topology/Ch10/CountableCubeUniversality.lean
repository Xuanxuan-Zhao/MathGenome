import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.CountableCubeUniversality
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.UrysohnMetrization
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.MetrizableCountability
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.CompactNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.TotalBoundedPermanence
import Mathlib.Topology.MetricSpace.Isometry

/-! The countable cube universality corollary, paper.tex
`d10:10:hilbert-cube-universal`. The product metric on the cube retains
its product topology. Pulling it back along an embedding gives exactly the
given topology and total boundedness, including for an empty domain. -/

open Set Topology TopologicalSpace
universe u

namespace D10Topology.Ch10

/-- Every subspace of the countable cube has a countable basis and is T₃. -/
theorem cube_iff_secondCountable_t3 {X : Type u} [TopologicalSpace X] :
    (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ↔
      SecondCountableTopology X ∧ Ch07.T3 X := by
  constructor
  · rintro ⟨e, he⟩
    letI : T3Space X := he.t3Space
    exact ⟨he.secondCountableTopology, (Ch07.t3_iff_mathlib X).mpr inferInstance⟩
  · rintro ⟨hS, hR, h1⟩
    exact (urysohn_metrization hR hS h1).1

theorem cube_iff_separable_metrizable {X : Type u} [t : TopologicalSpace X] :
    (∃ e : X → (ℕ+ → unitInterval), IsEmbedding e) ↔
      SeparableSpace X ∧ Ch09.Metrizable t := by
  constructor
  · intro h
    obtain ⟨hS, hR, h1⟩ := cube_iff_secondCountable_t3.mp h
    have hm := (urysohn_metrization hR hS h1).2
    exact ⟨(Ch08.metrizable_secondCountable_iff_separable hm).mp hS, hm⟩
  · rintro ⟨hSep, hm⟩
    have hS := (Ch08.metrizable_secondCountable_iff_separable hm).mpr hSep
    letI : MetrizableSpace X := (Ch09.metrizable_iff_mathlib t).mp hm
    exact cube_iff_secondCountable_t3.mpr
      ⟨hS, (Ch07.t3_iff_mathlib X).mpr inferInstance⟩

theorem compact_hausdorff_secondCountable_metrizable {X : Type u}
    [t : TopologicalSpace X] (hc : Ch05.CoverCompact X)
    (h2 : T2Space X) (hS : SecondCountableTopology X) : Ch09.Metrizable t := by
  letI : T2Space X := h2
  letI : NormalSpace X := Ch07.compact_hausdorff_normal hc
  exact (urysohn_metrization inferInstance hS inferInstance).2

/-- The pullback metric may have a different uniformity from any metric
previously chosen on X; only its topology is prescribed. -/
theorem cube_embedding_totallyBounded_metric {X : Type u} [t : TopologicalSpace X]
    (e : X → (ℕ+ → unitInterval)) (he : IsEmbedding e) :
    ∃ d : MetricSpace X, Ch09.metricTopology d.toPseudoMetricSpace = t ∧
      Ch09.TotallyBounded d.toPseudoMetricSpace := by
  letI : MetricSpace (ℕ+ → unitInterval) := PiCountable.metricSpace
  let d : MetricSpace X := he.comapMetricSpace e
  refine ⟨d, rfl, ?_⟩
  letI : MetricSpace X := d
  have hi : _root_.Isometry e := Isometry.of_dist_eq (fun _ _ => rfl)
  apply (Ch09.totallyBounded_iff_mathlib d.toPseudoMetricSpace).mpr
  have hc : _root_.TotallyBounded (univ : Set (ℕ+ → unitInterval)) :=
    isCompact_univ.totallyBounded
  simpa only [preimage_univ] using totallyBounded_preimage hi.isUniformInducing hc

theorem compatible_totallyBounded_metric_iff_separable {X : Type u}
    [t : TopologicalSpace X] (hm : Ch09.Metrizable t) :
    (∃ d : MetricSpace X, Ch09.metricTopology d.toPseudoMetricSpace = t ∧
      Ch09.TotallyBounded d.toPseudoMetricSpace) ↔ SeparableSpace X := by
  constructor
  · rintro ⟨d, rfl, hd⟩
    letI : MetricSpace X := d
    exact Ch09.totallyBounded_separable hd
  · intro hSep
    obtain ⟨e, he⟩ := cube_iff_separable_metrizable.mpr ⟨hSep, hm⟩
    exact cube_embedding_totallyBounded_metric e he

end D10Topology.Ch10
