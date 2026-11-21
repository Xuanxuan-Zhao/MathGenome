import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.RationalsNotLocallyCompact
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
Example d10:11:rationals: no point of ℚ has a compact neighborhood.
The dense inclusion into ℝ takes compact sets to closed sets. Were a compact
set a neighborhood in ℚ, its closed image would contain a real neighborhood,
which meets the dense irrational complement. The general dense-inducing
lemma below implements precisely this argument.
-/

open Set Topology

namespace D10Topology.Ch11

theorem rational_topology_induced :
    (inferInstance : TopologicalSpace ℚ) =
      TopologicalSpace.induced ((↑) : ℚ → ℝ) (inferInstance : TopologicalSpace ℝ) :=
  Rat.isEmbedding_coe_real.isInducing.eq_induced

theorem rational_no_compact_neighborhood (q : ℚ) (K : Set ℚ)
    (hK : IsCompact K) : K ∉ 𝓝 q := by
  intro hN
  have hInt : interior K = ∅ :=
    Rat.isDenseEmbedding_coe_real.isDenseInducing.interior_compact_eq_empty
      dense_irrational hK
  have hq : q ∈ interior K := mem_interior_iff_mem_nhds.mpr hN
  rw [hInt] at hq
  exact hq

theorem rational_not_locallyCompact : ¬ LocallyCompact ℚ := by
  intro h
  obtain ⟨K, hK, hN⟩ := (locallyCompact_iff_compact_neighborhood ℚ).mp h 0
  exact rational_no_compact_neighborhood 0 K hK hN

theorem rational_metrizable :
    Specs.D10Topology.Ch09.MetricConventions.Metrizable
      (inferInstance : TopologicalSpace ℚ) :=
  ⟨Rat.instMetricSpace, rfl⟩

theorem real_lch : LCH ℝ :=
  ⟨locallyCompact_of_mathlib_locallyCompactSpace ℝ inferInstance, inferInstance⟩

theorem rational_subspace_counterexample :
    IsEmbedding ((↑) : ℚ → ℝ) ∧
      Specs.D10Topology.Ch09.MetricConventions.Metrizable
        (inferInstance : TopologicalSpace ℚ) ∧
      LCH ℝ ∧ ¬ LocallyCompact ℚ :=
  ⟨Rat.isEmbedding_coe_real, rational_metrizable, real_lch, rational_not_locallyCompact⟩

end D10Topology.Ch11
