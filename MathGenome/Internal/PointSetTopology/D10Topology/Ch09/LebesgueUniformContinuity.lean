import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.LebesgueUniformContinuity
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Theorem d10:09:lebesgue of paper.tex.
A uniform ball refinement of the cover gives the Lebesgue number: choose a
point of the nonempty subset, and bound every distance to it by the extended
diameter. Heine--Cantor is transported through the existing metric interfaces.
All compactness assumptions concern the topology of the specified metric. -/

open Set
open scoped Topology
universe u v

namespace D10Topology.Ch09

/-- The Lebesgue number works for every nonempty subset, using extended diameter. -/
theorem lebesgue_number {X : Type u} (d : MetricSpace X)
    (hc : @Ch05.CoverCompact X (metricTopology d.toPseudoMetricSpace))
    (U : Set (Set X))
    (hU : ∀ V ∈ U, IsOpen[metricTopology d.toPseudoMetricSpace] V)
    (hcover : (univ : Set X) ⊆ ⋃₀ U) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ A : Set X, A.Nonempty →
      diameter d.toPseudoMetricSpace A < ENNReal.ofReal ε₀ →
      ∃ V ∈ U, A ⊆ V := by
  let := d
  have hk : IsCompact (univ : Set X) :=
    (Ch05.coverCompact_iff_isCompact_univ X).mp hc
  obtain ⟨δ, hδ, hballs⟩ := lebesgue_number_lemma_of_metric_sUnion hk hU hcover
  refine ⟨δ, hδ, ?_⟩
  intro A hA hdiam
  obtain ⟨a, ha⟩ := hA
  obtain ⟨V, hVU, hV⟩ := hballs a (mem_univ a)
  refine ⟨V, hVU, fun y hy => hV ?_⟩
  have hdist : ENNReal.ofReal (distance d.toPseudoMetricSpace y a) ≤
      diameter d.toPseudoMetricSpace A :=
    le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le a (le_iSup_of_le ha le_rfl)))
  exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp (hdist.trans_lt hdiam)

/-- Every continuous map from a compact metric space is uniformly continuous. -/
theorem compact_continuous_uniformlyContinuous {X : Type u} {Y : Type v}
    (d : MetricSpace X) (e : MetricSpace Y)
    (hc : @Ch05.CoverCompact X (metricTopology d.toPseudoMetricSpace))
    (f : X → Y)
    (hf : @Continuous X Y (metricTopology d.toPseudoMetricSpace)
      (metricTopology e.toPseudoMetricSpace) f) :
    UniformlyContinuous d.toPseudoMetricSpace e.toPseudoMetricSpace f := by
  let := d
  let := e
  let : CompactSpace X := (Ch05.coverCompact_iff_compactSpace X).mp hc
  exact (uniformlyContinuous_iff_mathlib _ _ f).mpr
    (CompactSpace.uniformContinuous_of_continuous hf)

end D10Topology.Ch09
