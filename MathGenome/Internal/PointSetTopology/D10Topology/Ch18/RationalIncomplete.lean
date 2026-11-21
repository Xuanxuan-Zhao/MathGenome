import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.RationalIncomplete
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.NumberTheory.Real.Irrational

/-! Example d10:18:rational-incomplete. Rational density gives a sequence
converging in ℝ to √2. The equality of rational and real distances makes it
Cauchy in ℚ. A rational limit would, under the continuous inclusion into ℝ,
contradict uniqueness of limits and the irrationality of √2.
-/

namespace D10Topology.Ch18
open D10Topology.Ch09
open Filter
open scoped Topology

theorem rational_distance (p q : ℚ) :
    distance (inferInstance : PseudoMetricSpace ℚ) p q = |(p : ℝ) - (q : ℝ)| :=
  Rat.dist_eq p q

theorem rational_cauchy_without_limit :
    ∃ s : ℕ → ℚ,
      CauchySequence (inferInstance : PseudoMetricSpace ℚ) s ∧
      SequenceConverges (inferInstance : PseudoMetricSpace ℝ)
        (fun n => (s n : ℝ)) (Real.sqrt 2) ∧
      ∀ q : ℚ, ¬ SequenceConverges (inferInstance : PseudoMetricSpace ℚ) s q := by
  obtain ⟨s, _, _, hs⟩ := Real.exists_seq_rat_strictMono_tendsto (Real.sqrt 2)
  have hc : CauchySeq s := by
    rw [Metric.cauchySeq_iff]
    simpa only [Rat.dist_cast] using Metric.cauchySeq_iff.mp hs.cauchySeq
  refine ⟨s, (cauchySequence_iff_mathlib _ _).mpr hc,
    (sequenceConverges_iff_mathlib _ _ _).mpr hs, ?_⟩
  intro q hq
  have hqR : Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (q : ℝ)) :=
    Rat.continuous_coe_real.continuousAt.tendsto.comp
      ((sequenceConverges_iff_mathlib _ _ _).mp hq)
  exact irrational_sqrt_two ⟨q, tendsto_nhds_unique hqR hs⟩

theorem rational_not_complete :
    ¬ SequentiallyComplete (inferInstance : PseudoMetricSpace ℚ) := by
  intro h
  obtain ⟨s, hc, _, hn⟩ := rational_cauchy_without_limit
  obtain ⟨q, hq⟩ := h s hc
  exact hn q hq

end D10Topology.Ch18
