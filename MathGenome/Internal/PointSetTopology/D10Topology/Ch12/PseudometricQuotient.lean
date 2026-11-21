import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricQuotient
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions

/-!
The metric quotient of one pseudometric (paper.tex,
`d10:12:countable-pseudometrics`, zero-distance part).
Mathlib's separation quotient carries the descended metric. The class-equality
bridge below verifies that its equivalence classes are exactly those of q=0.
All parameters remain explicit, allowing several pseudometrics on one type.
-/
open Set Filter
open scoped Uniformity
universe u

namespace D10Topology.Ch12

abbrev ZeroDistance := @Specs.D10Topology.Ch12.PseudometricQuotient.ZeroDistance
abbrev MetricQuotient := @Specs.D10Topology.Ch12.PseudometricQuotient.MetricQuotient
abbrev metricQuotientMap := @Specs.D10Topology.Ch12.PseudometricQuotient.metricQuotientMap
@[instance_reducible]
def metricQuotientMetric := @Specs.D10Topology.Ch12.PseudometricQuotient.metricQuotientMetric
abbrev metricQuotientDistance :=
  @Specs.D10Topology.Ch12.PseudometricQuotient.metricQuotientDistance

theorem zeroDistance_equivalence :
    Specs.D10Topology.Ch12.PseudometricQuotient.zeroDistance_equivalence := by
  intro X q
  let := q
  refine ⟨fun x => dist_self x, ?_, ?_⟩
  · intro x y hxy
    exact (dist_comm y x).trans hxy
  · intro x y z hxy hyz
    change dist x y = 0 at hxy
    change dist y z = 0 at hyz
    change dist x z = 0
    apply le_antisymm _ dist_nonneg
    calc
      dist x z ≤ dist x y + dist y z := dist_triangle x y z
      _ = 0 := by rw [hxy, hyz, add_zero]

theorem zeroDistance_distance_independent :
    Specs.D10Topology.Ch12.PseudometricQuotient.distance_independent := by
  intro X q x x' y y' hx hy
  let := q
  exact dist_congr hx hy

theorem metricQuotient_map_eq_iff : Specs.D10Topology.Ch12.PseudometricQuotient.map_eq_iff := by
  intro X q x y
  let := q
  exact SeparationQuotient.mk_eq_mk.trans Metric.inseparable_iff

theorem metricQuotient_map_surjective : Specs.D10Topology.Ch12.PseudometricQuotient.map_surjective := by
  intro X q
  let := q
  exact SeparationQuotient.surjective_mk

theorem metricQuotient_distance_formula : Specs.D10Topology.Ch12.PseudometricQuotient.distance_formula := by
  intro X q x y
  rfl

theorem metricQuotient_metric_axioms : Specs.D10Topology.Ch12.PseudometricQuotient.metric_axioms := by
  intro X q
  exact (Ch09.metric_representation _).mpr ⟨metricQuotientMetric q, rfl⟩

theorem metricQuotient_entourage_preimage : Specs.D10Topology.Ch12.PseudometricQuotient.entourage_preimage := by
  intro X q ε
  rfl

theorem metricQuotient_inverse_image_uniformity :
    Specs.D10Topology.Ch12.PseudometricQuotient.inverse_image_uniformity := by
  intro X q
  let := q
  exact UniformSpace.ext SeparationQuotient.comap_mk_uniformity

theorem metricQuotient_inverse_image_entourages :
    Specs.D10Topology.Ch12.PseudometricQuotient.inverse_image_entourages := by
  intro X q
  let := q
  exact SeparationQuotient.comap_mk_uniformity

theorem metricQuotient_map_isQuotientMap : Specs.D10Topology.Ch12.PseudometricQuotient.map_isQuotientMap := by
  intro X q
  let := q
  exact SeparationQuotient.isQuotientMap_mk

theorem metricQuotient_empty : Specs.D10Topology.Ch12.PseudometricQuotient.quotient_empty := by
  intro X hX q
  refine ⟨fun a => ?_⟩
  obtain ⟨x, _⟩ := metricQuotient_map_surjective q a
  exact isEmptyElim x

end D10Topology.Ch12
