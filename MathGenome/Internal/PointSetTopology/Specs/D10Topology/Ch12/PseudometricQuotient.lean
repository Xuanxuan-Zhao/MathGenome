import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.MetricSpace.Basic

/-!
The zero-distance quotient in `paper.tex`, d10:12:countable-pseudometrics.
The canonical library separation quotient is used as the carrier. Its class
relation is proved to be precisely zero q-distance in `map_eq_iff`; no
separation or nonemptiness hypothesis is imposed on the original space.
The metric, distance, and class map form the shared interface for completion.
-/
open Set Filter
open scoped Uniformity
universe u

namespace Specs.D10Topology.Ch12.PseudometricQuotient

def ZeroDistance {X : Type u} (q : PseudoMetricSpace X) (x y : X) : Prop :=
  @dist X q.toDist x y = 0

def zeroDistanceType := {X : Type u} → PseudoMetricSpace X → X → X → Prop
def zeroDistanceValue : zeroDistanceType := @ZeroDistance

/-- The carrier of the quotient, retaining the specified pseudometric as a parameter. -/
def MetricQuotient {X : Type u} (q : PseudoMetricSpace X) : Type u :=
  @SeparationQuotient X q.toUniformSpace.toTopologicalSpace

def metricQuotientType := {X : Type u} → PseudoMetricSpace X → Type u
def metricQuotientValue : metricQuotientType := @MetricQuotient

def metricQuotientMap {X : Type u} (q : PseudoMetricSpace X) : X → MetricQuotient q :=
  @SeparationQuotient.mk X q.toUniformSpace.toTopologicalSpace

def metricQuotientMapType := {X : Type u} → (q : PseudoMetricSpace X) → X → MetricQuotient q
def metricQuotientMapValue : metricQuotientMapType := @metricQuotientMap

/-- The library quotient metric descends the original finite real-valued distance. -/
@[instance_reducible]
def metricQuotientMetric {X : Type u} (q : PseudoMetricSpace X) :
    MetricSpace (MetricQuotient q) :=
  @SeparationQuotient.instMetricSpace X q

def metricQuotientMetricType := {X : Type u} → (q : PseudoMetricSpace X) →
  MetricSpace (MetricQuotient q)
def metricQuotientMetricValue : metricQuotientMetricType := @metricQuotientMetric

def metricQuotientDistance {X : Type u} (q : PseudoMetricSpace X) :
    MetricQuotient q → MetricQuotient q → ℝ :=
  @dist _ (metricQuotientMetric q).toDist

def metricQuotientDistanceType := {X : Type u} → (q : PseudoMetricSpace X) →
  MetricQuotient q → MetricQuotient q → ℝ
def metricQuotientDistanceValue : metricQuotientDistanceType := @metricQuotientDistance

/-- Reflexivity, symmetry, and transitivity of exactly the zero-distance relation. -/
def zeroDistance_equivalence : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X), Equivalence (ZeroDistance q)

/-- Changing both representatives by zero distance leaves the distance unchanged. -/
def distance_independent : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X) (x x' y y' : X),
    ZeroDistance q x x' → ZeroDistance q y y' →
      Ch09.MetricConventions.distance q x y = Ch09.MetricConventions.distance q x' y'

/-- This identifies the chosen carrier with the quotient by the paper's relation. -/
def map_eq_iff : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X) (x y : X),
    metricQuotientMap q x = metricQuotientMap q y ↔ ZeroDistance q x y

def map_surjective : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X), Function.Surjective (metricQuotientMap q)

/-- The complete formula q₀([x],[y])=q(x,y). -/
def distance_formula : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X) (x y : X),
    metricQuotientDistance q (metricQuotientMap q x) (metricQuotientMap q y) =
      Ch09.MetricConventions.distance q x y

def metric_axioms : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    Ch09.MetricConventions.MetricAxioms (metricQuotientDistance q)

def entourage_preimage : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X) (ε : ℝ),
    (Prod.map (metricQuotientMap q) (metricQuotientMap q)) ⁻¹'
      {xy | metricQuotientDistance q xy.1 xy.2 < ε} =
      {xy | Ch09.MetricConventions.distance q xy.1 xy.2 < ε}

/-- Equality of uniform structures, rather than just equality of topologies. -/
def inverse_image_uniformity : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    UniformSpace.comap (metricQuotientMap q) (metricQuotientMetric q).toUniformSpace =
      q.toUniformSpace

/-- The corresponding explicit equality of entourage filters. -/
def inverse_image_entourages : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    Filter.comap (Prod.map (metricQuotientMap q) (metricQuotientMap q))
      (@uniformity (MetricQuotient q) (metricQuotientMetric q).toUniformSpace) =
      @uniformity X q.toUniformSpace

/-- The metric topology is the quotient topology for the class map. -/
def map_isQuotientMap : Prop :=
  ∀ {X : Type u} (q : PseudoMetricSpace X),
    @Topology.IsQuotientMap X (MetricQuotient q)
      q.toUniformSpace.toTopologicalSpace
      (metricQuotientMetric q).toUniformSpace.toTopologicalSpace (metricQuotientMap q)

def quotient_empty : Prop :=
  ∀ {X : Type u} [IsEmpty X] (q : PseudoMetricSpace X), IsEmpty (MetricQuotient q)

end Specs.D10Topology.Ch12.PseudometricQuotient
