import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods

/-! Metric conventions for paper.tex: d10:09:metric, d10:09:equivalences,
d10:09:complete-definition, d10:09:total-bounded, and the extended diameter
in d10:09:cantor-intersection.
All distances are finite real numbers. Only diameter takes values in the extended
nonnegative reals. No nonempty-space assumption is imposed.
-/
open Set Filter
open scoped Topology ENNReal NNReal
universe u v

namespace Specs.D10Topology.Ch09.MetricConventions

/-- Canonical finite real-valued metrics. -/
def MetricType := (X : Type u) → Type u
def Metric : MetricType := fun X => MetricSpace X

/-- Distinct points may have zero distance. -/
def PseudometricType := (X : Type u) → Type u
def Pseudometric : PseudometricType := fun X => PseudoMetricSpace X

def distanceType := {X : Type u} → PseudoMetricSpace X → X → X → ℝ
def distance : distanceType := fun d => @dist _ d.toDist

def PseudometricAxiomsType := {X : Type u} → (X → X → ℝ) → Prop
def PseudometricAxioms : PseudometricAxiomsType := fun d =>
  (∀ x y, 0 ≤ d x y) ∧ (∀ x, d x x = 0) ∧
    (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z)

def MetricAxiomsType := {X : Type u} → (X → X → ℝ) → Prop
def MetricAxioms : MetricAxiomsType := fun d => PseudometricAxioms d ∧ ∀ x y, d x y = 0 ↔ x = y

/-- For positive r this is the paper's open ball; other radii are also allowed. -/
def ballType := {X : Type u} → PseudoMetricSpace X → X → ℝ → Set X
def ball : ballType := fun d x r => {y | distance d x y < r}

def metricTopologyType := {X : Type u} → PseudoMetricSpace X → TopologicalSpace X
def metricTopology : metricTopologyType := fun d => d.toUniformSpace.toTopologicalSpace

def MetrizableType := {X : Type u} → TopologicalSpace X → Prop
def Metrizable : MetrizableType := fun t => ∃ d : MetricSpace _, metricTopology d.toPseudoMetricSpace = t

def TopologicallyEquivalentType := {X : Type u} → PseudoMetricSpace X → PseudoMetricSpace X → Prop
def TopologicallyEquivalent : TopologicallyEquivalentType := fun d e => ∀ U : Set _, IsOpen[metricTopology d] U ↔ IsOpen[metricTopology e] U

/-- The same delta works for every pair of points. -/
def UniformlyContinuousType := {X : Type u} → {Y : Type v} → PseudoMetricSpace X → PseudoMetricSpace Y → (X → Y) → Prop
def UniformlyContinuous : UniformlyContinuousType := fun d e f => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
  ∀ x x', distance d x x' < δ → distance e (f x) (f x') < ε

def UniformlyEquivalentType := {X : Type u} → PseudoMetricSpace X → PseudoMetricSpace X → Prop
def UniformlyEquivalent : UniformlyEquivalentType := fun d e => UniformlyContinuous d e id ∧ UniformlyContinuous e d id

/-- The full real-parameter inequality; the library bridge specializes to nonnegative L. -/
def LipschitzType := {X : Type u} → {Y : Type v} → PseudoMetricSpace X → PseudoMetricSpace Y → ℝ → (X → Y) → Prop
def Lipschitz : LipschitzType := fun d e L f => ∀ x y, distance e (f x) (f y) ≤ L * distance d x y

def IsometryType := {X : Type u} → {Y : Type v} → PseudoMetricSpace X → PseudoMetricSpace Y → (X → Y) → Prop
def Isometry : IsometryType := fun d e f => ∀ x y, distance e (f x) (f y) = distance d x y

def IsometricIsomorphismType := {X : Type u} → {Y : Type v} → MetricSpace X → MetricSpace Y → (X → Y) → Prop
def IsometricIsomorphism : IsometricIsomorphismType := fun d e f => Isometry d.toPseudoMetricSpace e.toPseudoMetricSpace f ∧ Function.Surjective f

def BilipschitzEquivalentType := {X : Type u} → PseudoMetricSpace X → PseudoMetricSpace X → Prop
def BilipschitzEquivalent : BilipschitzEquivalentType := fun d e => ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
  ∀ x y, c * distance d x y ≤ distance e x y ∧ distance e x y ≤ C * distance d x y

/-- Natural-number indices start at zero; reindexing the paper's n≥1 changes no tail condition. -/
def CauchySequenceType := {X : Type u} → PseudoMetricSpace X → (ℕ → X) → Prop
def CauchySequence : CauchySequenceType := fun d s => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
  ∀ m, N ≤ m → ∀ n, N ≤ n → distance d (s m) (s n) < ε

def SequenceConvergesType := {X : Type u} → PseudoMetricSpace X → (ℕ → X) → X → Prop
def SequenceConverges : SequenceConvergesType := fun d s x => ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
  ∀ n, N ≤ n → distance d (s n) x < ε

def SequentiallyCompleteType := {X : Type u} → PseudoMetricSpace X → Prop
def SequentiallyComplete : SequentiallyCompleteType := fun d => ∀ s : ℕ → _, CauchySequence d s → ∃ x, SequenceConverges d s x

/-- Existence of a compatible complete metric, not completeness of an arbitrary compatible metric. -/
def CompletelyMetrizableType := {X : Type u} → TopologicalSpace X → Prop
def CompletelyMetrizable : CompletelyMetrizableType := fun t => ∃ d : MetricSpace _, metricTopology d.toPseudoMetricSpace = t ∧
  SequentiallyComplete d.toPseudoMetricSpace

/-- Finite centers lie in the actual space. The finite set may be empty. -/
def TotallyBoundedType := {X : Type u} → PseudoMetricSpace X → Prop
def TotallyBounded : TotallyBoundedType := fun d => ∀ ε : ℝ, 0 < ε → ∃ F : Set _, F.Finite ∧
  (⋃ c ∈ F, ball d c ε) = Set.univ

/-- Extended diameter: no boundedness hypothesis or real-valued truncation. -/
def diameterType := {X : Type u} → PseudoMetricSpace X → Set X → ℝ≥0∞
noncomputable def diameter : diameterType := fun d A => ⨆ x ∈ A, ⨆ y ∈ A, ENNReal.ofReal (distance d x y)

def pseudometric_representation : Prop :=
  ∀ {X : Type u} (f : X → X → ℝ),
  PseudometricAxioms f ↔ ∃ d : PseudoMetricSpace X, distance d = f

def metric_representation : Prop :=
  ∀ {X : Type u} (f : X → X → ℝ),
  MetricAxioms f ↔ ∃ d : MetricSpace X, distance d.toPseudoMetricSpace = f

def ball_eq_mathlib : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (x : X) (r : ℝ),
  ball d x r = @Metric.ball X d x r

def metricTopology_open_iff : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (U : Set X),
  IsOpen[metricTopology d] U ↔ ∀ x ∈ U, ∃ r > 0, ball d x r ⊆ U

def metrizable_iff_mathlib : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X),
  Metrizable t ↔ @TopologicalSpace.MetrizableSpace X t

def topologicallyEquivalent_iff_topology_eq : Prop :=
  ∀ {X : Type u} (d e : PseudoMetricSpace X),
  TopologicallyEquivalent d e ↔ metricTopology d = metricTopology e

def uniformlyContinuous_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : PseudoMetricSpace X)
    (e : PseudoMetricSpace Y) (f : X → Y),
  UniformlyContinuous d e f ↔ @UniformContinuous X Y d.toUniformSpace e.toUniformSpace f

def uniformlyEquivalent_iff_mathlib : Prop :=
  ∀ {X : Type u} (d e : PseudoMetricSpace X),
  UniformlyEquivalent d e ↔
    @UniformContinuous X X d.toUniformSpace e.toUniformSpace id ∧
    @UniformContinuous X X e.toUniformSpace d.toUniformSpace id

def lipschitz_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : PseudoMetricSpace X)
    (e : PseudoMetricSpace Y) (L : ℝ≥0) (f : X → Y),
  Lipschitz d e (L : ℝ) f ↔ @LipschitzWith X Y
    (@PseudoMetricSpace.toPseudoEMetricSpace X d)
    (@PseudoMetricSpace.toPseudoEMetricSpace Y e) L f

def isometry_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : PseudoMetricSpace X)
    (e : PseudoMetricSpace Y) (f : X → Y),
  Isometry d e f ↔ @_root_.Isometry X Y
    (@PseudoMetricSpace.toPseudoEMetricSpace X d)
    (@PseudoMetricSpace.toPseudoEMetricSpace Y e) f

def isometricIsomorphism_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} (d : MetricSpace X)
    (e : MetricSpace Y) (f : X → Y),
  IsometricIsomorphism d e f ↔ ∃ g : @IsometryEquiv X Y
    (@PseudoMetricSpace.toPseudoEMetricSpace X d.toPseudoMetricSpace)
    (@PseudoMetricSpace.toPseudoEMetricSpace Y e.toPseudoMetricSpace), (g : X → Y) = f

def cauchySequence_iff_mathlib : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (s : ℕ → X),
  CauchySequence d s ↔ @CauchySeq X ℕ d.toUniformSpace _ s

def sequenceConverges_iff_mathlib : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (s : ℕ → X) (x : X),
  SequenceConverges d s x ↔ Filter.Tendsto s Filter.atTop (@nhds X (metricTopology d) x)

def sequentiallyComplete_iff_mathlib : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X),
  SequentiallyComplete d ↔ @CompleteSpace X d.toUniformSpace

def completelyMetrizable_iff_mathlib : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X),
  CompletelyMetrizable t ↔ @TopologicalSpace.IsCompletelyMetrizableSpace X t

def totallyBounded_iff_mathlib : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X),
  TotallyBounded d ↔ @_root_.TotallyBounded X d.toUniformSpace Set.univ

def diameter_eq_mathlib : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (A : Set X),
  diameter d A = @Metric.ediam X (@PseudoMetricSpace.toEDist X d) A

def diameter_empty : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X), diameter d (∅ : Set X) = 0

def diameter_le_iff : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (A : Set X) (r : ℝ≥0∞),
  diameter d A ≤ r ↔ ∀ x ∈ A, ∀ y ∈ A, ENNReal.ofReal (distance d x y) ≤ r

def diameter_eq_top_iff : Prop :=
  ∀ {X : Type u} (d : PseudoMetricSpace X) (A : Set X),
  diameter d A = ⊤ ↔ ∀ R : ℝ≥0∞, R < ⊤ →
    ∃ x ∈ A, ∃ y ∈ A, R < ENNReal.ofReal (distance d x y)

def empty_complete : Prop :=
  ∀ {X : Type u} [IsEmpty X] (d : PseudoMetricSpace X), SequentiallyComplete d

def empty_totallyBounded : Prop :=
  ∀ {X : Type u} [IsEmpty X] (d : PseudoMetricSpace X), TotallyBounded d

end Specs.D10Topology.Ch09.MetricConventions
