import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.ContinuityTests
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! Independent interfaces for paper.tex, Definitions 13.1 and 13.9.
The function sets are unrestricted, including empty sets of maps. Topologies
are named explicitly to avoid confusing the product and uniform topologies.
The library uniform convergence structures are justified by the distance and
neighborhood statements below, rather than by an identification by name. -/
noncomputable section
open Set Filter
open scoped Topology Uniformity
universe u v
namespace Specs.D10Topology.Ch13.FunctionTopologies

abbrev AllMaps (X : Type u) (Y : Type v) := X → Y
abbrev ContinuousMaps (X : Type u) (Y : Type v) [TopologicalSpace X]
    [TopologicalSpace Y] := ContinuousMap X Y

def allMapsType := (X : Type u) → (Y : Type v) → Type (max u v)
def continuousMapsType := (X : Type u) → (Y : Type v) →
  [TopologicalSpace X] → [TopologicalSpace Y] → Type (max u v)

def pointwiseTopology {X : Type u} {Y : Type v} [TopologicalSpace Y] :
    TopologicalSpace (X → Y) := inferInstance

def compactOpenSet {X : Type u} {Y : Type v} (K : Set X) (O : Set Y) : Set (X → Y) :=
  {f | f '' K ⊆ O}

def compactOpenTopology {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (X → Y) :=
  TopologicalSpace.generateFrom
    {B | ∃ K : Set X, IsCompact K ∧ ∃ O : Set Y, IsOpen O ∧ B = compactOpenSet K O}

def pointwiseContinuousTopology {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (ContinuousMaps X Y) :=
  TopologicalSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) pointwiseTopology

def compactOpenContinuousTopology {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (ContinuousMaps X Y) :=
  TopologicalSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) compactOpenTopology

def boundedDistance {Y : Type v} [MetricSpace Y] (y z : Y) : ℝ := min 1 (dist y z)

def uniformDistance {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y) : ℝ :=
  ⨆ x : X, boundedDistance (f x) (g x)

def compactDistance {X : Type u} {Y : Type v} [MetricSpace Y]
    (K : Set X) (f g : X → Y) : ℝ :=
  ⨆ x : K, boundedDistance (f x) (g x)

def compactBall {X : Type u} {Y : Type v} [MetricSpace Y]
    (K : Set X) (f : X → Y) (ε : ℝ) : Set (X → Y) :=
  {g | compactDistance K f g < ε}

def uniformUniformity {X : Type u} {Y : Type v} [MetricSpace Y] :
    UniformSpace (X → Y) :=
  UniformSpace.comap UniformFun.ofFun (UniformFun.uniformSpace X Y)

def uniformTopology {X : Type u} {Y : Type v} [MetricSpace Y] :
    TopologicalSpace (X → Y) := uniformUniformity.toTopologicalSpace

def compactConvergenceUniformity {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] : UniformSpace (X → Y) :=
  UniformSpace.comap (UniformOnFun.ofFun {K : Set X | IsCompact K})
    (UniformOnFun.uniformSpace X Y {K : Set X | IsCompact K})

def compactConvergenceTopology {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] : TopologicalSpace (X → Y) :=
  compactConvergenceUniformity.toTopologicalSpace

def uniformContinuousTopology {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] : TopologicalSpace (ContinuousMaps X Y) :=
  TopologicalSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) uniformTopology

def compactConvergenceContinuousUniformity {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] : UniformSpace (ContinuousMaps X Y) :=
  UniformSpace.comap (fun f : ContinuousMaps X Y => (f : X → Y)) compactConvergenceUniformity

def compactConvergenceContinuousTopology {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] : TopologicalSpace (ContinuousMaps X Y) :=
  compactConvergenceContinuousUniformity.toTopologicalSpace

/-- Neighborhoods need not be open. The distance is the original metric d. -/
def EquicontinuousAt {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)) (x : X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 x,
    ∀ y ∈ U, ∀ f ∈ A, dist (f y) (f x) < ε

def Equicontinuous {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y]
    (A : Set (ContinuousMaps X Y)) : Prop := ∀ x, EquicontinuousAt A x

def PointwiseRelativelyCompact {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set (ContinuousMaps X Y)) : Prop :=
  ∀ x : X, IsCompact (closure ((fun f : ContinuousMaps X Y => f x) '' A))

-- Expected types of the canonical definitions (values are the definitions above).
def pointwiseTopologyType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace Y] → TopologicalSpace (X → Y)
def compactOpenSetType := {X : Type u} → {Y : Type v} → Set X → Set Y → Set (X → Y)
def compactOpenTopologyType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] → TopologicalSpace (X → Y)
def continuousTopologyType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] → TopologicalSpace (ContinuousMaps X Y)
def boundedDistanceType := {Y : Type v} → [MetricSpace Y] → Y → Y → ℝ
def uniformDistanceType := {X : Type u} → {Y : Type v} → [MetricSpace Y] → (X → Y) → (X → Y) → ℝ
def compactDistanceType := {X : Type u} → {Y : Type v} → [MetricSpace Y] → Set X → (X → Y) → (X → Y) → ℝ
def compactBallType := {X : Type u} → {Y : Type v} → [MetricSpace Y] → Set X → (X → Y) → ℝ → Set (X → Y)
def uniformUniformityType := {X : Type u} → {Y : Type v} → [MetricSpace Y] → UniformSpace (X → Y)
def uniformTopologyType := {X : Type u} → {Y : Type v} → [MetricSpace Y] → TopologicalSpace (X → Y)
def compactConvergenceUniformityType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [MetricSpace Y] → UniformSpace (X → Y)
def compactConvergenceTopologyType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [MetricSpace Y] → TopologicalSpace (X → Y)
def uniformContinuousTopologyType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [MetricSpace Y] → TopologicalSpace (ContinuousMaps X Y)
def compactConvergenceContinuousUniformityType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [MetricSpace Y] → UniformSpace (ContinuousMaps X Y)
def EquicontinuousAtType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [MetricSpace Y] → Set (ContinuousMaps X Y) → X → Prop
def EquicontinuousType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [MetricSpace Y] → Set (ContinuousMaps X Y) → Prop
def PointwiseRelativelyCompactType := {X : Type u} → {Y : Type v} →
  [TopologicalSpace X] → [TopologicalSpace Y] → Set (ContinuousMaps X Y) → Prop

-- Expected theorem statements. These are full proposition types, not assumed facts.

def boundedDistance_nonneg : Prop :=
  ∀ {Y : Type v} [MetricSpace Y] (y z : Y),
    0 ≤ boundedDistance y z

def boundedDistance_le_one : Prop :=
  ∀ {Y : Type v} [MetricSpace Y] (y z : Y),
    boundedDistance y z ≤ 1

def boundedDistance_self : Prop :=
  ∀ {Y : Type v} [MetricSpace Y] (y : Y),
    boundedDistance y y = 0

def boundedDistance_comm : Prop :=
  ∀ {Y : Type v} [MetricSpace Y] (y z : Y),
    boundedDistance y z = boundedDistance z y

def boundedDistance_triangle : Prop :=
  ∀ {Y : Type v} [MetricSpace Y] (x y z : Y),
    boundedDistance x z ≤ boundedDistance x y + boundedDistance y z

def boundedDistance_eq_zero : Prop :=
  ∀ {Y : Type v} [MetricSpace Y] (y z : Y),
    boundedDistance y z = 0 ↔ y = z

def uniformDistance_nonneg : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y),
    0 ≤ uniformDistance f g

def uniformDistance_le_one : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y),
    uniformDistance f g ≤ 1

def boundedDistance_le_uniformDistance : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y) (x : X),
    boundedDistance (f x) (g x) ≤ uniformDistance f g

def uniformDistance_le : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y) (r : ℝ) (hr : 0 ≤ r),
    uniformDistance f g ≤ r ↔ ∀ x, boundedDistance (f x) (g x) ≤ r

def uniformDistance_self : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f : X → Y),
    uniformDistance f f = 0

def uniformDistance_comm : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y),
    uniformDistance f g = uniformDistance g f

def uniformDistance_triangle : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g h : X → Y),
    uniformDistance f h ≤ uniformDistance f g + uniformDistance g h

def uniformDistance_eq_zero : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y),
    uniformDistance f g = 0 ↔ f = g

def compact_pseudometric_exists : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (K : Set X),
    ∃ m : PseudoMetricSpace (X → Y), @dist _ m.toDist = compactDistance K

def compactDistance_empty : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f g : X → Y),
    compactDistance ∅ f g = 0

def uniformDistance_empty : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [IsEmpty X] (f g : X → Y),
    uniformDistance f g = 0

def continuousMaps_representation : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    Function.Bijective (fun f : ContinuousMaps X Y =>
      (⟨(f : X → Y), f.continuous⟩ : {g : X → Y // Continuous g}))

def compactOpenSet_mem : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (K : Set X) (O : Set Y) (f : X → Y),
    f ∈ compactOpenSet K O ↔ ∀ x ∈ K, f x ∈ O

def compactOpenContinuousTopology_eq_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    compactOpenContinuousTopology (X := X) (Y := Y) = ContinuousMap.compactOpen

def equicontinuousAt_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] (A : Set (ContinuousMaps X Y)) (x : X),
    EquicontinuousAt A x ↔ _root_.EquicontinuousAt (fun f : A => (f.val : X → Y)) x

def equicontinuous_iff_mathlib : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] (A : Set (ContinuousMaps X Y)),
    Equicontinuous A ↔ _root_.Equicontinuous (fun f : A => (f.val : X → Y))

def pointwiseRelativelyCompact_iff_range : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [MetricSpace Y] (A : Set (ContinuousMaps X Y)),
    PointwiseRelativelyCompact A ↔
      ∀ x : X, IsCompact (closure (range (fun f : A => f.val x)))

def compactDistance_nonneg : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (K : Set X) (f g : X → Y),
    0 ≤ compactDistance K f g

def compactDistance_le_one : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (K : Set X) (f g : X → Y),
    compactDistance K f g ≤ 1

def boundedDistance_le_compactDistance : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (K : Set X) (f g : X → Y) (x : X) (hx : x ∈ K),
    boundedDistance (f x) (g x) ≤ compactDistance K f g

def compactDistance_le : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (K : Set X) (f g : X → Y) (r : ℝ) (hr : 0 ≤ r),
    compactDistance K f g ≤ r ↔ ∀ x ∈ K, boundedDistance (f x) (g x) ≤ r

def uniformUniformity_hasBasis : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y],
    (@uniformity (X → Y) uniformUniformity).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {p | uniformDistance p.1 p.2 < ε})

def compactConvergenceUniformity_hasBasis : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X],
    (@uniformity (X → Y) compactConvergenceUniformity).HasBasis
      (fun Ke : Set X × ℝ => IsCompact Ke.1 ∧ 0 < Ke.2)
      (fun Ke => {p | compactDistance Ke.1 p.1 p.2 < Ke.2})

def compactConvergence_uniformity_eq : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X],
    @uniformity (X → Y) compactConvergenceUniformity =
      ⨅ (K : Set X) (_ : IsCompact K) (ε : ℝ) (_ : 0 < ε),
        𝓟 {p | compactDistance K p.1 p.2 < ε}

def compactConvergence_nhds_hasBasis : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X] (f : X → Y),
    (@nhds (X → Y) compactConvergenceTopology f).HasBasis
      (fun Ke : Set X × ℝ => IsCompact Ke.1 ∧ 0 < Ke.2)
      (fun Ke => compactBall Ke.1 f Ke.2)

def uniform_metric_realizes : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y],
    ∃ m : MetricSpace (X → Y),
    @dist _ m.toDist = uniformDistance ∧ m.toUniformSpace = uniformUniformity

def uniform_nhds_hasBasis : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] (f : X → Y),
    (@nhds (X → Y) uniformTopology f).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {g | uniformDistance f g < ε})

def uniform_continuous_metric_realizes : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X],
    ∃ m : MetricSpace (ContinuousMaps X Y),
    (∀ f g, @dist _ m.toDist f g = uniformDistance (f : X → Y) (g : X → Y)) ∧
      m.toUniformSpace.toTopologicalSpace = uniformContinuousTopology

def compact_continuous_pseudometric_exists : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X] (K : Set X),
    ∃ m : PseudoMetricSpace (ContinuousMaps X Y),
      ∀ f g, @dist _ m.toDist f g = compactDistance K (f : X → Y) (g : X → Y)

def compactConvergenceContinuousTopology_eq_induced : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X],
    compactConvergenceContinuousTopology (X := X) (Y := Y) =
      TopologicalSpace.induced (fun f : ContinuousMaps X Y => (f : X → Y)) compactConvergenceTopology

def compactConvergenceContinuous_uniformity_eq : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X],
    @uniformity (ContinuousMaps X Y) compactConvergenceContinuousUniformity =
      ⨅ (K : Set X) (_ : IsCompact K) (ε : ℝ) (_ : 0 < ε),
        𝓟 {p | compactDistance K (p.1 : X → Y) (p.2 : X → Y) < ε}

def compactConvergenceContinuous_nhds_hasBasis : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X] (f : ContinuousMaps X Y),
    (@nhds (ContinuousMaps X Y) compactConvergenceContinuousTopology f).HasBasis
      (fun Ke : Set X × ℝ => IsCompact Ke.1 ∧ 0 < Ke.2)
      (fun Ke => {g | compactDistance Ke.1 (f : X → Y) (g : X → Y) < Ke.2})

def compactConvergence_finite_neighborhoods : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X] (f : X → Y) (N : Set (X → Y)),
    N ∈ @nhds (X → Y) compactConvergenceTopology f ↔
      ∃ F : Finset (Set X × ℝ), (∀ Ke ∈ F, IsCompact Ke.1 ∧ 0 < Ke.2) ∧
        (⋂ Ke ∈ F, compactBall Ke.1 f Ke.2) ⊆ N

def compactConvergenceContinuous_finite_neighborhoods : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace Y] [TopologicalSpace X] (f : ContinuousMaps X Y)
    (N : Set (ContinuousMaps X Y)),
    N ∈ @nhds (ContinuousMaps X Y) compactConvergenceContinuousTopology f ↔
      ∃ F : Finset (Set X × ℝ), (∀ Ke ∈ F, IsCompact Ke.1 ∧ 0 < Ke.2) ∧
        (⋂ Ke ∈ F, {g : ContinuousMaps X Y | compactDistance Ke.1 (f : X → Y) (g : X → Y) < Ke.2}) ⊆ N

def empty_function_topology_unique : Prop :=
  ∀ {X : Type u} {Y : Type v} [IsEmpty (X → Y)]
    (t s : TopologicalSpace (X → Y)),
    t = s

def empty_domain_unique_map : Prop :=
  ∀ {X : Type u} {Y : Type v} [IsEmpty X],
    ∃! f : X → Y, True

def empty_domain_unique_continuous_map : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [IsEmpty X],
    ∃! f : ContinuousMaps X Y, True

end Specs.D10Topology.Ch13.FunctionTopologies
