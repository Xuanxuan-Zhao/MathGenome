import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricFamilies

/-! The countable-base assertions of `d10:12:pseudometric-representation`.
Countable means at most countable. Distances in `PseudoMetricSpace` and
`MetricSpace` are finite real numbers, and compatibility below is equality of
uniform structures, not merely equality of their induced topologies. -/
open Set Filter
open scoped Uniformity
universe u

namespace Specs.D10Topology.Ch12.CountableUniformMetrization

/-- A countable family of entourages refining every entourage. In particular,
finite families are allowed, and no nonemptiness hypothesis on X is imposed. -/
def HasCountableEntourageBase (X : Type u) [UniformSpace X] : Prop :=
  ∃ B : Set (Set (X × X)), B.Countable ∧
    (∀ V ∈ B, V ∈ 𝓤 X) ∧ ∀ U ∈ 𝓤 X, ∃ V ∈ B, V ⊆ U

def hasCountableEntourageBaseType := (X : Type u) → [UniformSpace X] → Prop
def hasCountableEntourageBaseValue : hasCountableEntourageBaseType :=
  @HasCountableEntourageBase

def countable_entourage_base_iff_mathlib : Prop :=
  ∀ {X : Type u} [UniformSpace X],
    HasCountableEntourageBase X ↔ (𝓤 X).IsCountablyGenerated

def countable_uniform_pseudometrization : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X],
    HasCountableEntourageBase X ↔
      ∃ d : PseudoMetricSpace X, d.toUniformSpace = uX

def countable_uniform_metrization : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X], HasCountableEntourageBase X →
    ((∃ d : MetricSpace X, d.toUniformSpace = uX) ↔
      UniformConventions.Separated (X := X))

/-- The zero pseudometric on an empty type generates the degenerate uniformity.
This case has a countable entourage base and is separated. -/
def empty_uniform_pseudometrization : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X] [IsEmpty X],
    HasCountableEntourageBase X ∧
    UniformConventions.Separated (X := X) ∧
    (𝓤 X).sets = {∅} ∧
    (PseudometricFamilies.zeroPseudometric X).toUniformSpace = uX ∧
    ∀ x y : X, @dist X (PseudometricFamilies.zeroPseudometric X).toDist x y = 0

end Specs.D10Topology.Ch12.CountableUniformMetrization
