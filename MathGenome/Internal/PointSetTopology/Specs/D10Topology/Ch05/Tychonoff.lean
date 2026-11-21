import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import Mathlib.Topology.Order.Real

/-!
Independent statements for paper.tex `d10:05:tychonoff`.
Compactness is the source's finite open subcover property. The topology is
the shared initial topology of the coordinate projections. There are no
separation or inhabitedness assumptions in the forward direction.
-/

universe u v

namespace Specs.D10Topology.Ch05.Tychonoff
open Specs.D10Topology.Ch03.Products
open Specs.D10Topology.Ch05.Compactness

def tychonoff_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    (∀ i, @CoverCompact (X i) (tX i)) →
      @CoverCompact (productValue X) (productTopologyValue tX)

def compact_factors_of_nonempty_product : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (productValue X) →
      @CoverCompact (productValue X) (productTopologyValue tX) →
        ∀ i, @CoverCompact (X i) (tX i)

def nonempty_product_compact_iff : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i)),
    Nonempty (productValue X) →
      (@CoverCompact (productValue X) (productTopologyValue tX) ↔
        ∀ i, @CoverCompact (X i) (tX i))

def empty_index_product_compact : Prop :=
  ∀ {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)),
    @CoverCompact (productValue X) (productTopologyValue tX)

def product_compact_of_empty_factor : Prop :=
  ∀ {I : Type u} {X : I → Type v} (tX : ∀ i, TopologicalSpace (X i))
    (i : I) [IsEmpty (X i)],
    @CoverCompact (productValue X) (productTopologyValue tX)

/-- The actual real line has its usual topology, not a discrete surrogate. -/
def real_not_coverCompact : Prop := ¬ CoverCompact ℝ

/-- The binary product has the usual product topology. -/
def empty_real_compact_counterexample : Prop :=
  CoverCompact (Empty × ℝ) ∧ ¬ CoverCompact ℝ

end Specs.D10Topology.Ch05.Tychonoff
