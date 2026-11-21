import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
Independent statements for paper.tex, d10:11:proper-perfect and
d10:11:proper-calculus. The shared `Proper` predicate includes continuity
and uses compact preimages. Neither `Perfect` nor `Proper` requires
surjectivity or any separation axiom on the source.
-/

open Set Topology
universe u v w

namespace Specs.D10Topology.Ch11.ProperPerfect

open Specs.D10Topology.Ch11.LocalCompactConventions

/-- The library's universally proper notion agrees with perfectness without
separation hypotheses. This is distinct from the source's `Proper`. -/
def perfect_iff_isProperMap : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y), Perfect f ↔ IsProperMap f

def proper_of_isProperMap : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}, IsProperMap f → Proper f

/-- The reverse bridge is asserted only with the source's LCH target. -/
def isProperMap_iff_proper : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    LCH Y → ∀ (f : X → Y), IsProperMap f ↔ Proper f

def proper_of_perfect : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}, Perfect f → Proper f

def perfect_of_proper : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    LCH Y → ∀ {f : X → Y}, Proper f → Perfect f

def proper_iff_perfect : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    LCH Y → ∀ (f : X → Y), Proper f ↔ Perfect f

def proper_comp : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} {g : Y → Z}, Proper g → Proper f → Proper (g ∘ f)

def proper_closed_embedding : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}, IsClosedEmbedding f → Proper f

def proper_closed_inclusion : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] {A : Set X},
    IsClosed A → Proper (Subtype.val : A → X)

def proper_of_compact_domain : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}, Continuous f → Proper f

def compact_domain_of_proper : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {f : X → Y}, Proper f → CompactSpace X

end Specs.D10Topology.Ch11.ProperPerfect
