import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Topology.Separation.Regular

/-!
Independent statements for paper.tex, d10:11:compact-shrinking.
`LCH` retains the source's one-compact-neighborhood definition. All closures
are in the given ambient topology. No nonemptiness assumptions are made.
-/

open Set
universe u

namespace Specs.D10Topology.Ch11.CompactShrinking

open Specs.D10Topology.Ch11.LocalCompactConventions

/-- Hausdorffness permits upgrading one compact neighborhood to arbitrarily
small compact neighborhoods. -/
def locallyCompact_iff_locallyCompactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X],
    LocallyCompact X ↔ LocallyCompactSpace X

def lch_iff_locallyCompactSpace_and_t2 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    LCH X ↔ LocallyCompactSpace X ∧ T2Space X

def compact_set_shrinking : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ (C U : Set X), IsCompact C → IsOpen U → C ⊆ U →
      ∃ V : Set X, IsOpen V ∧ C ⊆ V ∧ V ⊆ closure V ∧
        closure V ⊆ U ∧ IsCompact (closure V)

def compact_shrinking : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    ∀ (x : X) (U : Set X), IsOpen U → x ∈ U →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ closure V ∧
        closure V ⊆ U ∧ IsCompact (closure V)

/-- Regularity follows without adding a separation axiom to its definition. -/
def lch_regular : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X →
    Specs.D10Topology.Ch07.SeparationConventions.regularValue X

end Specs.D10Topology.Ch11.CompactShrinking
