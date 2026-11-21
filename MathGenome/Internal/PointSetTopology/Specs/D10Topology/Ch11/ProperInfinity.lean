import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.OnePointConstruction
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.ProperPerfect

/-! Independent statements for paper.tex, d10:11:proper-infinity.
The topology is the accepted `OnePoint` construction, including compact
and empty underlying spaces. Properness includes continuity and compact
preimages, as in the shared source convention. -/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch11.ProperInfinity
open Specs.D10Topology.Ch11.LocalCompactConventions

def plusMapType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → (X → Y) → OnePoint X → OnePoint Y

def plusMapValue : plusMapType := @OnePoint.map

def plusMap_inclusion : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y) (x : X),
    OnePoint.map f (OnePoint.some x) = OnePoint.some (f x)

def plusMap_infinity : Prop :=
  ∀ {X : Type u} {Y : Type v} (f : X → Y),
    OnePoint.map f OnePoint.infty = OnePoint.infty

def continuous_plusMap_iff_proper : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    LCH X → LCH Y → ∀ (f : X → Y), Continuous f →
      (Continuous (OnePoint.map f) ↔ Proper f)

def plusHomeomorphType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] →
    (X ≃ₜ Y) → (OnePoint X ≃ₜ OnePoint Y)

def plusHomeomorphValue : plusHomeomorphType := fun e => e.onePointCongr

def plusHomeomorph_apply : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (z : OnePoint X), e.onePointCongr z = OnePoint.map e z

def homeomorphism_extends : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y],
    LCH X → LCH Y → ∀ (e : X ≃ₜ Y),
      ∃ E : OnePoint X ≃ₜ OnePoint Y,
        (∀ x : X, E (OnePoint.some x) = OnePoint.some (e x)) ∧
        E OnePoint.infty = OnePoint.infty

end Specs.D10Topology.Ch11.ProperInfinity
