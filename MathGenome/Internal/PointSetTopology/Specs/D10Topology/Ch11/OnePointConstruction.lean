import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Independent statements for paper.tex, d10:11:one-point and the dense
boundary of d10:11:compactification. `OnePoint X` is the tagged union
`Option X`, with `none` the new point and `some` the original points.
No noncompactness or nonemptiness is imposed on the construction. -/

open Set Topology
universe u v
namespace Specs.D10Topology.Ch11.OnePointConstruction
open Specs.D10Topology.Ch11.LocalCompactConventions

def xplusType : Type (u + 1) := Type u → Type u
def xplusValue : xplusType := OnePoint

def inclusionType : Type (u + 1) := {X : Type u} → X → OnePoint X
def inclusionValue : inclusionType := @OnePoint.some

def infinityType : Type (u + 1) := (X : Type u) → OnePoint X
def infinityValue : infinityType := fun _ => OnePoint.infty

def topologyType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] →
  TopologicalSpace (OnePoint X)
def topologyValue : topologyType := fun _ _ => inferInstance

def one_point_opens : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LCH X → ∀ U : Set (OnePoint X),
    IsOpen U ↔ (∃ V : Set X, IsOpen V ∧ U = OnePoint.some '' V) ∨
      ∃ K : Set X, IsCompact K ∧ U = (OnePoint.some '' K)ᶜ

def one_point_compact_hausdorff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LCH X →
    CompactSpace (OnePoint X) ∧ T2Space (OnePoint X)

def one_point_open_embedding : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], IsOpenEmbedding (@OnePoint.some X)

def one_point_induced_topology : Prop :=
  ∀ (X : Type u) [t : TopologicalSpace X],
    TopologicalSpace.induced (@OnePoint.some X) inferInstance = t

/-- No openness or density assumption is added to uniqueness. -/
def one_point_topology_unique : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (t : TopologicalSpace (OnePoint X)),
    @CompactSpace (OnePoint X) t → @T2Space (OnePoint X) t →
    @IsEmbedding X (OnePoint X) _ t OnePoint.some →
    t = @OnePoint.instTopologicalSpace X ‹TopologicalSpace X›

def one_point_dense_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    DenseRange (@OnePoint.some X) ↔ ¬CompactSpace X

def one_point_infinity_isolated_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    IsOpen ({OnePoint.infty} : Set (OnePoint X)) ↔ CompactSpace X

def one_point_empty : Prop :=
  ∀ (X : Type u) [IsEmpty X], ∀ z : OnePoint X, z = OnePoint.infty

/-- An arbitrary embedding onto a one-point complement, rather than an
assumed identification of underlying topologies, expresses the converse. -/
def one_point_converse : Prop :=
  ∀ {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
    [CompactSpace Z] [T2Space Z] (p : Z) (f : X → Z),
    IsEmbedding f → range f = {p}ᶜ →
    LCH X ∧ ∃ e : OnePoint X ≃ₜ Z,
      (∀ x, e (OnePoint.some x) = f x) ∧ e OnePoint.infty = p

def complement_one_point_lch : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
    (p : Z), LCH ({p}ᶜ : Set Z)

/-- This also proves the necessity of LCH, without assuming it in advance. -/
def one_point_compactification_iff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    HausdorffCompactification (@OnePoint.some X) ↔ LCH X ∧ ¬CompactSpace X

end Specs.D10Topology.Ch11.OnePointConstruction
