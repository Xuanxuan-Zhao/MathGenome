import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions
import Mathlib.Topology.Compactness.SigmaCompact

/-!
Independent definitions for paper.tex, d10:11:local-compactness,
d10:11:proper, d10:11:compactification, and the countable compact cover
in d10:11:exhaustion. Compactness uses the canonical `IsCompact`, whose
open-cover and subspace meanings are established by the upstream goal.
No separation axiom is implicit in local compactness or properness.
The definitions here are shared data, not assumed theorem certificates.
-/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch11.LocalCompactConventions

/-- One compact neighborhood at each point; the compact set need not be open. -/
def LocallyCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ K : Set X, IsCompact K ∧
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ K

/-- Hausdorffness is an additional, explicit condition. -/
def LCH (X : Type u) [TopologicalSpace X] : Prop :=
  LocallyCompact X ∧ T2Space X

/-- Source properness includes continuity and compact preimages of compact sets. -/
def Proper {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  Continuous f ∧ ∀ K : Set Y, IsCompact K → IsCompact (f ⁻¹' K)

/-- Perfect maps are continuous and closed, with compact fibers, without surjectivity. -/
def Perfect {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  Continuous f ∧ IsClosedMap f ∧ ∀ y : Y, IsCompact (f ⁻¹' {y})

/-- A compact Hausdorff target with a dense embedding; no proper-image condition. -/
def HausdorffCompactification {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K] (i : X → K) : Prop :=
  IsEmbedding i ∧ DenseRange i ∧ CompactSpace K ∧ T2Space K

/-- Countable includes finite and empty covering families. -/
def SigmaCompact (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ C : Set (Set X), C.Countable ∧ (∀ K ∈ C, IsCompact K) ∧ ⋃₀ C = univ

def spacePropertyType : Type (u + 1) := (X : Type u) → [TopologicalSpace X] → Prop
def locallyCompactValue : spacePropertyType := LocallyCompact
def lchValue : spacePropertyType := LCH
def sigmaCompactValue : spacePropertyType := SigmaCompact

def mapPropertyType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [TopologicalSpace X] → [TopologicalSpace Y] →
    (X → Y) → Prop
def properValue : mapPropertyType := @Proper
def perfectValue : mapPropertyType := @Perfect
def hausdorffCompactificationValue : mapPropertyType := @HausdorffCompactification

def locallyCompact_iff_compact_neighborhood : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LocallyCompact X ↔
    ∀ x : X, ∃ K : Set X, IsCompact K ∧ K ∈ 𝓝 x

def locallyCompact_iff_weaklyLocallyCompactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    LocallyCompact X ↔ WeaklyLocallyCompactSpace X

def lch_iff_weaklyLocallyCompactSpace_and_t2 : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    LCH X ↔ WeaklyLocallyCompactSpace X ∧ T2Space X

/-- This implication requires no separation; its converse is not asserted here. -/
def locallyCompact_of_mathlib_locallyCompactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], LocallyCompactSpace X → LocallyCompact X

/-- Spell out embedding and density using their source meanings. -/
def hausdorffCompactification_iff_source : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K] (i : X → K),
    HausdorffCompactification i ↔
      (∃ h : X ≃ₜ range i, ∀ x, (h x : K) = i x) ∧
      closure (range i) = univ ∧
      Specs.D10Topology.Ch05.Compactness.CoverCompact K ∧ T2Space K

def sigmaCompact_iff_sequence : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], SigmaCompact X ↔
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ

def sigmaCompact_iff_sigmaCompactSpace : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], SigmaCompact X ↔ SigmaCompactSpace X

def empty_locallyCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], LocallyCompact X

def empty_lch : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], LCH X

def empty_sigmaCompact : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X], SigmaCompact X

/-- A compact Hausdorff space may be its own compactification, even when empty. -/
def identity_hausdorffCompactification : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X],
    HausdorffCompactification (id : X → X)

def empty_identity_hausdorffCompactification : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [IsEmpty X],
    HausdorffCompactification (id : X → X)

end Specs.D10Topology.Ch11.LocalCompactConventions
