import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.BasesAndNeighborhoods
import Mathlib.Topology.Separation.Regular

/-! Independent specification of paper.tex, d10:12:uniform-topology.
The topology is constructed from the paper's section criterion. Neither
nonemptiness nor any separation axiom is assumed. The neighborhood and local
base predicates are the canonical Chapter 1 open-witness formulations.
-/

open Set Filter
open scoped Uniformity Topology
universe u

namespace Specs.D10Topology.Ch12.UniformTopology

open UniformConventions

/-- The topology whose open sets satisfy the entourage-section condition.
The structure fields prove the topology axioms directly from filter operations. -/
@[instance_reducible]
def uniformTopology {X : Type u} [UniformSpace X] : TopologicalSpace X where
  IsOpen O := ∀ x ∈ O, ∃ U ∈ 𝓤 X, entourageBall U x ⊆ O
  isOpen_univ := by
    intro x _
    exact ⟨univ, univ_mem, subset_univ _⟩
  isOpen_inter := by
    intro O P hO hP x hx
    obtain ⟨U, hU, hUO⟩ := hO x hx.1
    obtain ⟨V, hV, hVP⟩ := hP x hx.2
    exact ⟨U ∩ V, inter_mem hU hV, fun _ hy => ⟨hUO hy.1, hVP hy.2⟩⟩
  isOpen_sUnion := by
    intro S hS x hx
    obtain ⟨O, hOS, hxO⟩ := hx
    obtain ⟨U, hU, hUO⟩ := hS O hOS x hxO
    exact ⟨U, hU, hUO.trans (subset_sUnion_of_mem hOS)⟩

def uniformTopologyType := {X : Type u} → [UniformSpace X] → TopologicalSpace X
def uniformTopologyValue : uniformTopologyType := @uniformTopology

def uniformTopology_isOpen : Prop :=
  ∀ {X : Type u} [UniformSpace X] (O : Set X),
    IsOpen[uniformTopology] O ↔
      ∀ x ∈ O, ∃ U ∈ 𝓤 X, entourageBall U x ⊆ O

def uniformTopology_eq_canonical : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X], uniformTopology = uX.toTopologicalSpace

/-- Explicit neighborhoods for the topology just constructed, not a second
unrelated topology supplied as a hidden instance. -/
def uniformTopology_neighborhood_iff : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x : X) (N : Set X),
    Ch01.BasesAndNeighborhoods.Neighborhood uniformTopology x N ↔
      ∃ U ∈ 𝓤 X, entourageBall U x ⊆ N

def uniformTopology_localBase : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x : X),
    Ch01.BasesAndNeighborhoods.LocalBase uniformTopology x
      {N : Set X | ∃ U ∈ 𝓤 X, entourageBall U x = N}

def uniformTopology_nhds : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x : X),
    @nhds X uniformTopology x = (𝓤 X).comap (Prod.mk x)

def uniformTopology_hausdorff_iff_separated : Prop :=
  ∀ {X : Type u} [UniformSpace X],
    @T2Space X uniformTopology ↔ Separated (X := X)

/-- RegularSpace does not contain T1Space in its definition. -/
def uniformTopology_regular : Prop :=
  ∀ {X : Type u} [UniformSpace X], @RegularSpace X uniformTopology

def uniformTopology_shrinking : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x : X) (O : Set X),
    IsOpen[uniformTopology] O → x ∈ O →
      ∃ V : Set X, IsOpen[uniformTopology] V ∧ x ∈ V ∧
        V ⊆ @closure X uniformTopology V ∧ @closure X uniformTopology V ⊆ O

/-- In particular the construction is valid for the unique degenerate empty
uniformity: all subsets of an empty underlying type are open. -/
def uniformTopology_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X] (O : Set X),
    IsOpen[uniformTopology] O

end Specs.D10Topology.Ch12.UniformTopology
