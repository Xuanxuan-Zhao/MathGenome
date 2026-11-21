import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.FirstCountableSequences
import Mathlib.Topology.Compactness.Lindelof

/-!
Independent statements for paper.tex, d10:08:definitions (lines 1026–1028).
The four conditions use the existing chapter 4 first-countability predicate
and Mathlib's canonical second-countability, separability and Lindelöf classes.
The equivalences below specify their exact neighborhood, basis, density and
open-cover meanings. Countable means at most countable throughout.
No separation or nonemptiness assumptions are imposed.
-/

open Set TopologicalSpace
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch08.CountabilityConventions
open Ch01.BasesAndNeighborhoods

/-- These values specify transparent names for existing objects, not new predicates. -/
def countabilityType := {X : Type u} → TopologicalSpace X → Prop

def firstCountableValue : countabilityType := fun t =>
  Ch04.FirstCountableSequences.FirstCountable t

def secondCountableValue : countabilityType := fun {X} t =>
  @SecondCountableTopology X t

def separableValue : countabilityType := fun {X} t =>
  @SeparableSpace X t

def lindelofValue : countabilityType := fun {X} t =>
  @LindelofSpace X t

def firstCountable_iff_mathlib : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch04.FirstCountableSequences.FirstCountable t ↔ FirstCountableTopology X

def secondCountable_iff_countable_basis : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    SecondCountableTopology X ↔
      ∃ B : Set (Set X), B.Countable ∧ BasisFor t B

def separable_iff_countable_dense : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    SeparableSpace X ↔ ∃ D : Set X, D.Countable ∧ closure D = univ

/-- The same universe suffices to index every family of subsets of X.
The forward direction for any index universe is specified separately below. -/
def lindelof_iff_countable_subcover : Prop :=
  ∀ {X : Type u} [TopologicalSpace X],
    LindelofSpace X ↔
      ∀ {ι : Type u} (U : ι → Set X), (∀ i, IsOpen (U i)) →
        (⋃ i, U i) = univ → ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ

def lindelof_indexed_countable_subcover : Prop :=
  ∀ {X : Type u} [TopologicalSpace X], LindelofSpace X →
    ∀ {ι : Type v} (U : ι → Set X), (∀ i, IsOpen (U i)) →
      (⋃ i, U i) = univ → ∃ J : Set ι, J.Countable ∧ (⋃ i ∈ J, U i) = univ

def countable_localBase_open_refinement : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X) (L : Set (Set X)),
    L.Countable → LocalBase t x L →
      ∃ M : Set (Set X), M.Countable ∧ LocalBase t x M ∧
        (∀ V ∈ M, IsOpen V) ∧ (∀ V ∈ M, ∃ N ∈ L, V ⊆ N)

/-- The countable range is a decreasing open local base refining the given one. -/
def countable_localBase_decreasing_open_refinement : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X) (L : Set (Set X)),
    L.Countable → LocalBase t x L →
      ∃ U : ℕ → Set X, Antitone U ∧ (∀ n, IsOpen (U n)) ∧
        LocalBase t x (range U) ∧ (∀ n, ∃ N ∈ L, U n ⊆ N)

def firstCountable_iff_decreasing_open_localBases : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X],
    Ch04.FirstCountableSequences.FirstCountable t ↔
      ∀ x : X, ∃ U : ℕ → Set X, Antitone U ∧ (∀ n, IsOpen (U n)) ∧
        LocalBase t x (range U)

def empty_countability_properties : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] [IsEmpty X],
    Ch04.FirstCountableSequences.FirstCountable t ∧ SecondCountableTopology X ∧
      SeparableSpace X ∧ LindelofSpace X

end Specs.D10Topology.Ch08.CountabilityConventions
