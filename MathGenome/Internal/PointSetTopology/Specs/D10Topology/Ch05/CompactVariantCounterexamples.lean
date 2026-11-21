import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.CountableCompactness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import Mathlib.Topology.Constructions.SumProd

/-! Independent statements for paper.tex `d10:05:variant-counterexamples`.
Bool represents {0,1}, with false = 0 and true = 1. Natural-number
subsequence positions start at zero, so positions 1,3,5,... are the
paper's second, fourth, sixth, ... positions. All topologies are explicit.
No separation axiom is assumed for the second example. -/

open Set
open scoped Topology
namespace Specs.D10Topology.Ch05.CompactVariantCounterexamples
open CountableCompactness Compactness
open Ch04.NetsAndSubnets

abbrev BinaryCube := Set ℕ → Bool

@[instance_reducible] def binaryCubeTopology : TopologicalSpace BinaryCube :=
  Ch03.Products.productTopologyValue (fun _ : Set ℕ => (⊥ : TopologicalSpace Bool))

noncomputable def binarySequence (n : ℕ) : BinaryCube := by
  classical
  exact fun A => if n ∈ A then true else false

/-- The coordinate selected after the proposed subsequence is given. -/
def evenPositionSet (φ : ℕ → ℕ) : Set ℕ := range (fun k => φ (2 * k + 1))

abbrev FiberSpace := ℕ × Bool

@[instance_reducible] def fiberTopology : TopologicalSpace FiberSpace :=
  @instTopologicalSpaceProd ℕ Bool ⊥ ⊤

def fiberPair (n : ℕ) : Set FiberSpace := {p | p.1 = n}

def otherInFiber (p : FiberSpace) : FiberSpace := (p.1, !p.2)

-- Expected types and values for the construction bindings.
def binaryCubeType := Type
def binaryCubeValue : binaryCubeType := Set ℕ → Bool

def binaryCubeTopologyType := TopologicalSpace BinaryCube
def binaryCubeTopologyValue : binaryCubeTopologyType := binaryCubeTopology

def binarySequenceType := ℕ → BinaryCube
noncomputable def binarySequenceValue : binarySequenceType := binarySequence

def evenPositionSetType := (ℕ → ℕ) → Set ℕ
def evenPositionSetValue : evenPositionSetType := evenPositionSet

def fiberSpaceType := Type
def fiberSpaceValue : fiberSpaceType := ℕ × Bool

def fiberTopologyType := TopologicalSpace FiberSpace
def fiberTopologyValue : fiberTopologyType := fiberTopology

def fiberPairType := ℕ → Set FiberSpace
def fiberPairValue : fiberPairType := fiberPair

def otherInFiberType := FiberSpace → FiberSpace
def otherInFiberValue : otherInFiberType := otherInFiber

/-- The topology is the product of the discrete coordinate topologies. -/
def binaryCube_topology_eq_pi : Prop :=
  binaryCubeTopology = @Pi.topologicalSpace (Set ℕ) (fun _ => Bool) (fun _ => ⊥)

def binaryCube_compact : Prop := @CoverCompact BinaryCube binaryCubeTopology

def binaryCube_hausdorff : Prop := @T2Space BinaryCube binaryCubeTopology

def binarySequence_coordinate : Prop :=
  ∀ (n : ℕ) (A : Set ℕ), binarySequence n A = true ↔ n ∈ A

def selected_coordinate_alternates : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ k,
    binarySequence (φ (2 * k)) (evenPositionSet φ) = false ∧
    binarySequence (φ (2 * k + 1)) (evenPositionSet φ) = true

/-- Failure at the specific even-position coordinate, for every proposed limit. -/
def selected_coordinate_not_convergent : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ b : Bool,
    ¬ Converges ⊥ (fun k => binarySequence (φ k) (evenPositionSet φ)) b

def binarySequence_no_convergent_subsequence : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ x : BinaryCube,
    ¬ Converges binaryCubeTopology (binarySequence ∘ φ) x

def binaryCube_not_sequentiallyCompact : Prop :=
  ¬ @SequentiallyCompact BinaryCube binaryCubeTopology

/-- Every open set is a union of full pairs; the first coordinate is discrete. -/
def fiber_open_iff : Prop :=
  ∀ U : Set FiberSpace, IsOpen[fiberTopology] U ↔
    ∃ S : Set ℕ, U = Prod.fst ⁻¹' S

/-- Every neighborhood of a point contains its entire two-point fiber. -/
def fiber_neighborhood_contains_pair : Prop :=
  ∀ (p : FiberSpace) (N : Set FiberSpace),
    Ch01.BasesAndNeighborhoods.Neighborhood fiberTopology p N → fiberPair p.1 ⊆ N

/-- In particular the other point is an accumulation point even of a singleton. -/
def otherInFiber_accumulation : Prop :=
  ∀ (A : Set FiberSpace) (p : FiberSpace), p ∈ A →
    otherInFiber p ∈ @derivedSet FiberSpace fiberTopology A

def nonempty_subset_has_accumulation : Prop :=
  ∀ A : Set FiberSpace, A.Nonempty → (@derivedSet FiberSpace fiberTopology A).Nonempty

def fiber_limitPointCompact : Prop := @LimitPointCompact FiberSpace fiberTopology

def fiber_not_t1 : Prop := ¬ @T1Space FiberSpace fiberTopology

/-- This explicitly supplies a countable open cover, not just noncompactness. -/
def fiber_pairs_countable_open_cover : Prop :=
  (range fiberPair).Countable ∧
    (∀ n, IsOpen[fiberTopology] (fiberPair n)) ∧ ⋃ n, fiberPair n = univ

def fiber_pairs_no_finite_subcover : Prop :=
  ∀ s : Finset ℕ, ¬ (univ : Set FiberSpace) ⊆ ⋃ n ∈ s, fiberPair n

def fiber_not_countablyCompact : Prop :=
  ¬ @CountableCoverCompact FiberSpace fiberTopology

end Specs.D10Topology.Ch05.CompactVariantCounterexamples
