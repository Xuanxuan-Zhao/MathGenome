import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetTests
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
Independent specification of paper.tex d10:04:first-countable-sequences,
d10:08:first-countable-sequences and the local-base refinement in
d10:08:definitions. Local bases consist of arbitrary neighborhoods.
There is no separation assumption and no countability condition on the target.
-/

open Set Filter
open scoped Topology
universe u v

namespace Specs.D10Topology.Ch04.FirstCountableSequences
open Ch01.BasesAndNeighborhoods Ch04.NetsAndSubnets

/-- Countable means at most countable; at a point a local base is necessarily nonempty. -/
def FirstCountableAt {X : Type u} (t : TopologicalSpace X) (x : X) : Prop :=
  ∃ L : Set (Set X), L.Countable ∧ LocalBase t x L

/-- The paper's first-countability condition, including the empty space. -/
def FirstCountable {X : Type u} (t : TopologicalSpace X) : Prop :=
  ∀ x : X, FirstCountableAt t x

def firstCountableAtType := {X : Type u} → TopologicalSpace X → X → Prop
def firstCountableAtValue : firstCountableAtType := fun t x =>
  ∃ L : Set (Set _), L.Countable ∧ LocalBase t x L

def firstCountableType := {X : Type u} → TopologicalSpace X → Prop
def firstCountableValue : firstCountableType := fun t => ∀ x, FirstCountableAt t x

def firstCountableAt_iff_countablyGenerated : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X),
    FirstCountableAt t x ↔ (𝓝 x).IsCountablyGenerated

def firstCountable_iff_mathlib : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X], FirstCountable t ↔ FirstCountableTopology X

def countable_localBase_open_refinement : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X) (L : Set (Set X)),
    L.Countable → LocalBase t x L →
    ∃ M : Set (Set X), M.Countable ∧ LocalBase t x M ∧
      (∀ V ∈ M, IsOpen V) ∧ (∀ V ∈ M, ∃ N ∈ L, V ⊆ N)

def countable_localBase_enumeration : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X) (L : Set (Set X)),
    L.Countable → LocalBase t x L → ∃ U : ℕ → Set X, range U = L

/-- The decreasing base is given by actual finite prefix intersections. -/
def decreasing_open_localBase : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X) (U : ℕ → Set X),
    LocalBase t x (range U) → (∀ n, IsOpen (U n)) →
    Antitone (fun n => ⋂ k ≤ n, U k) ∧
      (∀ n, IsOpen (⋂ k ≤ n, U k)) ∧
      LocalBase t x (range (fun n => ⋂ k ≤ n, U k))

def firstCountableAt_decreasing_open_localBase : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (x : X), FirstCountableAt t x →
    ∃ U : ℕ → Set X, Antitone U ∧ (∀ n, IsOpen (U n)) ∧
      LocalBase t x (range U)

/-- A sequence uses the upstream neighborhood definition of net convergence. -/
def sequence_converges_iff_tendsto : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X] (a : ℕ → X) (x : X),
    Converges t a x ↔ Tendsto a atTop (𝓝 x)

def closure_iff_exists_sequence : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X], FirstCountable t →
    ∀ (A : Set X) (x : X),
      x ∈ closure A ↔ ∃ a : ℕ → X, (∀ n, a n ∈ A) ∧ Converges t a x

def closed_iff_sequence_limits : Prop :=
  ∀ {X : Type u} [t : TopologicalSpace X], FirstCountable t →
    ∀ A : Set X, IsClosed A ↔
      ∀ (a : ℕ → X) (x : X), (∀ n, a n ∈ A) → Converges t a x → x ∈ A

/-- Only a countable local base at the tested point is needed. -/
def continuousAt_iff_sequence_limits : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y]
    (f : X → Y) (x : X), FirstCountableAt tX x →
    (ContinuousAt f x ↔
      ∀ a : ℕ → X, Converges tX a x → Converges tY (f ∘ a) (f x))

def continuous_iff_sequence_limits : Prop :=
  ∀ {X : Type u} [tX : TopologicalSpace X] {Y : Type v} [tY : TopologicalSpace Y],
    FirstCountable tX → ∀ f : X → Y,
    Continuous f ↔ ∀ (a : ℕ → X) (x : X),
      Converges tX a x → Converges tY (f ∘ a) (f x)

end Specs.D10Topology.Ch04.FirstCountableSequences
