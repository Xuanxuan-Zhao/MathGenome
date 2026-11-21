import Mathlib.Topology.Order

/-!
Independent interface for paper.tex, foundations F1–F4 and
`d10:01:topology`, `d10:01:generated`.

The canonical topology is Mathlib's `TopologicalSpace`. Families below are
families of subsets of the actual underlying type, including an empty type.
No separation axiom or nonemptiness assumption is imposed.
-/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

/-- The open family of the specified canonical topology. -/
def openSets {X : Type u} (t : TopologicalSpace X) : Set (Set X) :=
  {U | IsOpen[t] U}

/-- Closed means open complement in the same topology. -/
def closedSets {X : Type u} (t : TopologicalSpace X) : Set (Set X) :=
  {F | IsClosed[t] F}

/-- The paper's open-family axioms, including empty operations. -/
structure OpenFamilyAxioms {X : Type u} (O : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ O
  univ_mem : univ ∈ O
  sUnion_mem : ∀ A : Set (Set X), A ⊆ O → ⋃₀ A ∈ O
  finite_sInter_mem : ∀ A : Set (Set X), A.Finite → A ⊆ O → ⋂₀ A ∈ O

/-- The dual axioms, with arbitrary intersections and finite unions. -/
structure ClosedFamilyAxioms {X : Type u} (C : Set (Set X)) : Prop where
  empty_mem : ∅ ∈ C
  univ_mem : univ ∈ C
  sInter_mem : ∀ A : Set (Set X), A ⊆ C → ⋂₀ A ∈ C
  finite_sUnion_mem : ∀ A : Set (Set X), A.Finite → A ⊆ C → ⋃₀ A ∈ C

end D10Topology.Ch01

namespace Specs.D10Topology.Ch01.TopologicalFoundations
open _root_.D10Topology.Ch01

-- Definitions are specified by both type and value.
def topologyType : Type (u + 1) := (X : Type u) → Type u
def topologyValue : topologyType := fun X => TopologicalSpace X

def discreteType : Type (u + 1) := (X : Type u) → TopologicalSpace X
def discreteValue : discreteType := fun _ => ⊥
def indiscreteValue : discreteType := fun _ => ⊤

def finerType : Type (u + 1) :=
  {X : Type u} → TopologicalSpace X → TopologicalSpace X → Prop
def finerValue : finerType := fun σ τ => openSets τ ⊆ openSets σ

def generatedType : Type (u + 1) :=
  {X : Type u} → Set (Set X) → TopologicalSpace X
def generatedValue : generatedType := fun A => TopologicalSpace.generateFrom A

def intersectionType : Type (u + 1) :=
  {X : Type u} → Set (TopologicalSpace X) → TopologicalSpace X
def intersectionValue : intersectionType := fun T => sSup T

def open_axioms : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X), OpenFamilyAxioms (openSets t)

def open_characterization : Prop :=
  ∀ {X : Type u} (O : Set (Set X)),
    OpenFamilyAxioms O ↔ ∃! t : TopologicalSpace X, openSets t = O

def closed_iff_open_complement : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X) (F : Set X),
    F ∈ closedSets t ↔ Fᶜ ∈ openSets t

def discrete_opens : Prop :=
  ∀ (X : Type u), openSets (discreteValue X) = univ

def indiscrete_opens : Prop :=
  ∀ (X : Type u), openSets (indiscreteValue X) = {∅, univ}

def finer_iff_le : Prop :=
  ∀ {X : Type u} (σ τ : TopologicalSpace X), finerValue σ τ ↔ σ ≤ τ

def closed_axioms : Prop :=
  ∀ {X : Type u} (t : TopologicalSpace X), ClosedFamilyAxioms (closedSets t)

def closed_characterization : Prop :=
  ∀ {X : Type u} (C : Set (Set X)),
    ClosedFamilyAxioms C ↔ ∃! t : TopologicalSpace X, closedSets t = C

def generated_smallest : Prop :=
  ∀ {X : Type u} (A : Set (Set X)),
    A ⊆ openSets (generatedValue A) ∧
      ∀ t : TopologicalSpace X, A ⊆ openSets t →
        openSets (generatedValue A) ⊆ openSets t

def intersection_opens : Prop :=
  ∀ {X : Type u} (T : Set (TopologicalSpace X)),
    openSets (intersectionValue T) = ⋂ t ∈ T, openSets t

def intersection_family_axioms : Prop :=
  ∀ {X : Type u} (T : Set (TopologicalSpace X)),
    OpenFamilyAxioms (⋂ t ∈ T, openSets t)

/-- `Fin 3` represents a,b,c by 0,1,2. The specified union contains
both singleton summands but omits their union and fails the topology axioms. -/
def union_counterexample : Prop :=
  ∃ τ₁ τ₂ : TopologicalSpace (Fin 3),
    openSets τ₁ = {∅, {(0 : Fin 3)}, univ} ∧
    openSets τ₂ = {∅, {(1 : Fin 3)}, univ} ∧
    {(0 : Fin 3)} ∈ openSets τ₁ ∪ openSets τ₂ ∧
    {(1 : Fin 3)} ∈ openSets τ₁ ∪ openSets τ₂ ∧
    ({(0 : Fin 3)} ∪ {(1 : Fin 3)}) ∉ openSets τ₁ ∪ openSets τ₂ ∧
    ¬ OpenFamilyAxioms (openSets τ₁ ∪ openSets τ₂)

end Specs.D10Topology.Ch01.TopologicalFoundations
