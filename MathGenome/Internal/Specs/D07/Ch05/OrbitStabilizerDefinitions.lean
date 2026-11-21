import MathGenome.Internal.Specs.D07.Ch01.SubgroupDefinitionTest
import MathGenome.Internal.Specs.D07.Ch05.ActionDefinition
import Mathlib.GroupTheory.GroupAction.Defs

/-!
Independent specification of `K07.05.orbit_stabilizer_definitions`
(paper.tex:830–840). The group and the acted-on type are arbitrary;
in particular the type may be empty, and no finiteness is assumed.
The canonical Mathlib orbit, stabilizer, and orbit setoid are used.
-/

namespace Specs.D07.Ch05.OrbitStabilizerDefinitions

universe u v

/-- The source orbit is a subset of the acted-on type. -/
def OrbitType : Type (max (u + 1) (v + 1)) :=
  (G : Type u) → (X : Type v) → [Group G] → [MulAction G X] → X → Set X

def orbitValue : OrbitType.{u, v} :=
  fun G _ _ _ x => Set.range (fun g : G => g • x)

/-- A stabilizer is a subgroup with the ambient group operations. -/
def StabilizerType : Type (max (u + 1) (v + 1)) :=
  (G : Type u) → (X : Type v) → [Group G] → [MulAction G X] → X → Subgroup G

def stabilizerValue : StabilizerType.{u, v} :=
  fun G _ _ _ x => MulAction.stabilizer G x

/-- Membership gives exactly the displayed set of action values. -/
def OrbitDescription : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X),
    orbitValue G X x = {y : X | ∃ g : G, g • x = y}

/-- The bundled stabilizer has exactly the source's fixed-point carrier. -/
def StabilizerDescription : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X),
    (stabilizerValue G X x : Set G) = {g : G | g • x = x}

/-- Explicit subgroup assertion for the set defined in the source. -/
def StabilizerIsSubgroup : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X),
    ∃ H : Subgroup G, (H : Set G) = {g : G | g • x = x}

/-- Belonging to the same orbit is an equivalence relation. -/
def OrbitRelationEquivalence : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    Equivalence (fun x y : X => y ∈ orbitValue G X x)

/-- The canonical orbit relation has the source orbits as its classes. -/
def OrbitClasses : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X),
    {y : X | MulAction.orbitRel G X x y} = orbitValue G X x

/-- Orbits are nonempty, cover X, and any two are equal or disjoint.
This also describes the empty partition when X is empty. -/
def OrbitsPartition : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    (∀ x : X, (orbitValue G X x).Nonempty) ∧
    (⋃ x : X, orbitValue G X x) = Set.univ ∧
    (∀ x y : X, orbitValue G X x = orbitValue G X y ∨
      Disjoint (orbitValue G X x) (orbitValue G X y))

/-- Set equality spells out g Stab(x) g⁻¹ with its exact multiplication order. -/
def StabilizerConjugation : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (g : G) (x : X),
    (stabilizerValue G X (g • x) : Set G) =
      (fun h : G => g * h * g⁻¹) '' (stabilizerValue G X x : Set G)

end Specs.D07.Ch05.OrbitStabilizerDefinitions
