import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent specification for the definitions and orbit–stabilizer assertions in
paper.tex, Chapter 5 introduction and the proof of p204:W30 (lines 994–1015).
The action is an arbitrary left group action; no faithfulness or nonemptiness
condition is imposed. Burnside's formula is a separate obligation.
-/

namespace Specs.FiniteCombinatorics.Action.OrbitStabilizer

universe u v

/-- Type of the fixed-point set for a single group element. -/
def fixedByType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X], G → Set X

/-- Precisely the points fixed by the specified group element. -/
def fixedByValue : fixedByType.{u, v} :=
  fun _ X _ _ g => {x : X | g • x = x}

/-- Type of the stabilizer subgroup of a point. -/
def stabilizerType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X], X → Subgroup G

/-- The canonical subgroup with membership `g • x = x`. -/
def stabilizerValue : stabilizerType.{u, v} :=
  fun G _ _ _ x => MulAction.stabilizer G x

/-- Type of the orbit of a point. -/
def orbitType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X], X → Set X

/-- The image of the orbit map `g ↦ g • x`. -/
def orbitValue : orbitType.{u, v} :=
  fun G _ _ _ x => Set.range (fun g : G => g • x)

/-- Orbits contain their base points, cover the set, and are equal or disjoint.
Thus the family of distinct orbits is a partition, including when `X` is empty. -/
def orbitsPartitionType : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X],
    (∀ x : X, x ∈ MulAction.orbit G x) ∧
    (⋃ x : X, MulAction.orbit G x) = Set.univ ∧
    ∀ x y : X, MulAction.orbit G x = MulAction.orbit G y ∨
      Disjoint (MulAction.orbit G x) (MulAction.orbit G y)

/-- Natural cardinalities of the orbit and stabilizer multiply to the group order.
`Finite` asks only for finiteness, without choosing enumerations. -/
def orbitStabilizerType : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] [Finite X]
    (x : X),
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G

end Specs.FiniteCombinatorics.Action.OrbitStabilizer
