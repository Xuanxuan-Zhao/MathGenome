import MathGenome.Internal.Specs.D07.Ch03.Lagrange
import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerDefinitions
import MathGenome.Internal.Specs.D07.Ch05.OrbitStabilizerEquivalence
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent specification of `K07.05.orbit_stabilizer_counting`
(paper.tex:849–860). For a finite group, individual orbits are finite and
their cardinalities satisfy the index and product formulas. The acted-on
type need not be finite or nonempty. The final sum assumes only that the
acted-on type is finite; its index type is the set of distinct orbits,
not the set of points, so every orbit occurs exactly once.
-/

namespace Specs.D07.Ch05.OrbitStabilizerCounting

universe u v

open Specs.D07.Ch05.OrbitStabilizerDefinitions

/-- An orbit is finite when the acting group is finite. -/
def FiniteOrbit : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] (x : X),
    (orbitValue G X x).Finite

/-- The index counts left cosets of the stabilizer, without requiring normality. -/
def OrbitCardEqIndex : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] (x : X),
    Nat.card ↥(orbitValue G X x) = (stabilizerValue G X x).index

/-- The finite orbit size times the stabilizer order equals the group order. -/
def OrbitCardMulStabilizerCard : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite G] (x : X),
    Nat.card ↥(orbitValue G X x) * Nat.card (stabilizerValue G X x) = Nat.card G

/-- Finite additivity for the orbit partition. No finiteness of G is required.
For empty X, both the sum and its index type are empty. -/
def CardEqSumOrbitCards : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Finite X],
    letI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
    Nat.card X = ∑ q : MulAction.orbitRel.Quotient G X, Nat.card ↥q.orbit

end Specs.D07.Ch05.OrbitStabilizerCounting
