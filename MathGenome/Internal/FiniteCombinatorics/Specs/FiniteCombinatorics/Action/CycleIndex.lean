import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.PermutationCycles
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.MvPolynomial.Basic

/-! Independent specification of paper.tex W31. Variable `i : Fin |X|`
represents the source variable s_(i+1), so the polynomial ring has exactly |X|
variables. Complete cycles use the same canonical construction as W05.
No faithfulness or nonemptiness assumption is imposed. -/
namespace FiniteCombinatorics.CycleIndexSpec

open scoped BigOperators
universe u v

variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

def actionPermutation : G →* Equiv.Perm X := MulAction.toPermHom G X

def actionImage : Subgroup (Equiv.Perm X) := (actionPermutation G X).range

variable [Fintype X]

noncomputable def cyclicOrbit (g : G) (x : X) : Finset X :=
  PermutationCyclesSpec.cyclicOrbit (actionPermutation G X g) x
noncomputable def cycles (g : G) : Finset (Finset X) :=
  PermutationCyclesSpec.cycles (actionPermutation G X g)
noncomputable def countCycles (g : G) (k : ℕ) : ℕ :=
  PermutationCyclesSpec.countCyclesOfLength (actionPermutation G X g) k

/-- The universal monomial of a finite permutation, with s_(i+1) indexed by i. -/
noncomputable def permutationMonomial (σ : Equiv.Perm X) :
    MvPolynomial (Fin (Fintype.card X)) ℚ :=
  ∏ i : Fin (Fintype.card X),
    MvPolynomial.X i ^ PermutationCyclesSpec.countCyclesOfLength σ (i.val + 1)

noncomputable def elementMonomial (g : G) : MvPolynomial (Fin (Fintype.card X)) ℚ :=
  permutationMonomial X (actionPermutation G X g)

noncomputable def cycleIndex [Fintype G] : MvPolynomial (Fin (Fintype.card X)) ℚ :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, elementMonomial G X g

/-- The average over the subgroup of permutations that occur in the action. -/
noncomputable def imageCycleIndex [Fintype G] : MvPolynomial (Fin (Fintype.card X)) ℚ := by
  classical
  exact (Fintype.card (actionImage G X) : ℚ)⁻¹ •
    ∑ σ : actionImage G X, permutationMonomial X σ.val

-- Expected types and values of the public definitions.
def actionPermutationType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X], G →* Equiv.Perm X
def actionImageType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X], Subgroup (Equiv.Perm X)
def cyclicOrbitType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X], G → X → Finset X
def cyclesType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X], G → Finset (Finset X)
def countCyclesType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X], G → ℕ → ℕ
def permutationMonomialType :=
  ∀ (X : Type v) [Fintype X], Equiv.Perm X → MvPolynomial (Fin (Fintype.card X)) ℚ
def elementMonomialType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X],
    G → MvPolynomial (Fin (Fintype.card X)) ℚ
def cycleIndexType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [Fintype G],
    MvPolynomial (Fin (Fintype.card X)) ℚ
def imageCycleIndexType :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [Fintype G],
    MvPolynomial (Fin (Fintype.card X)) ℚ

-- Expected theorem types, not assumed certificates.
def ActionPermutationApply : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] (g : G) (x : X),
    actionPermutation G X g x = g • x

def OrbitPowers : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G) (x y : X),
    y ∈ cyclicOrbit G X g x ↔ ∃ n : ℕ, (g ^ n) • x = y

def CyclesMembership : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X]
    (g : G) (C : Finset X), C ∈ cycles G X g ↔ ∃ x, cyclicOrbit G X g x = C

def Partition : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G) (x : X),
    ∃! C : Finset X, C ∈ cycles G X g ∧ x ∈ C

def PairwiseDisjoint : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G),
    (↑(cycles G X g) : Set (Finset X)).PairwiseDisjoint id

def Covers : Prop := by
  classical
  exact ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G),
    (cycles G X g).biUnion id = Finset.univ

def LengthBounds : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X]
    (g : G) (C : Finset X), C ∈ cycles G X g → 0 < C.card ∧ C.card ≤ Fintype.card X

def LengthSum : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G),
    ∑ C ∈ cycles G X g, C.card = Fintype.card X

def WeightedCount : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G),
    ∑ k ∈ Finset.Icc 1 (Fintype.card X), k * countCycles G X g k = Fintype.card X

def SingletonCycle : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G) (x : X),
    {x} ∈ cycles G X g ↔ g • x = x

def FixedPointCount : Prop := by
  classical
  exact ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G),
    countCycles G X g 1 = (Finset.univ.filter (fun x : X => g • x = x)).card

def ZeroCount : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G),
    countCycles G X g 0 = 0

def OverlargeCount : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] (g : G) (k : ℕ),
    Fintype.card X < k → countCycles G X g k = 0

def ImageAverage : Prop := by
  classical
  exact ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [Fintype G],
    cycleIndex G X = imageCycleIndex G X

def EmptyCycles : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [IsEmpty X] (g : G),
    cycles G X g = ∅

def EmptyCount : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [IsEmpty X]
    (g : G) (k : ℕ), countCycles G X g k = 0

def EmptyMonomial : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [IsEmpty X] (g : G),
    elementMonomial G X g = 1

def EmptyIndex : Prop :=
  ∀ (G : Type u) (X : Type v) [Group G] [MulAction G X] [Fintype X] [Fintype G] [IsEmpty X],
    cycleIndex G X = 1

end FiniteCombinatorics.CycleIndexSpec
