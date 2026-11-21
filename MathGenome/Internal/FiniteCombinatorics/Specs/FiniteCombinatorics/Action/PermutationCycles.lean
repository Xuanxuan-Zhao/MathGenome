import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
Independent specification of the complete cycle decomposition in paper.tex,
W05 and W31. In particular the orbit construction does not discard fixed points.
All definitions below make sense on an empty finite type.
-/
namespace FiniteCombinatorics.PermutationCyclesSpec

open scoped BigOperators
universe u
variable {X : Type u} [Fintype X]

/-- The complete cyclic orbit, with no nonfixed-point restriction. -/
noncomputable def cyclicOrbit (σ : Equiv.Perm X) (x : X) : Finset X := by
  classical
  exact Finset.univ.filter (σ.SameCycle x)

/-- The finite set of distinct complete cyclic orbits. -/
noncomputable def cycles (σ : Equiv.Perm X) : Finset (Finset X) := by
  classical
  exact Finset.univ.image (cyclicOrbit σ)

def cycleLength (C : Finset X) : ℕ := C.card

/-- Defined for all naturals, and zero at zero. The source's c_k is k ≥ 1. -/
noncomputable def countCyclesOfLength (σ : Equiv.Perm X) (k : ℕ) : ℕ := by
  classical
  exact ((cycles σ).filter (fun C => cycleLength C = k)).card

/-- Sum over the entire possible positive length range. -/
noncomputable def totalCycles (σ : Equiv.Perm X) : ℕ :=
  ∑ k ∈ Finset.Icc 1 (Fintype.card X), countCyclesOfLength σ k

noncomputable def fixedPoints (σ : Equiv.Perm X) : Finset X := by
  classical
  exact Finset.univ.filter (fun x => σ x = x)

-- Expected types and values for the public construction.
def cyclicOrbitType := {X : Type u} → [Fintype X] → Equiv.Perm X → X → Finset X
def cyclesType := {X : Type u} → [Fintype X] → Equiv.Perm X → Finset (Finset X)
def cycleLengthType := {X : Type u} → Finset X → ℕ
def countCyclesOfLengthType := {X : Type u} → [Fintype X] → Equiv.Perm X → ℕ → ℕ
def totalCyclesType := {X : Type u} → [Fintype X] → Equiv.Perm X → ℕ
def fixedPointsType := {X : Type u} → [Fintype X] → Equiv.Perm X → Finset X

-- Every expected theorem is a Prop, with no assumed certificates.
def OrbitMembership : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (x y : X),
  y ∈ cyclicOrbit σ x ↔ σ.SameCycle x y

def OrbitPowers : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (x y : X),
  y ∈ cyclicOrbit σ x ↔ ∃ n : ℕ, (σ ^ n) x = y

def OrbitEquality : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (x y : X),
  cyclicOrbit σ x = cyclicOrbit σ y ↔ σ.SameCycle x y

def CyclesMembership : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (C : Finset X),
  C ∈ cycles σ ↔ ∃ x, cyclicOrbit σ x = C

def Partition : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (x : X),
  ∃! C : Finset X, C ∈ cycles σ ∧ x ∈ C

def PairwiseDisjoint : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X),
  (↑(cycles σ) : Set (Finset X)).PairwiseDisjoint id

def Covers : Prop := by
  classical
  exact ∀ {X : Type u} [Fintype X] (σ : Equiv.Perm X),
    (cycles σ).biUnion id = (Finset.univ : Finset X)

def LengthBounds : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (C : Finset X),
  C ∈ cycles σ → 0 < cycleLength C ∧ cycleLength C ≤ Fintype.card X

def LengthSum : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X),
  ∑ C ∈ cycles σ, cycleLength C = Fintype.card X

def SingletonOrbit : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (x : X),
  cyclicOrbit σ x = {x} ↔ σ x = x

def SingletonCycle : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (x : X),
  {x} ∈ cycles σ ↔ σ x = x

def FixedPointCount : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X),
  countCyclesOfLength σ 1 = (fixedPoints σ).card

def ZeroLengthCount : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X), countCyclesOfLength σ 0 = 0

def OverlargeLengthCount : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X) (k : ℕ),
  Fintype.card X < k → countCyclesOfLength σ k = 0

def TotalCount : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X), totalCycles σ = (cycles σ).card

def WeightedCount : Prop := ∀ {X : Type u} [Fintype X], ∀ (σ : Equiv.Perm X),
  ∑ k ∈ Finset.Icc 1 (Fintype.card X), k * countCyclesOfLength σ k = Fintype.card X

def EmptyCycles : Prop := ∀ {X : Type u} [Fintype X], ∀ [IsEmpty X] (σ : Equiv.Perm X), cycles σ = ∅
def EmptyCount : Prop := ∀ {X : Type u} [Fintype X], ∀ [IsEmpty X] (σ : Equiv.Perm X) (k : ℕ),
  countCyclesOfLength σ k = 0

def EmptyTotal : Prop := ∀ {X : Type u} [Fintype X], ∀ [IsEmpty X] (σ : Equiv.Perm X), totalCycles σ = 0

end FiniteCombinatorics.PermutationCyclesSpec
