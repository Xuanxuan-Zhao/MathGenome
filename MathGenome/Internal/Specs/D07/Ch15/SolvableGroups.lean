import MathGenome.Internal.Specs.D07.Ch15.SolvableClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Nat.Prime.Defs

/-!
Independent specification of K07.15.solvable_groups (paper.tex:4308–4319).
The group and its derived subgroups use their original inherited operations;
`derivedSeries` starts at top and iterates the subgroup commutator. Solvability
is termination at bottom, with no finiteness condition. The series criterion
is restricted to finite groups. A series is ascending, with each member normal
only in the next member, and every actual factor cyclic of prime order.
A zero-length series is permitted, covering the trivial group.
-/

namespace Specs.D07.Ch15.SolvableGroups

universe u

/-- One step of an ascending subnormal series, with its actual quotient factor. -/
def PrimeCyclicStep {G : Type u} [Group G] (H K : Subgroup G) : Prop :=
  H ≤ K ∧ ∃ hNormal : (H.subgroupOf K).Normal,
    letI := hNormal
    IsCyclic (K ⧸ H.subgroupOf K) ∧ (Nat.card (K ⧸ H.subgroupOf K)).Prime

/-- A finite chain from identity to the whole group with prime cyclic factors. -/
def HasPrimeCyclicSeries (G : Type u) [Group G] : Prop :=
  ∃ (n : ℕ) (H : ℕ → Subgroup G),
    H 0 = ⊥ ∧ H n = ⊤ ∧ ∀ i < n, PrimeCyclicStep (H i) (H (i + 1))

def DerivedZero : Prop :=
  ∀ (G : Type u) [Group G], derivedSeries G 0 = ⊤

def DerivedSuccessor : Prop :=
  ∀ (G : Type u) [Group G] (j : ℕ),
    derivedSeries G (j + 1) = ⁅derivedSeries G j, derivedSeries G j⁆

def SolvableIffDerivedTerminates : Prop :=
  ∀ (G : Type u) [Group G],
    Group.IsSolvable G ↔ ∃ r : ℕ, derivedSeries G r = ⊥

def FiniteSolvableIffPrimeCyclicSeries : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Group.IsSolvable G ↔ HasPrimeCyclicSeries G

def AbelianDerivedOne : Prop :=
  ∀ (G : Type u) [Group G], (∀ x y : G, x * y = y * x) →
    derivedSeries G 1 = ⊥

def AbelianSolvable : Prop :=
  ∀ (G : Type u) [Group G], (∀ x y : G, x * y = y * x) → Group.IsSolvable G

def SymmetricFiveNotSolvable : Prop :=
  ¬ Group.IsSolvable (Equiv.Perm (Fin 5))

def SymmetricNotSolvable : Prop :=
  ∀ n : ℕ, 5 ≤ n → ¬ Group.IsSolvable (Equiv.Perm (Fin n))

end Specs.D07.Ch15.SolvableGroups
