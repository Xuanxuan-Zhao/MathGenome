import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Sylow

/-!
Independent specification of K07.07.primary_subgroups, paper.tex:3391–3410.
The canonical additive subgroups have the stated annihilation carriers.
Only the Sylow assertion assumes finiteness. `Multiplicative` changes
notation so that Mathlib's Sylow structure applies to the same group.
-/
namespace Specs.D07.Ch07.PrimarySubgroups

universe u

abbrev TorsionSubgroupType := (A : Type u) → [AddCommGroup A] → AddSubgroup A
abbrev PrimarySubgroupType := (A : Type u) → [AddCommGroup A] → ℕ → AddSubgroup A

def torsionSubgroupValue : TorsionSubgroupType.{u} := AddCommGroup.torsion

def primarySubgroupValue : PrimarySubgroupType.{u} := AddCommGroup.primaryComponent

/-- The source uses a strictly positive integer annihilator. -/
def MemTorsion : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (a : A),
    a ∈ torsionSubgroupValue A ↔ ∃ n : ℤ, 0 < n ∧ n • a = 0

def TorsionCharacteristic : Prop :=
  ∀ (A : Type u) [AddCommGroup A], (torsionSubgroupValue A).Characteristic

/-- The exponent may be zero, so the identity is included. -/
def MemPrimary : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (p : ℕ) (hp : p.Prime) (a : A),
    a ∈ primarySubgroupValue A p ↔ ∃ k : ℕ, (p ^ k) • a = 0

def PrimaryCharacteristic : Prop :=
  ∀ (A : Type u) [AddCommGroup A] (p : ℕ), p.Prime →
    (primarySubgroupValue A p).Characteristic

/-- Existence as a Sylow subgroup and equality with every Sylow subgroup,
for every prime, including primes not dividing the group order. -/
def PrimaryUniqueSylow : Prop :=
  ∀ (A : Type u) [AddCommGroup A] [Finite A] (p : ℕ), p.Prime →
    ∃ S : Sylow p (Multiplicative A),
      S.toSubgroup = (primarySubgroupValue A p).toSubgroup ∧
      ∀ Q : Sylow p (Multiplicative A), Q = S

end Specs.D07.Ch07.PrimarySubgroups
