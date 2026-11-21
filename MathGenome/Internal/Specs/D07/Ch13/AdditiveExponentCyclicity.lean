import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.GroupTheory.Exponent

/-!
Independent statements for the final additive-group assertion of
K07.13.multiplicative_cyclic (paper.tex:3920), with the characteristic
identification supplied by K07.13.prime_power_cardinality.

`F` is any finite field of the stated cardinality, so these statements also
apply to an embedded model without choosing a model or a multiplicative
generator. `IsAddCyclic F` concerns its whole additive group, including zero.
The least-positive formulation spells out the meaning of additive exponent;
characteristic p and additive cyclicity are conclusions, not hypotheses.
-/

universe u

namespace Specs.D07.Ch13.AdditiveExponentCyclicity

def CharacteristicOfCardinality : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p n : ℕ),
    p.Prime → 1 ≤ n → Nat.card F = p ^ n → CharP F p

def AdditiveExponent : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p n : ℕ),
    p.Prime → 1 ≤ n → Nat.card F = p ^ n → AddMonoid.exponent F = p

def LeastPositiveAnnihilator : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p n : ℕ),
    p.Prime → 1 ≤ n → Nat.card F = p ^ n →
      0 < p ∧ (∀ x : F, p • x = 0) ∧
        ∀ m : ℕ, 0 < m → (∀ x : F, m • x = 0) → p ≤ m

def AdditiveCyclicIff : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p n : ℕ),
    p.Prime → 1 ≤ n → Nat.card F = p ^ n → (IsAddCyclic F ↔ n = 1)

def PrimeCardinalityCyclic : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p : ℕ),
    p.Prime → Nat.card F = p → IsAddCyclic F

def HigherDegreeNotCyclic : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (p n : ℕ),
    p.Prime → 1 < n → Nat.card F = p ^ n → ¬ IsAddCyclic F

end Specs.D07.Ch13.AdditiveExponentCyclicity
