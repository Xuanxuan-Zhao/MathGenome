import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Basic.Real.Basic

/-!
Independent statements of the two inequalities in Theorem 2.1 (p205:W05).
The ground type is arbitrary and finite. Natural division by two represents
the floor of half the ground-set cardinality. No positivity or nonemptiness
assumption is imposed.
-/

namespace Specs.P205.Families

universe u

/-- The LYM bound, with the ground-set cardinality explicitly named `n`. -/
def lymBoundType : Prop :=
  ∀ {X : Type u} [Fintype X] (n : ℕ), Fintype.card X = n →
    ∀ (𝒜 : Finset (Finset X)),
      IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)) →
        (∑ A ∈ 𝒜, (Nat.choose n A.card : ℝ)⁻¹) ≤ 1

/-- Sperner's bound, including ground sets of cardinality zero or one. -/
def spernerBoundType : Prop :=
  ∀ {X : Type u} [Fintype X] (n : ℕ), Fintype.card X = n →
    ∀ (𝒜 : Finset (Finset X)),
      IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)) →
        𝒜.card ≤ Nat.choose n (n / 2)

end Specs.P205.Families
