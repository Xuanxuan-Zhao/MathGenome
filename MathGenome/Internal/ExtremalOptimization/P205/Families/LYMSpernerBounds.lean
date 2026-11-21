import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.LYMSpernerBounds

/-!
The LYM and Sperner inequalities of Theorem 2.1 (p205:W05).
The Mathlib results use the same finite families and inclusion antichains;
substitution of `Fintype.card X = n` supplies the source's size parameter.
-/

namespace P205.Families

universe u

/-- The Lubell–Yamamoto–Meshalkin inequality on any finite ground type. -/
theorem lym_bound {X : Type u} [Fintype X] (n : ℕ)
    (hcard : Fintype.card X = n) (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    (∑ A ∈ 𝒜, (Nat.choose n A.card : ℝ)⁻¹) ≤ 1 := by
  subst n
  exact Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜

/-- Sperner's cardinality bound on any finite ground type. -/
theorem sperner_bound {X : Type u} [Fintype X] (n : ℕ)
    (hcard : Fintype.card X = n) (𝒜 : Finset (Finset X))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X))) :
    𝒜.card ≤ Nat.choose n (n / 2) := by
  subst n
  exact h𝒜.sperner

end P205.Families
