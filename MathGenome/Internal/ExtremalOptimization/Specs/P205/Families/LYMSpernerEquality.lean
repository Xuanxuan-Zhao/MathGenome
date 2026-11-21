import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.LYMSpernerBounds

/-! Full equality assertions of Theorem 2.1. `univ.powersetCard k` is the
entire layer of rank `k`; `(n + 1) / 2` is the ceiling of `n / 2`.
All ground types are arbitrary finite types, including the empty type. -/
namespace Specs.P205.Families
universe u

noncomputable def lymEqualityType : Prop :=
  ∀ {X : Type u} [Fintype X] (n : ℕ), Fintype.card X = n →
    ∀ (𝒜 : Finset (Finset X)),
      IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)) →
        ((∑ A ∈ 𝒜, (Nat.choose n A.card : ℝ)⁻¹) = 1 ↔
          ∃ k : ℕ, k ≤ n ∧ 𝒜 = (@Finset.univ X _).powersetCard k)

noncomputable def spernerEqualityType : Prop :=
  ∀ {X : Type u} [Fintype X] (n : ℕ), Fintype.card X = n →
    ∀ (𝒜 : Finset (Finset X)),
      IsAntichain (· ⊆ ·) (𝒜 : Set (Finset X)) →
        (𝒜.card = Nat.choose n (n / 2) ↔
          𝒜 = (@Finset.univ X _).powersetCard (n / 2) ∨
          𝒜 = (@Finset.univ X _).powersetCard ((n + 1) / 2))

noncomputable def middleLayersCoincideType : Prop :=
  ∀ {X : Type u} [Fintype X] (n : ℕ), Fintype.card X = n →
    ((@Finset.univ X _).powersetCard (n / 2) =
      (@Finset.univ X _).powersetCard ((n + 1) / 2) ↔ n % 2 = 0)
end Specs.P205.Families
