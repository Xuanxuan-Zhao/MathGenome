import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ColexInitialShadow

/-! Independent statement of paper.tex, Theorem 2.7 (p205:W09).
The finite ground set is its finite linearly ordered point type, as in the
upstream Specs; a specified finite subset is represented by its subtype.
The library shadow deletes one point, so its zeroth iterate is the identity
and the shadow of a rank-zero family is empty. -/

namespace P205.Families.Spec

/-- Every iterated lower shadow is minimized by the equally sized colex
initial segment, on any finite linearly ordered ground set. -/
def KruskalKatona : Prop :=
  ∀ (α : Type*) [LinearOrder α] [Fintype α] (k m : ℕ)
    (𝒜 : Finset (Finset α)),
    1 ≤ k → k ≤ Fintype.card α →
    (∀ A ∈ 𝒜, A.card = k) → 𝒜.card = m →
    ∀ j : ℕ, j ≤ k →
      ((Finset.shadow^[j]) (initialColex α k m)).card ≤
        ((Finset.shadow^[j]) 𝒜).card

end P205.Families.Spec
