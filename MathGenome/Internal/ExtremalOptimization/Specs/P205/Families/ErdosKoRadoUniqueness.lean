import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.ErdosKoRadoBound

namespace Specs.P205.Families

/-- In the strict EKR range, equality holds exactly for full stars on the
specified arbitrary finite ground set. The center belongs to that ground set. -/
def uniqueness : Prop :=
  ∀ {α : Type*} [DecidableEq α] (X : Finset α) (k : ℕ) (F : Finset (Finset α)),
    1 ≤ k → 2 * k < X.card → F ⊆ X.powersetCard k →
    (F : Set (Finset α)).Intersecting →
    (F.card = (X.card - 1).choose (k - 1) ↔
      ∃ c ∈ X, F = P205.Families.fullStar X k c)

end Specs.P205.Families
