import Mathlib.Combinatorics.SetFamily.Intersecting
import Mathlib.Data.Finset.Powerset

namespace P205.Families

/-- All k-subsets of the specified finite ground set containing the center. -/
def fullStar {α : Type*} [DecidableEq α] (X : Finset α) (k : ℕ) (c : α) :
    Finset (Finset α) := (X.powersetCard k).filter (c ∈ ·)

end P205.Families

namespace Specs.P205.Families

/-- The ground set is arbitrary, and the positive rank includes k = 1. -/
def bound : Prop :=
  ∀ {α : Type*} [DecidableEq α] (X : Finset α) (k : ℕ) (F : Finset (Finset α)),
    1 ≤ k → 2 * k ≤ X.card → F ⊆ X.powersetCard k →
    (F : Set (Finset α)).Intersecting → F.card ≤ (X.card - 1).choose (k - 1)

def star : Prop :=
  ∀ {α : Type*} [DecidableEq α] (X : Finset α) (k : ℕ) (c : α),
    1 ≤ k → 2 * k ≤ X.card → c ∈ X →
    P205.Families.fullStar X k c ⊆ X.powersetCard k ∧
    (P205.Families.fullStar X k c : Set (Finset α)).Intersecting ∧
    (P205.Families.fullStar X k c).card = (X.card - 1).choose (k - 1)

/-- Exactly one set from each complementary pair is selected. -/
def boundaryEquality : Prop :=
  ∀ {α : Type*} [DecidableEq α] (X : Finset α) (k : ℕ) (F : Finset (Finset α)),
    1 ≤ k → X.card = 2 * k → F ⊆ X.powersetCard k →
    (F : Set (Finset α)).Intersecting →
    (F.card = (X.card - 1).choose (k - 1) ↔
      ∀ A ∈ X.powersetCard k, (A ∈ F ↔ X \ A ∉ F))

end Specs.P205.Families
