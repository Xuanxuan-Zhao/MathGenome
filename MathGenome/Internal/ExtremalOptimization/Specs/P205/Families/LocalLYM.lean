import Mathlib.Combinatorics.SetFamily.Shadow
import Mathlib.Basic.Real.Basic

/-!
Independent statements for Proposition p205:W06 and its shadow convention.
The finite ground set is represented by an arbitrary finite type `α`; a finite
set `X` in an ambient type is represented by its subtype. Thus `Fintype.card α`
is the source's `n`. Families are finite collections of finite subsets of `α`.
The canonical library definitions `Finset.shadow` (one-point deletions) and
`Finset.upShadow` (one-point extensions within `α`) are used throughout.
-/

namespace Specs.P205.Families

universe u

/-- The lower local LYM inequality, with real normalized layer densities. -/
def LowerLocalLYM : Prop :=
  ∀ (α : Type u) [DecidableEq α] [Fintype α]
    (k : ℕ) (A : Finset (Finset α)),
    1 ≤ k → k ≤ Fintype.card α →
    (∀ s ∈ A, s.card = k) →
    (A.card : ℝ) / (Fintype.card α).choose k ≤
      ((Finset.shadow A).card : ℝ) / (Fintype.card α).choose (k - 1)

/-- The upper local LYM inequality includes rank zero and empty families. -/
def UpperLocalLYM : Prop :=
  ∀ (α : Type u) [DecidableEq α] [Fintype α]
    (k : ℕ) (A : Finset (Finset α)),
    k < Fintype.card α →
    (∀ s ∈ A, s.card = k) →
    (A.card : ℝ) / (Fintype.card α).choose k ≤
      ((Finset.upShadow A).card : ℝ) / (Fintype.card α).choose (k + 1)

/-- A family whose members all have rank zero has empty lower shadow. -/
def RankZeroShadow : Prop :=
  ∀ (α : Type u) [DecidableEq α] (A : Finset (Finset α)),
    (∀ s ∈ A, s.card = 0) → Finset.shadow A = ∅

/-- On a uniform family, the upper shadow is exactly the next-rank supersets. -/
def UpperShadowMembership : Prop :=
  ∀ (α : Type u) [DecidableEq α] [Fintype α]
    (k : ℕ) (A : Finset (Finset α)),
    (∀ s ∈ A, s.card = k) → ∀ t : Finset α,
    t ∈ Finset.upShadow A ↔ t.card = k + 1 ∧ ∃ s ∈ A, s ⊆ t

end Specs.P205.Families
