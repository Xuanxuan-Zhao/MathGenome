import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Interval.Set.Basic

/-!
Independent specification for the definition at `paper.tex:3982–3992`.
The scalar field is real or complex, represented by `RCLike`.
-/

open scoped BigOperators

namespace Specs.D11.Ch12

/-- Type of the absolute-continuity predicate on a subset of the real line. -/
def absolutelyContinuousOnType :=
  ∀ {𝕂 : Type*} [RCLike 𝕂], (ℝ → 𝕂) → Set ℝ → Prop

/-- The uniform disjoint-open-interval condition in the source.

Families are indexed by `Fin n`, including the empty family. Both endpoints
belong to the domain; disjointness concerns the open intervals, so shared
endpoints are permitted. All endpoints are real, so the tested intervals are
bounded. In particular, for the domain `Set.univ` the single `δ` works on the
whole real line, independently of the location of the intervals.
-/
def absolutelyContinuousOnValue : absolutelyContinuousOnType :=
  fun {_} _ F s =>
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (u v : Fin n → ℝ),
        (∀ j, u j < v j) →
        (∀ j, u j ∈ s ∧ v j ∈ s) →
        (Pairwise fun i j => Disjoint (Set.Ioo (u i) (v i))
          (Set.Ioo (u j) (v j))) →
        (∑ j, (v j - u j)) < δ → (∑ j, ‖F (v j) - F (u j)‖) < ε

/-- Type of the compact-interval predicate; the source applies it when `a < b`. -/
def absolutelyContinuousOnIntervalType :=
  ∀ {𝕂 : Type*} [RCLike 𝕂], (ℝ → 𝕂) → ℝ → ℝ → Prop

/-- Compact-interval specialization, retaining both endpoint values of `F`.
In the source `a < b`; the formula also makes sense on degenerate intervals.
-/
def absolutelyContinuousOnIntervalValue : absolutelyContinuousOnIntervalType :=
  fun F a b => absolutelyContinuousOnValue F (Set.Icc a b)

/-- Type of the global absolute-continuity predicate. -/
def absolutelyContinuousType :=
  ∀ {𝕂 : Type*} [RCLike 𝕂], (ℝ → 𝕂) → Prop

/-- Global uniform AC, with one `δ` for all bounded interval families in `ℝ`. -/
def absolutelyContinuousValue : absolutelyContinuousType :=
  fun F => absolutelyContinuousOnValue F Set.univ

end Specs.D11.Ch12
