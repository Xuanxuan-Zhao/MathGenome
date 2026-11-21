import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.UnionCopies

/-! The numerical stage of matroid union, before any union matroid is constructed.
All extrema use the independently defined maximum assignable subset size. -/
namespace Specs.P205.Matroids
open _root_.P205.Matroids Set
open scoped BigOperators
universe u

/-- Every given independent assignment admits a refinement by deletion only. -/
def AssignmentRefinement : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (parts : Fin k → Set α),
    (∀ i, (F.matroid i).Indep (parts i)) →
    ∃ refined : Fin k → Set α, (∀ i, refined i ⊆ parts i) ∧
      DisjointAssignment F (⋃ i, parts i) (⋃ i, parts i) refined

/-- Duplicated occurrences can be deleted while preserving the assigned set. -/
def AssignableDisjointization : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (S I : Set α), I ⊆ S →
    (AssignableValue F I ↔ ∃ parts : Fin k → Set α, DisjointAssignment F S I parts)

/-- The genuine maximum equals the minimum rank expression, with attainment. -/
def MaximumAssignableMin : Prop :=
  ∀ {α : Type u} {k : ℕ} (F : Family α k) (S : Set α), S ⊆ F.ground →
    (∃ T : Set α, T ⊆ S ∧
      qValue F S = (S \ T).ncard + ∑ i, rankValue (F.matroid i) T) ∧
    (∀ T : Set α, T ⊆ S →
      qValue F S ≤ (S \ T).ncard + ∑ i, rankValue (F.matroid i) T)

/-- The empty family assigns only the empty set; its minimum is attained at S. -/
def MaximumAssignableZero : Prop :=
  ∀ {α : Type u} (F : Family α 0) (S : Set α), S ⊆ F.ground →
    (∀ I : Set α, AssignableValue F I ↔ I = ∅) ∧ qValue F S = 0 ∧
    qValue F S = (S \ S).ncard + ∑ i, rankValue (F.matroid i) S ∧
    (∀ T : Set α, T ⊆ S →
      qValue F S ≤ (S \ T).ncard + ∑ i, rankValue (F.matroid i) T)

end Specs.P205.Matroids
