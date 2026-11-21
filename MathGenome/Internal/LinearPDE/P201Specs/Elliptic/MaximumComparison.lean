import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.StrongMaximum

/-! Independent statements for the full classical comparison theorem
(`paper.tex`, Theorem `pde:elliptic-max`). Coefficients are continuous only
inside the domain. `IsPreconnected` includes the empty open set; on that
set both real suprema below are the same empty supremum. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace P201Specs.Elliptic

/-- The weak maximum bound for c ≤ 0, with the actual real suprema of
values on the domain and its topological boundary. -/
def weakMaximumStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n),
  Bornology.IsBounded (Ω : Set (Space n)) → IsPreconnected (Ω : Set (Space n)) →
  ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ),
  EllipticCoefficients Ω a b c →
  (∀ x ∈ (Ω : Set (Space n)), c x ≤ 0) →
  ContDiffOn ℝ 2 u (Ω : Set (Space n)) →
  ContinuousOn u (closure (Ω : Set (Space n))) →
  (∀ x ∈ (Ω : Set (Space n)), 0 ≤ nondivergenceOperator a b c u x) →
  sSup (u '' (Ω : Set (Space n))) ≤
    max 0 (sSup (u '' frontier (Ω : Set (Space n))))

/-- When c = 0 the boundary supremum needs no truncation at zero. -/
def weakMaximumZeroOrderFreeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n),
  Bornology.IsBounded (Ω : Set (Space n)) → IsPreconnected (Ω : Set (Space n)) →
  ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u : Space n → ℝ),
  EllipticCoefficients Ω a b c →
  (∀ x ∈ (Ω : Set (Space n)), c x = 0) →
  ContDiffOn ℝ 2 u (Ω : Set (Space n)) →
  ContinuousOn u (closure (Ω : Set (Space n))) →
  (∀ x ∈ (Ω : Set (Space n)), 0 ≤ nondivergenceOperator a b c u x) →
  sSup (u '' (Ω : Set (Space n))) ≤
    sSup (u '' frontier (Ω : Set (Space n)))

/-- Classical comparison for the same operator and regularity class. -/
def comparisonStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (Ω : Domain n),
  Bornology.IsBounded (Ω : Set (Space n)) → IsPreconnected (Ω : Set (Space n)) →
  ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
    (b : Space n → Space n) (c u v : Space n → ℝ),
  EllipticCoefficients Ω a b c →
  (∀ x ∈ (Ω : Set (Space n)), c x ≤ 0) →
  ContDiffOn ℝ 2 u (Ω : Set (Space n)) →
  ContinuousOn u (closure (Ω : Set (Space n))) →
  ContDiffOn ℝ 2 v (Ω : Set (Space n)) →
  ContinuousOn v (closure (Ω : Set (Space n))) →
  (∀ x ∈ (Ω : Set (Space n)),
    nondivergenceOperator a b c v x ≤ nondivergenceOperator a b c u x) →
  (∀ x ∈ frontier (Ω : Set (Space n)), u x ≤ v x) →
  ∀ x ∈ (Ω : Set (Space n)), u x ≤ v x

/-- All clauses of the source theorem, including both strong assertions. -/
def classicalComparisonStatement : Prop :=
  weakMaximumStatement ∧ strongMaximumStatement ∧
  weakMaximumZeroOrderFreeStatement ∧ strongMaximumZeroOrderFreeStatement ∧
  comparisonStatement

end P201Specs.Elliptic
