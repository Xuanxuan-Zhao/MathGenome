import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticSurdRecurrence

/-! The representation and eventual reduction stages of `paper.tex`, nt:E08,
lines 2496–2518. All complete quotients are the canonical stopping-aware
objects. The denominator is signed, including at the initial index. -/
namespace P203Specs

/-- A single positive nonsquare discriminant represents every complete quotient,
with admissible integer states and exactly the signed surd updates. -/
def QuadraticSurdExpansion : Prop :=
  ∀ x : ℝ, QuadraticIrrational x →
    ∃ (D : ℤ) (P Q : ℕ → ℤ), 0 < D ∧ ¬ IsSquare D ∧
      (∀ n : ℕ, Q n ≠ 0 ∧ Q n ∣ D - P n ^ 2 ∧
        completeQuotient x n = some (((P n : ℝ) + Real.sqrt (D : ℝ)) / (Q n : ℝ))) ∧
      (∀ n : ℕ, P (n + 1) = surdNextP (P n) (Q n) D ∧
        Q (n + 1) = surdNextQ (P n) (Q n) D)

/-- Eventually every canonical complete quotient is reduced. In particular,
quadraticity and both strict conjugate bounds are conclusions. -/
def QuadraticEventualReduction : Prop :=
  ∀ x : ℝ, QuadraticIrrational x →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ α : ℝ, completeQuotient x n = some α ∧ ReducedQuadratic α

end P203Specs
