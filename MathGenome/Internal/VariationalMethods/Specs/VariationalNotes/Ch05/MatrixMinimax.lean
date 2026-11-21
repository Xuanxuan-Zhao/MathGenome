import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Matrix.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open scoped BigOperators
open Set

namespace VariationalNotes.Ch05.MatrixGame

/-- Probability vectors: nonnegative coordinates with sum one. -/
abbrev simplex (k : ℕ) : Set (Fin k → ℝ) := stdSimplex ℝ (Fin k)

/-- The coordinate expansion of `pᵀ M q`. -/
def payoff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * M i j * q j

/-- Coordinates of `Mᵀ p` and `M q`, respectively. -/
def columnPayoff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) (j : Fin n) : ℝ := ∑ i, p i * M i j

def rowPayoff {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (i : Fin m) : ℝ := ∑ j, M i j * q j

noncomputable def lower {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) : ℝ := sInf ((payoff M p) '' simplex n)

noncomputable def upper {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) : ℝ := sSup ((fun p => payoff M p q) '' simplex m)

namespace Specs

/-- The inner minimum is the smallest pure column payoff and is attained. -/
def FixedMinimum : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → ∀ (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ), p ∈ simplex m →
    ∃ j : Fin n,
      IsLeast (range (columnPayoff M p)) (columnPayoff M p j) ∧
      IsLeast ((payoff M p) '' simplex n) (columnPayoff M p j) ∧
      lower M p = sInf (range (columnPayoff M p))

/-- The inner maximum is the largest pure row payoff and is attained. -/
def FixedMaximum : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → ∀ (M : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ), q ∈ simplex n →
    ∃ i : Fin m,
      IsGreatest (range (rowPayoff M q)) (rowPayoff M q i) ∧
      IsGreatest ((fun p => payoff M p q) '' simplex m) (rowPayoff M q i) ∧
      upper M q = sSup (range (rowPayoff M q))

/-- Finite real minimax values, attained outer extrema, and a saddle pair. -/
def MatrixMinimax : Prop :=
  ∀ {m n : ℕ}, 0 < m → 0 < n → ∀ M : Matrix (Fin m) (Fin n) ℝ,
    ∃ p ∈ simplex m, ∃ q ∈ simplex n,
      (∀ p' ∈ simplex m, payoff M p' q ≤ payoff M p q) ∧
      (∀ q' ∈ simplex n, payoff M p q ≤ payoff M p q') ∧
      lower M p = payoff M p q ∧ upper M q = payoff M p q ∧
      IsGreatest (lower M '' simplex m) (payoff M p q) ∧
      IsLeast (upper M '' simplex n) (payoff M p q) ∧
      sSup (lower M '' simplex m) = sInf (upper M '' simplex n)

end Specs
end VariationalNotes.Ch05.MatrixGame
