import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BisectionInvariants

/-! Independent infinite-run statement of paper.tex, Theorem p206:W63.
The factor `(1/2)^n` is `2^(-n)`; index zero counts zero updates.
Uniqueness below concerns the intersection of the chosen brackets, not all
roots of the function in the initial interval. -/

namespace Specs.NumAnalysis206.Iterations.BisectionConvergence

open BisectionInvariants
open Filter
open scoped Topology

/-- An infinite run assumes only initial endpoints and permitted exact updates. -/
structure InfiniteRun (f : ℝ → ℝ) (a b : ℝ) where
  left : ℕ → ℝ
  right : ℕ → ℝ
  left_zero : left 0 = a
  right_zero : right 0 = b
  step : ∀ n, LegalHalf f (left n) (right n) (left (n+1)) (right (n+1))

/-- Every finite prefix uses precisely the existing finite-run interface. -/
def InfiniteRun.toFinite {f : ℝ → ℝ} {a b : ℝ} (r : InfiniteRun f a b) (N : ℕ) :
    FiniteRun f a b N where
  left := r.left
  right := r.right
  left_zero := r.left_zero
  right_zero := r.right_zero
  step n _ := r.step n

/-- The full finite invariants and per-bracket root-distance conclusion,
now at every index of an infinite run. -/
def RunInvariants (f : ℝ → ℝ) (a b : ℝ) (r : InfiniteRun f a b) : Prop :=
  (∀ n, r.left n < r.right n ∧
    Set.Icc (r.left n) (r.right n) ⊆ Set.Icc a b ∧
    f (r.left n) * f (r.right n) ≤ 0 ∧
    r.right n - r.left n = (1 / 2 : ℝ)^n * (b-a) ∧
    ∃ p ∈ Set.Icc (r.left n) (r.right n), f p = 0 ∧
      |midpoint (r.left n) (r.right n) - p| ≤ (1 / 2 : ℝ)^(n+1) * (b-a)) ∧
  (∀ n, Set.Icc (r.left (n+1)) (r.right (n+1)) ⊆
    Set.Icc (r.left n) (r.right n))

/-- Complete infinite-run conclusion, including all finite invariants.
Only continuity on the original closed bracket is required. -/
def infiniteConvergence : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∀ r : InfiniteRun f a b,
      RunInvariants f a b r ∧
      ∃ p : ℝ,
        (∀ n, p ∈ Set.Icc (r.left n) (r.right n)) ∧
        f p = 0 ∧
        (∀ q : ℝ, (∀ n, q ∈ Set.Icc (r.left n) (r.right n)) → q = p) ∧
        Tendsto r.left atTop (𝓝 p) ∧
        Tendsto r.right atTop (𝓝 p) ∧
        Tendsto (fun n => midpoint (r.left n) (r.right n)) atTop (𝓝 p) ∧
        ∀ n, |midpoint (r.left n) (r.right n) - p| ≤
          (1 / 2 : ℝ)^(n+1) * (b-a)

end Specs.NumAnalysis206.Iterations.BisectionConvergence
