import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.BracketExistence

/-! Independent finite-run model and statements for paper.tex, p206:W63.
Index zero is the initial interval. A run of length N has N completed halvings
and N+1 available intervals. No invariant is included among the run's fields.
The factor (1/2)^n is the source's 2^(-n), with natural-number indexing. -/

namespace Specs.NumAnalysis206.Iterations.BisectionInvariants

/-- Exact real midpoint. -/
noncomputable def midpoint (a b : ℝ) : ℝ := (a + b) / 2

/-- Either exact half is permitted, provided its endpoint product is nonpositive.
This includes a zero endpoint and a zero midpoint, without a strict-sign test. -/
def LegalHalf (f : ℝ → ℝ) (a b c d : ℝ) : Prop :=
  ((c = a ∧ d = midpoint a b) ∨ (c = midpoint a b ∧ d = b)) ∧
    f c * f d ≤ 0

/-- Early success returns only an endpoint or the exact midpoint known to be zero. -/
def SuccessfulReturn (f : ℝ → ℝ) (a b p : ℝ) : Prop :=
  (p = a ∨ p = midpoint a b ∨ p = b) ∧ f p = 0

/-- The only assumptions on later intervals are the algorithm's legal updates. -/
structure FiniteRun (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) where
  left : ℕ → ℝ
  right : ℕ → ℝ
  left_zero : left 0 = a
  right_zero : right 0 = b
  step : ∀ n, n < N → LegalHalf f (left n) (right n) (left (n+1)) (right (n+1))

/-- A half is always available, even if an endpoint or midpoint vanishes.
Each of these three known-zero tests also permits immediate successful return. -/
def stepAvailability : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → f a * f b ≤ 0 →
    (∃ c d, LegalHalf f a b c d) ∧
    (f a = 0 → SuccessfulReturn f a b a) ∧
    (f (midpoint a b) = 0 → SuccessfulReturn f a b (midpoint a b)) ∧
    (f b = 0 → SuccessfulReturn f a b b)

/-- Geometry and exact width of any permitted update. -/
def halfProperties : Prop :=
  ∀ (f : ℝ → ℝ) (a b c d : ℝ), a < b → LegalHalf f a b c d →
    c < d ∧ Set.Icc c d ⊆ Set.Icc a b ∧ f c * f d ≤ 0 ∧
      d - c = (b - a) / 2

/-- Every available interval retains a root and the midpoint has the source's
half-width error bound. All updates that exist give nested intervals. -/
def finiteInvariants : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ) (N : ℕ), a < b →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∀ r : FiniteRun f a b N,
      (∀ n, n ≤ N →
        r.left n < r.right n ∧
        Set.Icc (r.left n) (r.right n) ⊆ Set.Icc a b ∧
        f (r.left n) * f (r.right n) ≤ 0 ∧
        r.right n - r.left n = (1 / 2 : ℝ)^n * (b-a) ∧
        ∃ p ∈ Set.Icc (r.left n) (r.right n), f p = 0 ∧
          |midpoint (r.left n) (r.right n) - p| ≤
            (1 / 2 : ℝ)^(n+1) * (b-a)) ∧
      (∀ n, n < N → Set.Icc (r.left (n+1)) (r.right (n+1)) ⊆
        Set.Icc (r.left n) (r.right n))

/-- Early success at any available interval returns a root in that interval
and in the original bracket. -/
def returnCorrectness : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ) (N : ℕ), a < b →
    ContinuousOn f (Set.Icc a b) → f a * f b ≤ 0 →
    ∀ (r : FiniteRun f a b N) (n : ℕ), n ≤ N →
    ∀ p, SuccessfulReturn f (r.left n) (r.right n) p →
      p ∈ Set.Icc (r.left n) (r.right n) ∧ p ∈ Set.Icc a b ∧ f p = 0

end Specs.NumAnalysis206.Iterations.BisectionInvariants
