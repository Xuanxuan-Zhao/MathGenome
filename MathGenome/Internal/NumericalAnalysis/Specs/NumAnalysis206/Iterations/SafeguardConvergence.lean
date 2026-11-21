import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Iterations.SafeguardStep
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact

/-! Independent scope of paper.tex, Theorem p206:W65. The sequence index counts
successful endpoint replacements, not attempts. A finite prefix imposes no
conditions after its last completed update. All points and bounds are real. -/
namespace Specs.NumAnalysis206.Iterations.SafeguardConvergence
open Specs.NumAnalysis206.Iterations.SafeguardStep
open Filter Topology

/-- A completed update is witnessed by an actual sound attempt of the shared rule. -/
def Update (f : ℝ → ℝ) (α : ℝ) (l r : ℕ → ℝ) (n : ℕ) : Prop :=
  ∃ point sign, Sound f point sign ∧
    attempt f α (l n) (r n) point sign = .updated (l (n + 1)) (r (n + 1))

/-- Exactly the first `N` transitions are required to be successful. -/
structure Prefix (f : ℝ → ℝ) (α a b : ℝ) (l r : ℕ → ℝ) (N : ℕ) : Prop where
  left_initial : l 0 = a
  right_initial : r 0 = b
  updates : ∀ n < N, Update f α l r n

/-- The enclosure and geometric width after `n` successful updates. -/
def Invariant (f : ℝ → ℝ) (α a b : ℝ) (l r : ℕ → ℝ) (n : ℕ) : Prop :=
  a ≤ l n ∧ l n < r n ∧ r n ≤ b ∧ f (l n) * f (r n) < 0 ∧
    r n - l n ≤ (b - a) * (1 - α) ^ n

def finiteBounds : Prop :=
  ∀ (f : ℝ → ℝ) (α a b : ℝ) (l r : ℕ → ℝ),
    0 < α → α ≤ 1 / 2 → a < b → f a * f b < 0 →
    ∀ N, Prefix f α a b l r N → ∀ n ≤ N, Invariant f α a b l r n

/-- One common root belongs to every bracket. Both endpoints and the exact
midpoints tend to that root, with the stated bound at every index, including 0. -/
def infiniteConvergence : Prop :=
  ∀ (f : ℝ → ℝ) (α a b : ℝ) (l r : ℕ → ℝ),
    0 < α → α ≤ 1 / 2 → a < b → ContinuousOn f (Set.Icc a b) →
    f a * f b < 0 → l 0 = a → r 0 = b → (∀ n, Update f α l r n) →
    (∀ n, Invariant f α a b l r n) ∧
    (∀ i j, i ≤ j → Set.Icc (l j) (r j) ⊆ Set.Icc (l i) (r i)) ∧
    ∃ p : ℝ, f p = 0 ∧ (∀ n, p ∈ Set.Icc (l n) (r n)) ∧
      Tendsto l atTop (𝓝 p) ∧ Tendsto r atTop (𝓝 p) ∧
      Tendsto (fun n => (l n + r n) / 2) atTop (𝓝 p) ∧
      (∀ n, |(l n + r n) / 2 - p| ≤ (b - a) * (1 - α) ^ n / 2)

/-- These shared policies include midpoint fallback for undefined proposals,
strict sign preservation, certified-root return, enclosure retention on failures,
and counting only successful updates. -/
def attemptRules : Prop :=
  selection ∧ stepSafety ∧ failurePolicy ∧ countPolicy ∧ rootCertificate

/-- Complete W65, including finite prefixes and the stopping qualifications. -/
def safeguardedBracketing : Prop :=
  attemptRules ∧ finiteBounds ∧ infiniteConvergence

end Specs.NumAnalysis206.Iterations.SafeguardConvergence
