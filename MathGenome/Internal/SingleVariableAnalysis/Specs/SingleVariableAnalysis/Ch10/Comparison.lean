import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch10.OneEndpoint

/-! K03.10.comparison, paper.tex:2972–2990. All integrals below are finite
limits of proper Darboux integrals. Subtype indices range over the whole
regular interval, and their strict cofinal tails express the selected endpoint
approach, for finite endpoints and ±∞ alike. No sign restriction is imposed
on the discarded regular segment. -/
namespace Specs.SingleVariableAnalysis.Ch10.Comparison
open OneEndpoint

def rightComparison : Prop :=
  ∀ (f g : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ),
    rightRegularValue .real f a b → rightRegularValue .real g a b →
    (∃ r : rightIndexValue a b, ∀ x : rightIndexValue a b,
      r.val < x.val → 0 ≤ f x.val ∧ f x.val ≤ g x.val) →
    rightConvergesValue .real g a b → rightConvergesValue .real f a b

def leftComparison : Prop :=
  ∀ (f g : ℝ → ℝ) (a : WithBot ℝ) (b : ℝ),
    leftRegularValue .real f a b → leftRegularValue .real g a b →
    (∃ r : leftIndexValue a b, ∀ x : leftIndexValue a b,
      x.val < r.val → 0 ≤ f x.val ∧ f x.val ≤ g x.val) →
    leftConvergesValue .real g a b → leftConvergesValue .real f a b

def rightLimitComparison : Prop :=
  ∀ (f g : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ) (c : ℝ),
    rightRegularValue .real f a b → rightRegularValue .real g a b → 0 < c →
    (∃ r : rightIndexValue a b, ∀ x : rightIndexValue a b,
      r.val < x.val → 0 < f x.val ∧ 0 < g x.val) →
    (∀ ε : ℝ, 0 < ε → ∃ r : rightIndexValue a b,
      ∀ x : rightIndexValue a b, r.val < x.val → |f x.val / g x.val - c| < ε) →
    (rightConvergesValue .real f a b ↔ rightConvergesValue .real g a b)

def leftLimitComparison : Prop :=
  ∀ (f g : ℝ → ℝ) (a : WithBot ℝ) (b : ℝ) (c : ℝ),
    leftRegularValue .real f a b → leftRegularValue .real g a b → 0 < c →
    (∃ r : leftIndexValue a b, ∀ x : leftIndexValue a b,
      x.val < r.val → 0 < f x.val ∧ 0 < g x.val) →
    (∀ ε : ℝ, 0 < ε → ∃ r : leftIndexValue a b,
      ∀ x : leftIndexValue a b, x.val < r.val → |f x.val / g x.val - c| < ε) →
    (leftConvergesValue .real f a b ↔ leftConvergesValue .real g a b)

/-- Removing any regular initial segment preserves convergence, even for
sign-changing functions. The regularity hypothesis ensures that segment has
an existing finite proper integral. -/
def rightFinitePrefix : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ) (b : WithTop ℝ)
    (_h : rightRegularValue .real f a b) (r : rightIndexValue a b),
    rightConvergesValue .real f a b ↔ rightConvergesValue .real f r.val b

def leftFinitePrefix : Prop :=
  ∀ (f : ℝ → ℝ) (a : WithBot ℝ) (b : ℝ)
    (_h : leftRegularValue .real f a b) (r : leftIndexValue a b),
    leftConvergesValue .real f a b ↔ leftConvergesValue .real f a r.val

end Specs.SingleVariableAnalysis.Ch10.Comparison
