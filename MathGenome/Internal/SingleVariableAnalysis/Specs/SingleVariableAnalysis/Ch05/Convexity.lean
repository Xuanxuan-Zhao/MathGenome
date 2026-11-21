import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Analysis.Convex.Function

/-!
Independent specification for paper.tex:917–929, K03.05.convexity.
An interval means an order-connected real set, as in K03.03.interval_images;
this includes empty sets, singletons, unbounded intervals and all endpoint types.
The definitions below use the manuscript's literal formulas. They do not assume
continuity, differentiability, strict endpoint ordering, or nonempty domains.
-/

namespace Specs.SingleVariableAnalysis.Ch05.Convexity

/-- Predicates on real functions restricted to real domains. -/
def functionPredicateType : Type := Set ℝ → (ℝ → ℝ) → Prop

def convexFunctionOnValue : functionPredicateType := fun I f =>
  ∀ x ∈ I, ∀ y ∈ I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f ((1 - t) * x + t * y) ≤ (1 - t) * f x + t * f y

def strictConvexFunctionOnValue : functionPredicateType := fun I f =>
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ∀ t : ℝ, 0 < t → t < 1 →
    f ((1 - t) * x + t * y) < (1 - t) * f x + t * f y

/-- Concavity is convexity of the negative function. -/
def concaveFunctionOnValue : functionPredicateType := fun I f =>
  convexFunctionOnValue I (fun x => -f x)

/-- Both inequalities, with the common long secant in the middle. -/
def orderedSecantSlopesValue : functionPredicateType := fun I f =>
  ∀ x y z : ℝ, x ∈ I → y ∈ I → z ∈ I → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f x) / (z - x) ∧
      (f z - f x) / (z - x) ≤ (f z - f y) / (z - y)

/-- Identification with the canonical library predicate on every real interval. -/
def convexFunctionOnIffConvexOn : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ f : ℝ → ℝ,
    convexFunctionOnValue I f ↔ ConvexOn ℝ I f

def strictConvexFunctionOnIffStrictConvexOn : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ f : ℝ → ℝ,
    strictConvexFunctionOnValue I f ↔ StrictConvexOn ℝ I f

def concaveFunctionOnIffConcaveOn : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ f : ℝ → ℝ,
    concaveFunctionOnValue I f ↔ ConcaveOn ℝ I f

/-- The entire secant characterization, in both directions. -/
def convexFunctionOnIffOrderedSecantSlopes : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → ∀ f : ℝ → ℝ,
    convexFunctionOnValue I f ↔ orderedSecantSlopesValue I f

end Specs.SingleVariableAnalysis.Ch05.Convexity
