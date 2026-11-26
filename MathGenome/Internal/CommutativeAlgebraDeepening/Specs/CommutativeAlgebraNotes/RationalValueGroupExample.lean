import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ValuationPrimesAndConvexSubgroups
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

noncomputable section

namespace Specs.CommutativeAlgebraNotes.RationalValueGroupExample

open OrderedValuationGroups (valueGroup value AddValuationInequality)
open ValuationPrimesAndConvexSubgroups (convexAddSubgroup)

universe u

/-- The indices start at zero, so index `i` represents the field with
generator `t^(1/(i+1)!)`. -/
def embeddingExponent (i j : ℕ) : ℕ :=
  (j + 1).factorial / (i + 1).factorial

/-- A fraction's order at the generator, normalized for its stage in the union. -/
def normalizedOrder {k : Type u} [Field k] (i : ℕ) (p q : Polynomial k) : ℚ :=
  ((p.natTrailingDegree : ℚ) - (q.natTrailingDegree : ℚ)) / ((i + 1).factorial : ℚ)

/-- The rational ordered group has precisely its two extreme convex subgroups. -/
def ConvexSubgroups : Prop :=
  ∀ H : convexAddSubgroup ℚ, H.1 = ⊥ ∨ H.1 = ⊤

/-- The factorial tower of rational function fields, its valuation, and the resulting ring. -/
def Example : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (K : Type u) (_ : Field K)
      (transition : ∀ i j : ℕ, i ≤ j → RatFunc k →+* RatFunc k)
      (includeStage : ℕ → RatFunc k →+* K)
      (v : Additive Kˣ →+ ℚ) (V : ValuationSubring K),
      (∀ (i j : ℕ) (h : i ≤ j) (p : Polynomial k),
        transition i j h (algebraMap (Polynomial k) (RatFunc k) p) =
          algebraMap (Polynomial k) (RatFunc k) (Polynomial.expand k (embeddingExponent i j) p)) ∧
      (∀ i : ℕ, transition i (i + 1) (Nat.le_succ i) RatFunc.X =
        (RatFunc.X : RatFunc k) ^ (i + 2)) ∧
      (∀ i : ℕ, Function.Injective (includeStage i)) ∧
      (∀ (i j : ℕ) (h : i ≤ j) (x : RatFunc k),
        includeStage j (transition i j h x) = includeStage i x) ∧
      (∀ x : K, ∃ (i : ℕ) (y : RatFunc k), includeStage i y = x) ∧
      AddValuationInequality v ∧
      (∀ (i : ℕ) (p q : Polynomial k) (_ : p ≠ 0) (_ : q ≠ 0)
        (h : includeStage i (algebraMap (Polynomial k) (RatFunc k) p /
          algebraMap (Polynomial k) (RatFunc k) q) ≠ 0),
        v (Additive.ofMul (Units.mk0 (includeStage i
          (algebraMap (Polynomial k) (RatFunc k) p / algebraMap (Polynomial k) (RatFunc k) q)) h)) =
            normalizedOrder i p q) ∧
      Function.Surjective v ∧
      (∀ x : K, x ∈ V ↔ x = 0 ∨ ∃ h : x ≠ 0, 0 ≤ v (Additive.ofMul (Units.mk0 x h))) ∧
      (∃ e : valueGroup V ≃+o ℚ, ∀ a : Additive Kˣ, e (value V a) = v a) ∧
      ringKrullDim V = 1 ∧ ¬ IsNoetherianRing V

end Specs.CommutativeAlgebraNotes.RationalValueGroupExample
