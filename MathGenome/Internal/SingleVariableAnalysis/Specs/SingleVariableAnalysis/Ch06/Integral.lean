import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Oriented

/-!
K03.06.integral, paper.tex:2804–2822. A closed derivative family is exactly
upstream compact C^(n+1) regularity, including the continuous one-sided endpoint
values. The explicit finite sum is T_n formed with those values; it does not use
the derivatives of an arbitrary extension outside [u,v]. The integrals are the
proper Darboux integrals on the compact hull, with the upstream orientation.
Both choices of scalar, all natural n, arbitrary a,x in [u,v], and singleton
intervals are included. Integrability is a conclusion.
-/
namespace Specs.SingleVariableAnalysis.Ch06.Integral
open Set
open scoped BigOperators
open Specs.SingleVariableAnalysis.Ch04.Higher

/-- The integral remainder for every continuous real endpoint derivative family. -/
def realIntegralRemainder : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (u v : ℝ) (D : ℕ → ℝ → ℝ),
    closedDerivativeFamilyValue (n+1) f u v D →
    ∀ a ∈ Icc u v, ∀ x ∈ Icc u v,
    ∃ h : Ch08.Oriented.realIntegrableValue
      (fun t => (x-t)^n * D (n+1) t) a x,
      f x - ∑ k ∈ Finset.range (n+1), D k a / (k.factorial : ℝ) * (x-a)^k =
        (1 / (n.factorial : ℝ)) * Ch08.Oriented.realIntegralValue _ h

/-- Real increments and complex endpoint derivatives; the integral is componentwise. -/
def complexIntegralRemainder : Prop :=
  ∀ (f : ℝ → ℂ) (n : ℕ) (u v : ℝ) (D : ℕ → ℝ → ℂ),
    closedDerivativeFamilyValue (n+1) f u v D →
    ∀ a ∈ Icc u v, ∀ x ∈ Icc u v,
    ∃ h : Ch08.Oriented.complexIntegrableValue
      (fun t => (algebraMap ℝ ℂ (x-t))^n * D (n+1) t) a x,
      f x - ∑ k ∈ Finset.range (n+1),
        D k a / (k.factorial : ℂ) * (algebraMap ℝ ℂ (x-a))^k =
        (1 / (n.factorial : ℂ)) * Ch08.Oriented.complexIntegralValue _ h

/-- Canonical closed-interval real derivatives give the same formula. -/
def realIntegralRemainderWithin : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (u v : ℝ),
    ContDiffOn ℝ (n+1 : ℕ) f (Icc u v) →
    ∀ a ∈ Icc u v, ∀ x ∈ Icc u v,
    ∃ h : Ch08.Oriented.realIntegrableValue
      (fun t => (x-t)^n * iteratedDerivWithin (n+1) f (Icc u v) t) a x,
      f x - ∑ k ∈ Finset.range (n+1),
        iteratedDerivWithin k f (Icc u v) a / (k.factorial : ℝ) * (x-a)^k =
        (1 / (n.factorial : ℝ)) * Ch08.Oriented.realIntegralValue _ h

/-- Canonical closed-interval complex derivatives, with base field ℝ. -/
def complexIntegralRemainderWithin : Prop :=
  ∀ (f : ℝ → ℂ) (n : ℕ) (u v : ℝ),
    ContDiffOn ℝ (n+1 : ℕ) f (Icc u v) →
    ∀ a ∈ Icc u v, ∀ x ∈ Icc u v,
    ∃ h : Ch08.Oriented.complexIntegrableValue
      (fun t => (algebraMap ℝ ℂ (x-t))^n *
        iteratedDerivWithin (n+1) f (Icc u v) t) a x,
      f x - ∑ k ∈ Finset.range (n+1),
        iteratedDerivWithin k f (Icc u v) a / (k.factorial : ℂ) *
          (algebraMap ℝ ℂ (x-a))^k =
        (1 / (n.factorial : ℂ)) * Ch08.Oriented.complexIntegralValue _ h

end Specs.SingleVariableAnalysis.Ch06.Integral
