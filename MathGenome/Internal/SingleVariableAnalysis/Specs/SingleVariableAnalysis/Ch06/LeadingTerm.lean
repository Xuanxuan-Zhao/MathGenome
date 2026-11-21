import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.Peano
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.Equivalence
import Mathlib.Topology.Order.LocalExtr

/-! Independent specification of K03.06.leading_term, paper.tex:2829–2843.
Real increments and real iterated derivatives are used for both scalar fields.
The last derivative exists only at a; no continuity of it is assumed.
Strict extrema are stated directly as strict inequalities on a punctured
neighborhood. The odd-order conclusion excludes even non-strict extrema.
A function on an interval near an interior point is represented by an ambient
extension; the hypotheses and conclusions depend only on its local germ. -/
namespace Specs.SingleVariableAnalysis.Ch06.LeadingTerm
open Filter
open scoped Topology
universe u

def leadingTermPeano : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ) (c : K),
    1 ≤ n →
    (∃ U ∈ 𝓝 a, Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    (∀ j, 1 ≤ j → j < n → Ch04.Higher.realIteratedDerivativeValue j f a = 0) →
    c = Ch04.Higher.realIteratedDerivativeValue n f a / (n.factorial : K) →
    c ≠ 0 →
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => (f (a+h) - f a) - c * (algebraMap ℝ K h)^n)
      (fun h : ℝ => h^n)

def leadingTermEquivalent : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ) (c : K),
    1 ≤ n →
    (∃ U ∈ 𝓝 a, Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    (∀ j, 1 ≤ j → j < n → Ch04.Higher.realIteratedDerivativeValue j f a = 0) →
    c = Ch04.Higher.realIteratedDerivativeValue n f a / (n.factorial : K) →
    c ≠ 0 →
    Ch02.Equivalence.scalarEquivalentValue (𝓝[≠] (0 : ℝ))
      (fun h => f (a+h) - f a) (fun h => c * (algebraMap ℝ K h)^n)

def leadingTermStrictMin : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a c : ℝ),
    1 ≤ n →
    (∃ U ∈ 𝓝 a, Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    (∀ j, 1 ≤ j → j < n → Ch04.Higher.realIteratedDerivativeValue j f a = 0) →
    c = Ch04.Higher.realIteratedDerivativeValue n f a / (n.factorial : ℝ) →
    Even n → 0 < c → ∀ᶠ x in 𝓝[≠] a, f a < f x

def leadingTermStrictMax : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a c : ℝ),
    1 ≤ n →
    (∃ U ∈ 𝓝 a, Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    (∀ j, 1 ≤ j → j < n → Ch04.Higher.realIteratedDerivativeValue j f a = 0) →
    c = Ch04.Higher.realIteratedDerivativeValue n f a / (n.factorial : ℝ) →
    Even n → c < 0 → ∀ᶠ x in 𝓝[≠] a, f x < f a

def leadingTermOdd : Prop :=
  ∀ (f : ℝ → ℝ) (n : ℕ) (a c : ℝ),
    1 ≤ n →
    (∃ U ∈ 𝓝 a, Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ (Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    (∀ j, 1 ≤ j → j < n → Ch04.Higher.realIteratedDerivativeValue j f a = 0) →
    c = Ch04.Higher.realIteratedDerivativeValue n f a / (n.factorial : ℝ) →
    Odd n → c ≠ 0 → ¬ IsLocalMin f a ∧ ¬ IsLocalMax f a

end Specs.SingleVariableAnalysis.Ch06.LeadingTerm
