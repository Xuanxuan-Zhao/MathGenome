import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.TaylorPolynomial
import Mathlib.Analysis.Asymptotics.Lemmas

/-! K03.06.peano, paper.tex:2769–2780. The lower derivatives exist on
some neighborhood; only the derivative of order n-1 at a is required at
the last order. In particular this is not a C^n hypothesis. All increments
and derivatives are real, also when the target is ℂ. -/
namespace Specs.SingleVariableAnalysis.Ch06.Peano
open Filter
open scoped Topology
universe u

/-- The full Peano approximation under the source's pointwise top-order
hypothesis. The neighborhood may be chosen arbitrarily small inside the
original domain, since a is interior. -/
def taylorPeano : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ),
    1 ≤ n →
    (∃ U ∈ 𝓝 a,
      Specs.SingleVariableAnalysis.Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ
      (Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a+h) -
        ∑ k ∈ Finset.range (n+1),
          (Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue k f a /
            (k.factorial : K)) * (algebraMap ℝ K h)^k)
      (fun h : ℝ => h^n)

/-- The same estimate for the canonical Taylor remainder. -/
def taylorRemainderPeano : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (n : ℕ) (a : ℝ),
    1 ≤ n →
    (∃ U ∈ 𝓝 a,
      Specs.SingleVariableAnalysis.Ch04.Higher.kTimesDifferentiableOnValue (n-1) f U) →
    DifferentiableAt ℝ
      (Specs.SingleVariableAnalysis.Ch04.Higher.realIteratedDerivativeValue (n-1) f) a →
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => TaylorPolynomial.taylorRemainderValue f n a (a+h))
      (fun h : ℝ => h^n)

/-- Order zero is exactly continuity, in both directions. -/
def taylorPeanoZeroIff : Prop :=
  ∀ {K : Type u} [RCLike K] (f : ℝ → K) (a : ℝ),
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a+h) - f a) (fun h : ℝ => h^0) ↔ ContinuousAt f a

end Specs.SingleVariableAnalysis.Ch06.Peano
