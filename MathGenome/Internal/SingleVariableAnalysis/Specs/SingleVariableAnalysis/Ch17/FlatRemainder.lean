import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.FlatDecay
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.CoefficientUnique

/-!
Independent specification of K03.17.flat_remainder, paper.tex:4369–4384.
The function is exactly the shared zero extension of exp(-1/x²). The approach
is two-sided and punctured at zero, with every nonnegative integer order.
The power family consists of x^j; norms in the remainder estimates therefore
give |x|^j. All-orders expansions use finite sums and one fixed coefficient
sequence, with no assertion about convergence of an infinite series.
-/

namespace Specs.SingleVariableAnalysis.Ch17.FlatRemainder

open Filter
open scoped Topology

def powerScaleAtZero : Prop :=
  AsymptoticScale.isScalarAsymptoticScaleValue (𝓝[≠] (0 : ℝ))
    (fun j x => x ^ j)

def littleOEveryPower : Prop :=
  ∀ m : ℕ, Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ))
    Ch06.FlatDecay.flatExponentialValue (fun x => |x| ^ m)

def positiveOffZero : Prop :=
  ∀ x : ℝ, x ≠ 0 → 0 < Ch06.FlatDecay.flatExponentialValue x

def commonZeroExpansion : Prop :=
  AsymptoticScale.hasScalarAsymptoticExpansionValue (𝓝[≠] (0 : ℝ))
      (fun j x => x ^ j) (fun _ => 0) Ch06.FlatDecay.flatExponentialValue ∧
    AsymptoticScale.hasScalarAsymptoticExpansionValue (𝓝[≠] (0 : ℝ))
      (fun j x => x ^ j) (fun _ => 0) (fun _ => 0)

def coefficientsExactlyZero : Prop :=
  ∀ a : ℕ → ℝ,
    (AsymptoticScale.hasScalarAsymptoticExpansionValue (𝓝[≠] (0 : ℝ))
        (fun j x => x ^ j) a Ch06.FlatDecay.flatExponentialValue ↔ a = fun _ => 0) ∧
    (AsymptoticScale.hasScalarAsymptoticExpansionValue (𝓝[≠] (0 : ℝ))
        (fun j x => x ^ j) a (fun _ => 0) ↔ a = fun _ => 0)

def differsEveryPuncturedNeighborhood : Prop :=
  ∀ δ : ℝ, 0 < δ →
    (∀ x : ℝ, 0 < |x| → |x| < δ → Ch06.FlatDecay.flatExponentialValue x ≠ 0) ∧
    ∃ x : ℝ, 0 < |x| ∧ |x| < δ ∧ Ch06.FlatDecay.flatExponentialValue x ≠ 0

end Specs.SingleVariableAnalysis.Ch17.FlatRemainder
