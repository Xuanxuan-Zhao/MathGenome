import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction

/-!
Independent specification for the decay estimate in K03.06.smooth_flat
(paper.tex:2871–2886) and the power estimates in K03.17.flat_remainder
(paper.tex:4369–4384). The exponential is the shared factorial-series
construction. Natural indices enumerate all nonnegative integers; the
negative exponent in the first limit is an integer power.

The limit is two-sided and punctured. The zero extension's little-o estimates
are stated even on the full neighborhood filter, including its value at zero.
The finite sums with zero coefficients express the all-orders zero power
expansion. Smoothness and derivative representations are separate goals.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch06.FlatDecay

open Filter
open scoped Topology BigOperators

abbrev flatExponentialType := ℝ → ℝ

def flatExponentialValue : flatExponentialType := fun x =>
  if x = 0 then 0 else Ch07.ExpConstruction.realSeriesExpValue (-1 / x ^ 2)

def inversePowerDecay : Prop :=
  ∀ N : ℕ, Tendsto
    (fun x : ℝ => |x| ^ (-(N : ℤ)) *
      Ch07.ExpConstruction.realSeriesExpValue (-1 / x ^ 2))
    (𝓝[≠] 0) (𝓝 0)

def littleOEveryPower : Prop :=
  ∀ m : ℕ, Ch02.BigO.scalarLittleOValue (𝓝 (0 : ℝ))
    flatExponentialValue (fun x => |x| ^ m)

def positiveOffZero : Prop :=
  ∀ x : ℝ, x ≠ 0 → 0 < flatExponentialValue x

def zeroPowerExpansion : Prop :=
  ∀ m : ℕ, Ch02.BigO.scalarLittleOValue (𝓝 (0 : ℝ))
    (fun x => flatExponentialValue x -
      ∑ k ∈ Finset.range (m + 1), (0 : ℝ) * x ^ k)
    (fun x => |x| ^ m)

end Specs.SingleVariableAnalysis.Ch06.FlatDecay
