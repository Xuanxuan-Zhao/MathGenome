import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-! Independent statements for the cotangent assertion of paper.tex:2837–2851,
D12.16.08. The index n : ℕ denotes the pair at the positive integer n + 1.
Every summand is the single paired rational expression 2z / (z² - (n+1)²).
The domain is exactly the complement of all integer points in ℂ.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace Specs.D12Complex.Ch16.CotangentPartialFractions

def cotangent_paired_hasSum_type : Prop :=
  ∀ z : ℂ, z ∈ Complex.integerComplement →
    HasSum (fun n : ℕ => 2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2))
      ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z)

def cotangent_partial_fractions_type : Prop :=
  ∀ z : ℂ, z ∈ Complex.integerComplement →
    (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      1 / z + ∑' n : ℕ, 2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2)

def cotangent_paired_locally_uniform_type : Prop :=
  HasSumLocallyUniformlyOn
    (fun (n : ℕ) (z : ℂ) => 2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2))
    (fun z => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z)
    Complex.integerComplement

/-- The displayed paired order: the N-th partial sum contains the pairs at
1, 2, ..., N. Local uniform convergence holds on all of ℂ ∖ ℤ. -/
def cotangent_paired_partial_sums_type : Prop :=
  TendstoLocallyUniformlyOn
    (fun (N : ℕ) (z : ℂ) =>
      ∑ n ∈ Finset.range N, 2 * z / (z ^ 2 - ((n : ℂ) + 1) ^ 2))
    (fun z => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) - 1 / z)
    atTop Complex.integerComplement

end Specs.D12Complex.Ch16.CotangentPartialFractions
