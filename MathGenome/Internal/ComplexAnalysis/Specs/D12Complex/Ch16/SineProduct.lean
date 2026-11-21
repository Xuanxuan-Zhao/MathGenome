import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-! Independent statements for the sine-product part of D12.16.08,
paper.tex:2837–2851. Index n : ℕ is the positive integer n+1, and
Finset.range N includes exactly the factors at 1,...,N. The convergence
domain includes the integer zeros and the origin. -/
noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace Specs.D12Complex.Ch16.SineProduct
open _root_.D12Complex

/-- The paired factors converge locally uniformly on all of the plane. -/
def sine_paired_locally_uniform_type : Prop :=
  TendstoLocallyUniformlyOn
    (fun (N : ℕ) (z : ℂ) =>
      ∏ n ∈ Finset.range N, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2))
    (fun z => ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) atTop univ

/-- The identity holds at every complex point, including all integer zeros. -/
def sine_product_type : Prop :=
  ∀ z : ℂ, Complex.sin ((Real.pi : ℂ) * z) =
    (Real.pi : ℂ) * z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)

/-- The product after including the factor z is entire in the canonical sense. -/
def sine_product_holomorphic_type : Prop :=
  HolomorphicOn univ (fun z : ℂ =>
    z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2))

/-- There are no additional zeros. -/
def sine_product_zero_iff_type : Prop :=
  ∀ z : ℂ, (z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) = 0 ↔
    ∃ m : ℤ, z = (m : ℂ)

/-- All the integer zeros, including zero, have exactly order one. -/
def sine_product_simple_integer_zeros_type : Prop :=
  ∀ m : ℤ, analyticOrderAt (fun z : ℂ =>
    z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) (m : ℂ) = 1

/-- The unscaled product is normalized to one at zero and Q(z)/z → 1. -/
def sine_product_normalization_type : Prop :=
  (∏' n : ℕ, (1 - (0 : ℂ) ^ 2 / ((n : ℂ) + 1) ^ 2)) = 1 ∧
  Tendsto (fun z : ℂ =>
    (z * ∏' n : ℕ, (1 - z ^ 2 / ((n : ℂ) + 1) ^ 2)) / z)
    (𝓝[≠] 0) (𝓝 1)

end Specs.D12Complex.Ch16.SineProduct
