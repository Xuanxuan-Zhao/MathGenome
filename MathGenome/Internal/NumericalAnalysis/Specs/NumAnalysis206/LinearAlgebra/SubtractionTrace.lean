import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-! Independent statements for paper.tex (4.1), `p206:subtracttrace`.
The data are arbitrary real sequences restricted to the finite interval 1,…,k.
The state starts at s 0. Products over Ico 1 t contain precisely the earlier
subtraction factors, and all empty sums/products have their usual values.
Only nonvanishing of each subtraction factor is needed for these identities.
-/

namespace NumAnalysis206.LinearAlgebra.SubtractionTrace.Specs

def one_step_inverse : Prop :=
  ∀ (a b μ σ sPrev sNext : ℝ),
    sNext = (sPrev - a * b * (1 + μ)) * (1 + σ) →
    1 + σ ≠ 0 →
    sPrev = sNext / (1 + σ) + a * b * (1 + μ)

def subtraction_trace : Prop :=
  ∀ (k : ℕ) (a b μ σ s : ℕ → ℝ),
    (∀ t ∈ Finset.Icc 1 k,
      s t = (s (t - 1) - a t * b t * (1 + μ t)) * (1 + σ t)) →
    (∀ t ∈ Finset.Icc 1 k, 1 + σ t ≠ 0) →
    s 0 = s k * (∏ j ∈ Finset.Icc 1 k, (1 + σ j)⁻¹) +
      ∑ t ∈ Finset.Icc 1 k,
        a t * b t * (1 + μ t) * (∏ j ∈ Finset.Ico 1 t, (1 + σ j)⁻¹)

end NumAnalysis206.LinearAlgebra.SubtractionTrace.Specs
