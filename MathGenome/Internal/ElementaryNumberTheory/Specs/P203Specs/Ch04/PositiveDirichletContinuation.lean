import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Basic

noncomputable section

namespace P203Specs.Ch04.PositiveDirichletContinuation

/-- Lemma 4.7, paper.tex:1659–1689. `b n` is the coefficient at the
positive integer `n + 1`; thus there is no coefficient at zero. The
continuation is holomorphic on the entire open right half-plane. -/
def continuation_type : Prop :=
  ∀ (b : ℕ → ℝ), (∀ n, 0 ≤ b n) →
    (∀ s : ℂ, 1 < s.re →
      Summable (fun n : ℕ =>
        ‖(b n : ℂ) * Complex.exp (-s * (Real.log (n + 1) : ℂ))‖)) →
    ∀ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s | 0 < s.re} →
      (∀ s : ℂ, 1 < s.re →
        F s = ∑' n : ℕ,
          (b n : ℂ) * Complex.exp (-s * (Real.log (n + 1) : ℂ))) →
      ∀ σ : ℝ, 0 < σ →
        Summable (fun n : ℕ => b n * Real.exp (-σ * Real.log (n + 1)))

end P203Specs.Ch04.PositiveDirichletContinuation
