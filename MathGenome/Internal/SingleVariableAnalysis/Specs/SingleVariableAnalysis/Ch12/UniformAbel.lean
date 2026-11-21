import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Algebra.BigOperators.Intervals

/-!
Independent specification of K03.12.uniform_abel (paper.tex:1295–1307).
A series converges uniformly when its inclusive finite partial sums do.
The domain is arbitrary, including empty domains. At each point the real
multiplier may be nondecreasing or nonincreasing, with the choice depending
on that point. The bound is common to all terms and all points. No limit
of the multipliers, uniform or otherwise, is assumed. The statements include
zero bounds and conditionally convergent series.
-/

namespace Specs.SingleVariableAnalysis.Ch12.UniformAbel

open scoped BigOperators
universe u

def realUniformAbel : Prop :=
  ∀ {E : Type u} (a : ℕ → E → ℝ) (b : ℕ → E → ℝ) (M : ℝ),
    (∃ f : E → ℝ, Uniform.realUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.range (N + 1), a n x) f) →
    (∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x)) →
    (∀ x n, |b n x| ≤ M) →
    ∃ g : E → ℝ, Uniform.realUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.range (N + 1), a n x * b n x) g

def complexUniformAbel : Prop :=
  ∀ {E : Type u} (a : ℕ → E → ℂ) (b : ℕ → E → ℝ) (M : ℝ),
    (∃ f : E → ℂ, Uniform.complexUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.range (N + 1), a n x) f) →
    (∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x)) →
    (∀ x n, |b n x| ≤ M) →
    ∃ g : E → ℂ, Uniform.complexUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.range (N + 1), a n x * (b n x : ℂ)) g

end Specs.SingleVariableAnalysis.Ch12.UniformAbel
