import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.Uniform
import Mathlib.Algebra.BigOperators.Intervals

/-!
Independent specification of K03.12.uniform_dirichlet, paper.tex:1285–1298.
The domain is arbitrary (a subset is represented by its subtype), and may
be empty. Series are ordinary ordered inclusive partial sums from zero,
not unconditional `Summable` families. The weights are real in both cases.
The disjunction of monotonicity directions is inside `∀ x`, so different
points can have different directions. No sign or strict positivity of the
partial-sum bound is assumed. The two finite-tail conclusions retain the
constant 2M, including p = 0 and p = q.
-/
namespace Specs.SingleVariableAnalysis.Ch12.UniformDirichlet

open scoped BigOperators
universe u

def realTailBound : Prop :=
  ∀ {E : Type u} (a : ℕ → E → ℝ) (b : ℕ → E → ℝ) (M : ℝ),
    (∀ x N, |∑ n ∈ Finset.range (N + 1), a n x| ≤ M) →
    (∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x)) →
    Uniform.realUniformConvergesValue b (fun _ => 0) →
    ∀ x p q, p ≤ q →
      |∑ n ∈ Finset.Icc p q, a n x * b n x| ≤ 2 * M * |b p x|

def complexTailBound : Prop :=
  ∀ {E : Type u} (a : ℕ → E → ℂ) (b : ℕ → E → ℝ) (M : ℝ),
    (∀ x N, ‖∑ n ∈ Finset.range (N + 1), a n x‖ ≤ M) →
    (∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x)) →
    Uniform.realUniformConvergesValue b (fun _ => 0) →
    ∀ x p q, p ≤ q →
      ‖∑ n ∈ Finset.Icc p q, a n x * (b n x : ℂ)‖ ≤ 2 * M * |b p x|

def realUniformDirichlet : Prop :=
  ∀ {E : Type u} (a : ℕ → E → ℝ) (b : ℕ → E → ℝ) (M : ℝ),
    (∀ x N, |∑ n ∈ Finset.range (N + 1), a n x| ≤ M) →
    (∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x)) →
    Uniform.realUniformConvergesValue b (fun _ => 0) →
    ∃ f : E → ℝ, Uniform.realUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.range (N + 1), a n x * b n x) f

def complexUniformDirichlet : Prop :=
  ∀ {E : Type u} (a : ℕ → E → ℂ) (b : ℕ → E → ℝ) (M : ℝ),
    (∀ x N, ‖∑ n ∈ Finset.range (N + 1), a n x‖ ≤ M) →
    (∀ x, Monotone (fun n => b n x) ∨ Antitone (fun n => b n x)) →
    Uniform.realUniformConvergesValue b (fun _ => 0) →
    ∃ f : E → ℂ, Uniform.complexUniformConvergesValue
      (fun N x => ∑ n ∈ Finset.range (N + 1), a n x * (b n x : ℂ)) f

end Specs.SingleVariableAnalysis.Ch12.UniformDirichlet
