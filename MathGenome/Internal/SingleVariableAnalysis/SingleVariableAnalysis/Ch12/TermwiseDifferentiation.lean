import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch12.Differentiation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.LinearRules
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.PartialSums
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.TermwiseDifferentiation

/-!
K03.12.termwise_differentiation. Apply uniform convergence of derivatives to
S_N(x) = u₀(x) + ⋯ + u_N(x). Finite linearity identifies S_N' with the
corresponding partial sum of derivatives. Base-point convergence is precisely
ordinary series convergence. All limits concern ordered partial sums, including
conditionally convergent series. Differentiation remains over ℝ for ℂ targets.
-/

namespace SingleVariableAnalysis

open Set
open scoped BigOperators

theorem real_termwise_differentiation :
    Specs.SingleVariableAnalysis.Ch12.TermwiseDifferentiation.realTermwiseDifferentiation := by
  intro u g a b x₀ hab hx₀ hc hd hbase hg
  let S : ℕ → ℝ → ℝ := fun N x => realPartialSum (fun n => u n x) N
  have hSc : ∀ N, ContinuousOn (S N) (Icc a b) := by
    intro N
    exact continuousOn_finsetSum _ (fun n hn => hc n)
  have hSd : ∀ N, ∀ x ∈ Ioo a b, DifferentiableAt ℝ (S N) x := by
    intro N x hx
    exact (HasDerivAt.fun_sum (fun n (_ : n ∈ Finset.range (N + 1)) =>
      (hd n x hx).hasDerivAt)).differentiableAt
  have hSeq : ∀ N, ∀ x ∈ Ioo a b,
      deriv (S N) x = realPartialSum (fun n => deriv (u n) x) N := by
    intro N x hx
    simpa only [S, realPartialSum, one_mul] using
      (deriv_linear_combination (Finset.range (N + 1)) u (fun _ => (1 : ℝ)) x
        (fun n hn => hd n x hx))
  have hSg : RealUniformConverges
      (fun N (x : Ioo a b) => deriv (S N) x) (fun x => g x) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hg ε hε
    refine ⟨N, ?_⟩
    intro n hn x
    change |deriv (S n) x - g x| < ε
    rw [hSeq n x x.property]
    exact hN n hn x
  obtain ⟨f, hf, hfc, hfd⟩ := real_uniform_convergence_of_derivatives
    S g a b x₀ hab hx₀ hSc hSd hbase hSg
  refine ⟨f, hf, hfc, ?_, ?_⟩
  · intro x hx ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    exact ⟨N, fun n hn => hN n hn ⟨x, hx⟩⟩
  · intro x hx
    refine ⟨hfd x hx, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := hg ε hε
    exact ⟨N, fun n hn => hN n hn ⟨x, hx⟩⟩

theorem complex_termwise_differentiation :
    Specs.SingleVariableAnalysis.Ch12.TermwiseDifferentiation.complexTermwiseDifferentiation := by
  intro u g a b x₀ hab hx₀ hc hd hbase hg
  let S : ℕ → ℝ → ℂ := fun N x => complexPartialSum (fun n => u n x) N
  have hSc : ∀ N, ContinuousOn (S N) (Icc a b) := by
    intro N
    exact continuousOn_finsetSum _ (fun n hn => hc n)
  have hSd : ∀ N, ∀ x ∈ Ioo a b, DifferentiableAt ℝ (S N) x := by
    intro N x hx
    exact (HasDerivAt.fun_sum (fun n (_ : n ∈ Finset.range (N + 1)) =>
      (hd n x hx).hasDerivAt)).differentiableAt
  have hSeq : ∀ N, ∀ x ∈ Ioo a b,
      deriv (S N) x = complexPartialSum (fun n => deriv (u n) x) N := by
    intro N x hx
    simpa only [S, complexPartialSum, one_mul] using
      (deriv_linear_combination (Finset.range (N + 1)) u (fun _ => (1 : ℂ)) x
        (fun n hn => hd n x hx))
  have hSg : ComplexUniformConverges
      (fun N (x : Ioo a b) => deriv (S N) x) (fun x => g x) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hg ε hε
    refine ⟨N, ?_⟩
    intro n hn x
    change ‖deriv (S n) x - g x‖ < ε
    rw [hSeq n x x.property]
    exact hN n hn x
  obtain ⟨f, hf, hfc, hfd⟩ := complex_uniform_convergence_of_derivatives
    S g a b x₀ hab hx₀ hSc hSd hbase hSg
  refine ⟨f, hf, hfc, ?_, ?_⟩
  · intro x hx ε hε
    obtain ⟨N, hN⟩ := hf ε hε
    exact ⟨N, fun n hn => hN n hn ⟨x, hx⟩⟩
  · intro x hx
    refine ⟨hfd x hx, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := hg ε hε
    exact ⟨N, fun n hn => hN n hn ⟨x, hx⟩⟩

end SingleVariableAnalysis
