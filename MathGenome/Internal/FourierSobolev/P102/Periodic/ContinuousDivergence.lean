import MathGenome.Internal.FourierSobolev.P102.Periodic.DirichletOperatorNorms
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.ContinuousDivergence
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

namespace P102.Periodic

/-- Theorem 1.7: a single real continuous function has unbounded Fourier
partial sums at any prescribed point of a circle of positive period. -/
theorem exists_continuous_unbounded_partialSum (T : ℝ) [Fact (0 < T)] (x : Circle T) :
    ∃ f : C(Circle T, ℝ),
      ¬ BddAbove (Set.range (fun N : ℕ =>
        ‖partialSum T N (fun y => (f y : ℂ)) x‖)) := by
  classical
  obtain ⟨Λ, hΛ, _, hunbounded⟩ := exists_unbounded_dirichletFunctional T x
  by_contra h
  push Not at h
  have hpointwise : ∀ f : C(Circle T, ℝ), ∃ C : ℝ, ∀ N : ℕ, ‖Λ N f‖ ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := h f
    refine ⟨C, fun N => ?_⟩
    have hb := hC (Set.mem_range_self N)
    rw [← hΛ N f, Complex.norm_real] at hb
    exact hb
  obtain ⟨C, hC⟩ := banach_steinhaus hpointwise
  apply hunbounded
  exact ⟨C, by rintro _ ⟨N, rfl⟩; exact hC N⟩

end P102.Periodic
