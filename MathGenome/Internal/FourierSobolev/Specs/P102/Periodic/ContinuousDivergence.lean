import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent statement of Theorem 1.7, with the manuscript's circle,
probability Haar measure, and symmetric Fourier partial sums. -/

namespace P102.Periodic.Expected.ContinuousDivergence

/-- At every prescribed point, one real continuous function has unbounded
Fourier partial sums. Unboundedness is expressed by their absolute values. -/
def statement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (x : Circle T),
    ∃ f : C(Circle T, ℝ),
      ¬ BddAbove (Set.range (fun N : ℕ =>
        ‖partialSum T N (fun y => (f y : ℂ)) x‖))

end P102.Periodic.Expected.ContinuousDivergence
