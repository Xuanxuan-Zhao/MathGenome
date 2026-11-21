import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Separation

/-! Unequal-parameter assertion of paper.tex, Proposition d13:10:separation.
The real solutions, within derivatives and consecutive zeros are exactly the
shared Chapter 10 objects. No boundary condition is imposed on either solution,
and no sign or nonvanishing hypothesis is imposed on `v` at `c` or `d`. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch10.Comparison
open RegularProblem Separation

def SturmComparison : Prop :=
  ∀ (P : Problem) (lam mu : ℝ) (u v : ℝ → ℝ), lam < mu →
    IsRealSolution P lam u → Nonzero P u →
    IsRealSolution P mu v → Nonzero P v →
    ∀ c d : ℝ, ConsecutiveZeros P u c d →
      ∃ x ∈ Ioo c d, v x = 0

end Specs.D13Unified.Ch10.Comparison
