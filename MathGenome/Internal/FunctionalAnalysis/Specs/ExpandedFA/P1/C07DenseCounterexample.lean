import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Independent statement for paper.tex:1518–1528, fa2:p1:c07:dense-counterexample.
The shared natural coordinate n represents the manuscript positive index n+1.
The domain is the canonical c₀ with its inherited supremum norm, over either
real or complex scalars. Finite support is a property of those same coordinates.
-/

noncomputable section
open Filter
open scoped Topology
universe u
namespace ExpandedFA.P1.C07DenseCounterexample.Spec
open C01SequenceSpaces

/-- Boundedness, even convergence, on the dense finite-support subspace does
not imply a uniform operator bound or pointwise boundedness on all of c₀. -/
def Counterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    CompleteSpace (SequenceC0 𝕜) ∧
    Dense {x : SequenceC0 𝕜 | (Function.support (fun j => x.val j)).Finite} ∧
    ∃ T : ℕ → (SequenceC0 𝕜 →L[𝕜] 𝕜),
      (∀ n x, T n x = (n + 1 : 𝕜) * x.val n) ∧
      (∀ n, ‖T n‖ = (n + 1 : ℝ)) ∧
      (∀ x : SequenceC0 𝕜, (Function.support (fun j => x.val j)).Finite →
        (∀ᶠ n in atTop, T n x = 0) ∧
        (∃ C : ℝ, ∀ n, ‖T n x‖ ≤ C) ∧
        Tendsto (fun n => T n x) atTop (𝓝 0)) ∧
      (∃ x : SequenceC0 𝕜,
        (∀ j, x.val j = RCLike.ofReal ((j + 1 : ℝ) ^ (-(1 / 2 : ℝ)))) ∧
        (∀ n, T n x = RCLike.ofReal (Real.sqrt (n + 1 : ℝ))) ∧
        Tendsto (fun n => ‖T n x‖) atTop atTop ∧
        ¬ (∃ C : ℝ, ∀ n, ‖T n x‖ ≤ C)) ∧
      ¬ (∃ M : ℝ, ∀ n, ‖T n‖ ≤ M)

end ExpandedFA.P1.C07DenseCounterexample.Spec
