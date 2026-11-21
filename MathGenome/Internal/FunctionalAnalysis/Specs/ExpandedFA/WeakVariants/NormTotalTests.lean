import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Independent statements for the norm-total-test clauses of
`fa2:p2:source-convergence-domain-tests`, paper.tex 7803–7831.
All duals and closures below use the original normed structures. -/
namespace ExpandedFA.WeakVariants.NormTotalTests.Spec
universe u v
open Filter
open scoped Topology
noncomputable section

/-- Bounded sequences may be tested on any norm-total subset of the linear dual. -/
def NormTotalCriterion : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (s : ℕ → X) (x : X) (S : Set (X →L[𝕜] 𝕜)),
    (∃ C : ℝ, ∀ n, ‖s n‖ ≤ C) →
    (Submodule.span 𝕜 S).topologicalClosure = ⊤ →
    (Tendsto s atTop
      (@nhds X (P1.C12DualPairSpec.DualPairTopologyValue 𝕜 X (X →L[𝕜] 𝕜)
        (topDualPairing 𝕜 X)) x) ↔
      ∀ f ∈ S, Tendsto (fun n => f (s n)) atTop (𝓝 (f x)))

/-- The coordinate tests on ℓ¹ separate points and send the bounded unit vectors
 to zero, whereas the continuous sum functional takes value one. -/
def CoordinateCounterexample : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    let E := lp (fun _ : ℕ => 𝕜) 1
    let c : ℕ → E →L[𝕜] 𝕜 := lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) 1
    let e : ℕ → E := fun n => lp.single 1 n 1
    (∀ x y : E, (∀ j, c j x = c j y) → x = y) ∧
    (∀ n, ‖e n‖ = 1) ∧
    (∀ j, Tendsto (fun n => c j (e n)) atTop (𝓝 (c j 0))) ∧
    (∀ n, lp.tsumCLM 𝕜 ℕ 𝕜 (e n) = 1) ∧
    ¬ Tendsto e atTop
      (@nhds E (P1.C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜)
        (topDualPairing 𝕜 E)) 0)

end
end ExpandedFA.WeakVariants.NormTotalTests.Spec
