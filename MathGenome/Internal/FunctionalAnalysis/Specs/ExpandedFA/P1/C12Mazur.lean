import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Order.Interval.Finset.Nat

/-!
Independent statement of Mazur's lemma (`fa2:p1:c12:mazur`, paper.tex 2444–2450).
Weak convergence uses the canonical σ(E,E′), with the continuous scalar-linear
dual formed using the original norm topology. All coefficients and convex
combinations are real, including for complex E. Indices start at zero; the
error bound used in the implementation will therefore use 1/(n+1).
There is no completeness or nontriviality hypothesis.
-/

namespace ExpandedFA.P1.C12Mazur.Spec

universe u v
open Filter
open scoped Topology BigOperators

/-- Contiguous finite tail combinations converge in the original norm topology.
Coefficients outside the chosen interval are zero as well. -/
def MazurTailCombinations : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (xₙ : ℕ → E) (x : E),
      Tendsto xₙ atTop
        (@nhds E (C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E)) x) →
      ∃ (m : ℕ → ℕ) (a : ℕ → ℕ → ℝ),
        (∀ n, n ≤ m n) ∧
        (∀ n j, 0 ≤ a n j) ∧
        (∀ n j, j ∉ Finset.Icc n (m n) → a n j = 0) ∧
        (∀ n, ∑ j ∈ Finset.Icc n (m n), a n j = 1) ∧
        Tendsto (fun n => ∑ j ∈ Finset.Icc n (m n), a n j • xₙ j) atTop (𝓝 x)

end ExpandedFA.P1.C12Mazur.Spec
