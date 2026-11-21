import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorComplete

/-!
Independent statement of Theorem `fa2:p1:c03:neumann`, paper.tex lines 668–678.
The native endomorphism ring uses composition as multiplication and the
continuous identity map as `1`, so its zeroth power is the manuscript's identity.
All norms and convergence below use the canonical operator norm. Completeness
is the canonical `CompleteSpace` condition identified with the manuscript's
Banach condition in the upstream series interface. No nontriviality is assumed.
-/

open Filter
open scoped Topology

namespace ExpandedFA.P1.C03Neumann.Spec

universe u v

/-- The geometric series supplies a bounded two-sided inverse, its norm bound,
and the error after every partial sum through exponent N (including N = 0).
`HasSum` also asserts unconditional convergence, while the displayed `Tendsto`
explicitly records convergence of the manuscript's ordered partial sums. -/
def NeumannInversion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (T : E →L[𝕜] E), ‖T‖ < 1 →
    ∃ S : E →L[𝕜] E,
      HasSum (fun n : ℕ => T ^ n) S ∧
      S = ∑' n : ℕ, T ^ n ∧
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), T ^ n) atTop (𝓝 S) ∧
      (ContinuousLinearMap.id 𝕜 E - T).comp S = ContinuousLinearMap.id 𝕜 E ∧
      S.comp (ContinuousLinearMap.id 𝕜 E - T) = ContinuousLinearMap.id 𝕜 E ∧
      ‖S‖ ≤ 1 / (1 - ‖T‖) ∧
      (∀ N : ℕ, ‖S - ∑ n ∈ Finset.range (N + 1), T ^ n‖ ≤
        ‖T‖ ^ (N + 1) / (1 - ‖T‖)) ∧
      T ^ (0 : ℕ) = ContinuousLinearMap.id 𝕜 E

end ExpandedFA.P1.C03Neumann.Spec
