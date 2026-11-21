import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.CommonInterval
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Independent statement of paper.tex, d13:05:field-convergence.
`ODE` contains continuity on the specified open domain. Each approximating
field has its own local state Lipschitz constants. The canonical curves have
meaning only on their recorded maximal intervals; eventual inclusion below
asserts existence at both endpoints as well as throughout the interval.
Uniform convergence on compact subsets is tested only inside the common domain.
-/
noncomputable section
open Set Filter D13Unified
open scoped Topology

namespace Specs.D13Unified.Ch05.FieldConvergence
open Ch01.SolutionConcepts Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u

def fieldConvergenceExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (G : ℕ → ODE E),
    locallyLipschitzInStateValue F →
    (∀ j, (G j).domain = F.domain) →
    (∀ j, locallyLipschitzInStateValue (G j)) →
    (∀ K : Set (ℝ × E), IsCompact K → K ⊆ F.domain →
      TendstoUniformlyOn (fun j q => (G j).eval q.1 q.2)
        (fun q => F.eval q.1 q.2) atTop K) →
    ∀ (s : ℝ) (ξ : E) (sSeq : ℕ → ℝ) (ξSeq : ℕ → E),
    (s, ξ) ∈ F.domain →
    Tendsto (fun j => (sSeq j, ξSeq j)) atTop (𝓝 (s, ξ)) →
    ∀ a b : ℝ, a < s → s < b →
    Icc a b ⊆ (maximalIntervalValue F s ξ).carrier →
    (∀ᶠ j in atTop,
      Icc a b ⊆ (maximalIntervalValue (G j) (sSeq j) (ξSeq j)).carrier ∧
      classicalIVPOnValue (G j) (maximalIntervalValue (G j) (sSeq j) (ξSeq j))
        (solutionCurveValue (G j) (sSeq j) (ξSeq j)) (sSeq j) (ξSeq j)) ∧
    TendstoUniformlyOn (fun j t => solutionCurveValue (G j) (sSeq j) (ξSeq j) t)
      (solutionCurveValue F s ξ) atTop (Icc a b)

end Specs.D13Unified.Ch05.FieldConvergence
