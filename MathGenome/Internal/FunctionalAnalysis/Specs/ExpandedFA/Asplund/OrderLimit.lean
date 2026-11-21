import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.Iteration
import Mathlib.Topology.Order.MonotoneConvergence

/-! Independent statements for the primal part of
`fa2:p1:asplund-convex-iteration`, paper.tex 6829–6872.
Finiteness is expressed by real-valued functions. The only assumptions are
the accepted initial data on a real normed space; completeness and continuity
are not required. -/
namespace ExpandedFA.Asplund.OrderLimit.Spec

open Filter
open scoped Topology

def LimitType :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
    (E → ℝ) → (E → ℝ) → E → ℝ

/-- The decreasing sequence's real infimum. The theorems below verify that
it is a genuine finite common limit under the original hypotheses. -/
noncomputable def thetaValue : LimitType := fun E _ _ φ₀ ψ₀ x =>
  sInf (Set.range fun n => Iteration.Spec.phiValue E φ₀ ψ₀ n x)

/-- Every pair consists of finite convex functions, nonnegative and ordered,
both vanishing at zero. -/
def IteratesProperties : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ → ∀ n,
    Iteration.Spec.InitialDataValue E
      (Iteration.Spec.phiValue E φ₀ ψ₀ n) (Iteration.Spec.psiValue E φ₀ ψ₀ n)

def OrderChain : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ → ∀ n x,
    0 ≤ Iteration.Spec.psiValue E φ₀ ψ₀ n x ∧
    Iteration.Spec.psiValue E φ₀ ψ₀ n x ≤ Iteration.Spec.psiValue E φ₀ ψ₀ (n + 1) x ∧
    Iteration.Spec.psiValue E φ₀ ψ₀ (n + 1) x ≤
      Iteration.Spec.phiValue E φ₀ ψ₀ (n + 1) x ∧
    Iteration.Spec.phiValue E φ₀ ψ₀ (n + 1) x ≤ Iteration.Spec.phiValue E φ₀ ψ₀ n x

def MonotoneSequences : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ → ∀ x,
    Antitone (fun n => Iteration.Spec.phiValue E φ₀ ψ₀ n x) ∧
    Monotone (fun n => Iteration.Spec.psiValue E φ₀ ψ₀ n x)

/-- The one common finite convex limit, including its origin value,
nonnegativity, and bounds by every pair of iterates. -/
def CommonLimit : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ₀ ψ₀ : E → ℝ), Iteration.Spec.InitialDataValue E φ₀ ψ₀ →
    ConvexOn ℝ Set.univ (thetaValue E φ₀ ψ₀) ∧
    thetaValue E φ₀ ψ₀ 0 = 0 ∧
    (∀ x, 0 ≤ thetaValue E φ₀ ψ₀ x) ∧
    (∀ n x, Iteration.Spec.psiValue E φ₀ ψ₀ n x ≤ thetaValue E φ₀ ψ₀ x ∧
      thetaValue E φ₀ ψ₀ x ≤ Iteration.Spec.phiValue E φ₀ ψ₀ n x) ∧
    (∀ x, Tendsto (fun n => Iteration.Spec.phiValue E φ₀ ψ₀ n x)
        atTop (𝓝 (thetaValue E φ₀ ψ₀ x)) ∧
      Tendsto (fun n => Iteration.Spec.psiValue E φ₀ ψ₀ n x)
        atTop (𝓝 (thetaValue E φ₀ ψ₀ x)))

end ExpandedFA.Asplund.OrderLimit.Spec
