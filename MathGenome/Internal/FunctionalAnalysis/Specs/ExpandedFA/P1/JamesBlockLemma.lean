import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesBlockObjects
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Independent statement of James's convex-block lemma, paper.tex:3559–3577.
The manuscript's index 1 is represented by index 0. A prefix through index `n`
therefore has length `n + 1`, and its tail starts at `n + 1`.
No completeness of the real normed space is assumed: its continuous dual is
complete. All sums of functionals use that dual's operator norm topology. -/

universe u
namespace ExpandedFA.P1.JamesBlockLemma.Spec
open Set

noncomputable def tailMass (β : ℕ → ℝ) (n : ℕ) : ℝ := ∑' k, β (k + n)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Prefix of the translated weighted sequence. -/
noncomputable def partialSum (β : ℕ → ℝ) (g : ℕ → E →L[ℝ] ℝ)
    (w : E →L[ℝ] ℝ) (n : ℕ) : E →L[ℝ] ℝ :=
  ∑ j ∈ Finset.range n, β j • (g j - w)

/-- Almost minimizing expression used in the convex-block construction. -/
noncomputable def approximation (β : ℕ → ℝ) (g : ℕ → E →L[ℝ] ℝ)
    (w : E →L[ℝ] ℝ) (n : ℕ) : E →L[ℝ] ℝ :=
  (∑ j ∈ Finset.range n, β j • g j) + tailMass β n • g n - w

/-- Intermediate output of the recursive construction, rather than an assumed
certificate for the main lemma. Its existence is proved from the original
hypotheses by the implementation. The error budget is used only by the analytic assembly. -/
def BlockControls (A : Set E) (θ : ℝ) (β ε : ℕ → ℝ)
    (g : ℕ → E →L[ℝ] ℝ) (α : ℕ → ℝ) : Prop :=
  (∀ n, ‖g n‖ ≤ 1) ∧ Monotone α ∧ (∀ n, θ ≤ α n ∧ α n ≤ 2) ∧
    ∀ w ∈ JamesBlockObjects.Spec.LValue g, ∀ n,
      α n * (1 - ε n) < JamesBlockObjects.Spec.NormOnValue A (approximation β g w n) ∧
      JamesBlockObjects.Spec.NormOnValue A (approximation β g w n) < α n * (1 + ε n)

/-- The displayed conclusion includes norm convergence, in addition to the
value of the sum and every strict nonempty-prefix estimate. -/
def BlockConclusion (A : Set E) (θ : ℝ) (β : ℕ → ℝ) : Prop :=
  ∃ (g : ℕ → E →L[ℝ] ℝ) (a : ℝ),
    (∀ n, ‖g n‖ ≤ 1) ∧ θ ≤ a ∧ a ≤ 2 ∧
    ∀ w ∈ JamesBlockObjects.Spec.LValue g,
      Summable (fun j => β j • (g j - w)) ∧
      JamesBlockObjects.Spec.NormOnValue A (∑' j, β j • (g j - w)) = a ∧
      ∀ n : ℕ, JamesBlockObjects.Spec.NormOnValue A
        (∑ j ∈ Finset.range (n + 1), β j • (g j - w)) <
          a * (1 - θ * tailMass β (n + 1))

/-- The finite convex hull has no closure. Balance is real balance and the
input and output sequences lie in the closed dual unit ball. -/
def JamesBlockLemma : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Set E), A.Nonempty → Balanced ℝ A →
    A ⊆ Metric.closedBall (0 : E) 1 →
    ∀ (θ : ℝ), 0 < θ → θ < 1 →
    ∀ (f : ℕ → E →L[ℝ] ℝ), (∀ n, ‖f n‖ ≤ 1) →
    (∀ h ∈ convexHull ℝ (range f), ∀ w ∈ JamesBlockObjects.Spec.LValue f,
      θ ≤ JamesBlockObjects.Spec.NormOnValue A (h - w)) →
    ∀ (β : ℕ → ℝ), (∀ n, 0 < β n) → HasSum β 1 →
      BlockConclusion A θ β

end ExpandedFA.P1.JamesBlockLemma.Spec
