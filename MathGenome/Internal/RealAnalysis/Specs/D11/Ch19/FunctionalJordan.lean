import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CzeroBanachDensity
import Mathlib.Analysis.Normed.Operator.Basic

/-! Independent statement of paper.tex:5574–5585. The order conditions below
are pointwise inequalities on the canonical native C₀ space. -/
namespace Specs.D11.Ch19.FunctionalJordan
universe u

/-- Type of the supremum formula, with no additional domain assumptions. -/
def positiveSupType :=
  ∀ (X : Type u) [TopologicalSpace X],
    (ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ) → ZeroAtInftyContinuousMap X ℝ → ℝ

/-- On nonnegative f this is exactly sup {I(g) : 0 ≤ g ≤ f}. -/
noncomputable def positiveSupValue : positiveSupType.{u} := fun X _ I f =>
  sSup {r : ℝ | ∃ g : ZeroAtInftyContinuousMap X ℝ,
    (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ f x) ∧ I g = r}

/-- The prescribed positive-cone formula extends to a bounded positive real-linear
functional P; its difference with I is bounded positive and gives I = P - (P-I).
The norm bound also records finiteness of the extension. No nonemptiness or
countability hypothesis is imposed. -/
def functional_jordan : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (I : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ),
    ∃ P : ZeroAtInftyContinuousMap X ℝ →L[ℝ] ℝ,
      (∀ f, (∀ x, 0 ≤ f x) → P f = positiveSupValue X I f) ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ P f) ∧
      (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ (P - I) f) ∧
      I = P - (P - I) ∧ ‖P‖ ≤ ‖I‖

end Specs.D11.Ch19.FunctionalJordan
