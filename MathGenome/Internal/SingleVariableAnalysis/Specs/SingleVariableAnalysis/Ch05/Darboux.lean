import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
Independent specifications for K03.05.darboux (paper.tex:884–892).
An open real interval is represented by an open, order-connected subset of ℝ;
this includes unbounded intervals. Differentiability is required only on that
set. `deriv` is the ordinary derivative with real increments, as identified
by the upstream derivative bridge. No continuity of `deriv f` is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch05.Darboux

open Set

/-- Both orders of the endpoint derivatives, including their values themselves. -/
def darbouxClosed : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), IsOpen I → OrdConnected I →
    DifferentiableOn ℝ f I →
    ∀ (u v : ℝ), u ∈ I → v ∈ I → u < v →
      ∀ m : ℝ, m ∈ uIcc (deriv f u) (deriv f v) →
        ∃ c ∈ Icc u v, deriv f c = m

/-- A strict intermediate value is attained strictly inside the segment. -/
def darbouxStrict : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), IsOpen I → OrdConnected I →
    DifferentiableOn ℝ f I →
    ∀ (u v : ℝ), u ∈ I → v ∈ I → u < v →
      ∀ m : ℝ,
        ((deriv f u < m ∧ m < deriv f v) ∨
          (deriv f v < m ∧ m < deriv f u)) →
        ∃ c ∈ Ioo u v, deriv f c = m

/-- On any interval where ordinary derivatives exist and never vanish,
all derivatives are positive or all are negative. Empty intervals are allowed. -/
def derivativeConstantSign : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), OrdConnected I →
    (∀ x ∈ I, DifferentiableAt ℝ f x) →
    (∀ x ∈ I, deriv f x ≠ 0) →
    (∀ x ∈ I, 0 < deriv f x) ∨ (∀ x ∈ I, deriv f x < 0)

/-- The corollary with the same open-domain hypotheses as the main theorem. -/
def derivativeConstantSignOnOpenInterval : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), IsOpen I → OrdConnected I →
    DifferentiableOn ℝ f I → (∀ x ∈ I, deriv f x ≠ 0) →
    (∀ x ∈ I, 0 < deriv f x) ∨ (∀ x ∈ I, deriv f x < 0)

end Specs.SingleVariableAnalysis.Ch05.Darboux
