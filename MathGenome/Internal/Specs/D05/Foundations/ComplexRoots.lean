import Mathlib.Basic.Complex.Basic

/-! Independent statements for the complex-root lemma, paper.tex:392–397.
The real-root assertion is the positive-real consequence used in its proof.
No polynomial-root or algebraic-closedness hypothesis is supplied. -/

namespace D05.Specs.Foundations.ComplexRoots

/-- The positive real root required by the polar construction. -/
def positiveRealRoot : Prop :=
  ∀ (r : ℝ) (m : ℕ), 0 < r → 0 < m → ∃ s : ℝ, 0 < s ∧ s ^ m = r

/-- Zero has zero as an m-th root for every positive integer m. -/
def zeroRoot : Prop :=
  ∀ (m : ℕ), 0 < m → (0 : ℂ) ^ m = 0

/-- Every complex number has an m-th root for every positive integer m. -/
def complexRoot : Prop :=
  ∀ (z : ℂ) (m : ℕ), 0 < m → ∃ w : ℂ, w ^ m = z

end D05.Specs.Foundations.ComplexRoots
