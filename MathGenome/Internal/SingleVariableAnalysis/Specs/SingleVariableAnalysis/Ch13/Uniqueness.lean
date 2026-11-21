import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Differentiation

/-!
K03.13.uniqueness, paper.tex:1399–1407. Agreement means ordinary
inclusive partial sums converge to f(x) on some open real neighborhood of c.
No global agreement or prior smoothness is assumed. Complex-valued functions
have real domain and real-variable iterated derivatives. The derivative
assertion records existence as well as the coefficient value, including k=0.
Each of two expansions may have its own neighborhood.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Uniqueness
open PowerSeries

noncomputable def realCoefficientFormula : Prop :=
  ∀ (a : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ),
    (∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-c| < r →
      RealPowerSeriesHasSumValue a c x (f x)) →
    ∀ k : ℕ, iteratedDeriv k f c = (k.factorial : ℝ) * a k ∧
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f c) c

noncomputable def complexCoefficientFormula : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ),
    (∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-c| < r →
      ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)) →
    ∀ k : ℕ, iteratedDeriv k f c = (k.factorial : ℂ) * a k ∧
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k+1) f c) c

noncomputable def realCoefficientUnique : Prop :=
  ∀ (a b : ℕ → ℝ) (c : ℝ) (f : ℝ → ℝ),
    (∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-c| < r →
      RealPowerSeriesHasSumValue a c x (f x)) →
    (∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-c| < r →
      RealPowerSeriesHasSumValue b c x (f x)) →
    a = b

noncomputable def complexCoefficientUnique : Prop :=
  ∀ (a b : ℕ → ℂ) (c : ℝ) (f : ℝ → ℂ),
    (∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-c| < r →
      ComplexPowerSeriesHasSumValue a c (x : ℂ) (f x)) →
    (∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x-c| < r →
      ComplexPowerSeriesHasSumValue b c (x : ℂ) (f x)) →
    a = b

end Specs.SingleVariableAnalysis.Ch13.Uniqueness
