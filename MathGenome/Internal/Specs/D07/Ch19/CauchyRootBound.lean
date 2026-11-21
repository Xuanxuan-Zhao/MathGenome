import MathGenome.Internal.Specs.D07.Ch11.EvaluationUniversal
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.Complex.Norm

/-!
Independent specification of K07.19.cauchy_root_bound,
paper.tex:5566–5579 (chapters/M07.19.tex:334–347).

For the formal complex polynomial `f`, the source's `n` is `f.natDegree`,
`a_i` is `f.coeff i`, and `a_n` is `f.leadingCoeff`. Positive natural degree
excludes the zero and constant polynomials, and ensures a nonzero leading
coefficient. Complex absolute value is the usual complex norm.

The finite supremum below is the maximum of precisely the normalized lower
coefficients, not a maximum including the leading coefficient. Its values lie
in the nonnegative reals; the conclusions use the corresponding real number.
`MaximumCharacterization` explicitly records attainment when `n ≥ 1`.
No splitting field, algebraic closedness, or root-existence premise is used.
-/

namespace Specs.D07.Ch19.CauchyRootBound

open Polynomial
open scoped NNReal

/-- The source's `M = max_{i < n} |a_i/a_n|`. -/
noncomputable def normalizedCoefficientMaximum (f : Polynomial ℂ) : ℝ≥0 :=
  (Finset.range f.natDegree).sup (fun i => ‖f.coeff i / f.leadingCoeff‖₊)

/-- This is the actual maximum of the displayed nonempty finite set. -/
def MaximumCharacterization : Prop :=
  ∀ (f : Polynomial ℂ), 0 < f.natDegree →
    IsGreatest {r : ℝ | ∃ i : ℕ, i < f.natDegree ∧
      r = ‖f.coeff i / f.leadingCoeff‖}
      (normalizedCoefficientMaximum f : ℝ)

/-- The strict bound applies to every complex root. -/
def RootBound : Prop :=
  ∀ (f : Polynomial ℂ), 0 < f.natDegree →
    ∀ z : ℂ, f.IsRoot z →
      ‖z‖ < 1 + (normalizedCoefficientMaximum f : ℝ)

/-- In the special case `M = 0`, every root is zero. -/
def ZeroMaximumRoot : Prop :=
  ∀ (f : Polynomial ℂ), 0 < f.natDegree →
    normalizedCoefficientMaximum f = 0 →
      ∀ z : ℂ, f.IsRoot z → z = 0

end Specs.D07.Ch19.CauchyRootBound
