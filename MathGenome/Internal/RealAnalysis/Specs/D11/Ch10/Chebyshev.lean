import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statement of paper.tex:3399–3406 (D11.10.chebyshev).
The norm specializes to absolute value for both real and complex scalars.
The result is stated for normed additive groups, which includes both fields.
The integral is the shared supremum of finite nonnegative simple minorants.
No finiteness, sigma-finiteness, completeness, or Lp membership is assumed.
Both sides are extended nonnegative reals, including infinite values.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch10.Chebyshev

/-- Chebyshev's inequality for every positive real exponent, including `p < 1`. -/
def chebyshev : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (f : X → E) (p α : ℝ),
    Measurable f → 0 < p → 0 < α →
    ENNReal.ofReal (α ^ p) * μ {x | α < ‖f x‖} ≤
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ
        (fun x => ENNReal.ofReal (‖f x‖ ^ p))

end Specs.D11.Ch10.Chebyshev
