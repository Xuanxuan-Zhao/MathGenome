import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigProperties
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.SinCos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
K03.07.trig_properties: identities and bounds for the constructed real series.
The upstream `sinCosSeries_eq_real` identifies these precise factorial sums
with Mathlib's canonical sine and cosine. We transport the canonical identities
and estimates through that proved identification. Mathlib's identities are
derived algebraically from exp; its polynomial bounds use the sine series
estimate and the half-angle identity. Thus this reuse need not follow the
manuscript's zero-derivative/monotonicity proof route.
-/
noncomputable section
namespace SingleVariableAnalysis

private theorem realSeriesSin_eq_sin : realSeriesSin = Real.sin :=
  funext fun x => (sinCosSeries_eq_real x).1

private theorem realSeriesCos_eq_cos : realSeriesCos = Real.cos :=
  funext fun x => (sinCosSeries_eq_real x).2

theorem realSeriesSin_neg (x : ℝ) : realSeriesSin (-x) = -realSeriesSin x := by
  simpa only [realSeriesSin_eq_sin] using Real.sin_neg x

theorem realSeriesCos_neg (x : ℝ) : realSeriesCos (-x) = realSeriesCos x := by
  simpa only [realSeriesCos_eq_cos] using Real.cos_neg x

theorem realSeriesSin_add (x y : ℝ) :
    realSeriesSin (x + y) =
      realSeriesSin x * realSeriesCos y + realSeriesCos x * realSeriesSin y := by
  simpa only [realSeriesSin_eq_sin, realSeriesCos_eq_cos] using Real.sin_add x y

theorem realSeriesCos_add (x y : ℝ) :
    realSeriesCos (x + y) =
      realSeriesCos x * realSeriesCos y - realSeriesSin x * realSeriesSin y := by
  simpa only [realSeriesSin_eq_sin, realSeriesCos_eq_cos] using Real.cos_add x y

theorem realSeriesSin_sq_add_realSeriesCos_sq (x : ℝ) :
    realSeriesSin x ^ 2 + realSeriesCos x ^ 2 = 1 := by
  simpa only [realSeriesSin_eq_sin, realSeriesCos_eq_cos] using Real.sin_sq_add_cos_sq x

theorem realSeriesSin_abs_le_one (x : ℝ) : |realSeriesSin x| ≤ 1 := by
  simpa only [realSeriesSin_eq_sin] using Real.abs_sin_le_one x

theorem realSeriesCos_abs_le_one (x : ℝ) : |realSeriesCos x| ≤ 1 := by
  simpa only [realSeriesCos_eq_cos] using Real.abs_cos_le_one x

theorem realSeriesSin_abs_le_abs (x : ℝ) : |realSeriesSin x| ≤ |x| := by
  simpa only [realSeriesSin_eq_sin] using (Real.abs_sin_le_abs (x := x))

theorem realSeriesCos_sub_one_abs_le (x : ℝ) :
    |realSeriesCos x - 1| ≤ x ^ 2 / 2 := by
  rw [realSeriesCos_eq_cos, abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

end SingleVariableAnalysis
