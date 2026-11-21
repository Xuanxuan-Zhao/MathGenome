import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.SumIntegralCounting
import MathGenome.Internal.RealAnalysis.D11.Ch05.MonotoneSeries
import MathGenome.Internal.RealAnalysis.D11.Ch05.AtomicIntegrals
import MathGenome.Internal.RealAnalysis.D11.Ch06.AbsoluteSeries

/-!
Counting-factor interchange on arbitrary measure spaces (paper.tex:2880–2896).
The series assertions specialize the accepted arbitrary-measure series
theorems. The counting formula then uses the accepted atomic-integral
identity on ℕ; it needs no product measure or sigma-finiteness of μ.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace D11.Ch08.SumIntegralCounting

theorem nonnegative_interchange :
    Specs.D11.Ch08.SumIntegralCounting.nonnegative_interchange := by
  exact D11.Ch05.MonotoneSeries.nonnegative_series

theorem scalar_interchange :
    Specs.D11.Ch08.SumIntegralCounting.scalar_interchange := by
  intro X 𝕜 _ _ _ _ μ f hfm hfin
  obtain ⟨ha, hm, hF, hs, _hpartial, _herror, hp, _hL1, hi, hsum, heq⟩ :=
    D11.Ch06.AbsoluteSeries.absolute_series_interchange μ f hfm hfin
  exact ⟨ha, hm, hF, hs, hp, hi, hsum, heq⟩

theorem nonnegative_counting_interchange :
    Specs.D11.Ch08.SumIntegralCounting.nonnegative_counting_interchange := by
  intro X _ μ f hf
  have hc (g : ℕ → ℝ≥0∞) :
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value
        (Measure.count : Measure ℕ) g = ∑' n, g n :=
    D11.Ch05.AtomicIntegrals.counting_integral g
  calc
    _ = Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ
        (fun x => ∑' n, f n x) :=
      congrArg (Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ)
        (funext fun x => hc (fun n => f n x))
    _ = ∑' n, Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ (f n) :=
      nonnegative_interchange μ f hf
    _ = _ := (hc _).symm

end D11.Ch08.SumIntegralCounting
