import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Abel

/-!
Independent full propositions for K03.13.tauber, paper.tex:1474–1491.
Only the original coefficient condition and the Abel limit are hypotheses.
Interior absolute convergence and ordinary power-series values are conclusions.
The approximation uses the manuscript's inclusive s_N and x_N = 1 - 1/N;
the total value at N = 0 does not affect the sequence limit.
The weaker averaged condition is allocated to TauberAveraged.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Tauber
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch13.PowerSeries
open scoped BigOperators Topology

noncomputable def realInterior : Prop :=
  ∀ a : ℕ → ℝ, realSequenceConvergesValue (fun n => (n : ℝ) * a n) 0 →
    ∀ x : ℝ, 0 < x → x < 1 →
      RealPowerSeriesAbsolutelyConvergesValue a 0 x ∧
      RealPowerSeriesHasSumValue a 0 x (∑' n, a n * x ^ n)

noncomputable def complexInterior : Prop :=
  ∀ a : ℕ → ℂ, complexSequenceConvergesValue (fun n => (n : ℂ) * a n) 0 →
    ∀ x : ℝ, 0 < x → x < 1 →
      ComplexPowerSeriesAbsolutelyConvergesValue a 0 (x : ℂ) ∧
      ComplexPowerSeriesHasSumValue a 0 (x : ℂ) (∑' n, a n * (x : ℂ) ^ n)

noncomputable def realApproximation : Prop :=
  ∀ a : ℕ → ℝ, realSequenceConvergesValue (fun n => (n : ℝ) * a n) 0 →
    realSequenceConvergesValue
      (fun N => realPartialSumValue a N - ∑' n, a n * (1 - (N : ℝ)⁻¹) ^ n) 0

noncomputable def complexApproximation : Prop :=
  ∀ a : ℕ → ℂ, complexSequenceConvergesValue (fun n => (n : ℂ) * a n) 0 →
    complexSequenceConvergesValue
      (fun N => complexPartialSumValue a N -
        ∑' n, a n * ((1 - (N : ℝ)⁻¹ : ℝ) : ℂ) ^ n) 0

noncomputable def realTauber : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ),
    realSequenceConvergesValue (fun n => (n : ℝ) * a n) 0 →
    Filter.Tendsto (fun x : ℝ => ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 S) →
    realSeriesHasSumValue a S

noncomputable def complexTauber : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ),
    complexSequenceConvergesValue (fun n => (n : ℂ) * a n) 0 →
    Filter.Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1) (𝓝 S) →
    complexSeriesHasSumValue a S

end Specs.SingleVariableAnalysis.Ch13.Tauber
