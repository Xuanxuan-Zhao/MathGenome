import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.PowerSeries
import Mathlib.Topology.Order.Basic

/-!
Independent propositions for K03.13.abel, paper.tex:1464–1480.
The hypothesis is ordinary convergence, including conditional convergence.
The interior sums have separately asserted absolute convergence and ordinary
values. `tsum` is used only with these accompanying convergence assertions.
The filters are the real approaches 1 from below and -1 from above.
The negative endpoint uses the original coefficients multiplied by (-1)^n.
-/
namespace Specs.SingleVariableAnalysis.Ch13.Abel

open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch13.PowerSeries
open scoped BigOperators Topology

noncomputable def realInterior : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S →
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      RealPowerSeriesAbsolutelyConvergesValue a 0 x ∧
      RealPowerSeriesHasSumValue a 0 x (∑' n, a n * x ^ n)

noncomputable def complexInterior : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S →
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      ComplexPowerSeriesAbsolutelyConvergesValue a 0 (x : ℂ) ∧
      ComplexPowerSeriesHasSumValue a 0 (x : ℂ) (∑' n, a n * (x : ℂ) ^ n)

noncomputable def realIdentity : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S →
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      realSeriesConvergesValue (fun n => |realPartialSumValue a n * x ^ n|) ∧
      (∑' n, a n * x ^ n) = (1 - x) * ∑' n, realPartialSumValue a n * x ^ n

noncomputable def complexIdentity : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S →
    ∀ x : ℝ, 0 ≤ x → x < 1 →
      realSeriesConvergesValue (fun n => ‖complexPartialSumValue a n * (x : ℂ) ^ n‖) ∧
      (∑' n, a n * (x : ℂ) ^ n) =
        (1 - (x : ℂ)) * ∑' n, complexPartialSumValue a n * (x : ℂ) ^ n

noncomputable def realEndpoint : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue a S →
    Filter.Tendsto (fun x : ℝ => ∑' n, a n * x ^ n) (𝓝[<] 1) (𝓝 S)

noncomputable def complexEndpoint : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue a S →
    Filter.Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[<] 1) (𝓝 S)

noncomputable def realNegativeEndpoint : Prop :=
  ∀ (a : ℕ → ℝ) (S : ℝ), realSeriesHasSumValue (fun n => (-1 : ℝ) ^ n * a n) S →
    (∀ x : ℝ, -1 < x → x ≤ 0 →
      RealPowerSeriesAbsolutelyConvergesValue a 0 x ∧
      RealPowerSeriesHasSumValue a 0 x (∑' n, a n * x ^ n)) ∧
    Filter.Tendsto (fun x : ℝ => ∑' n, a n * x ^ n) (𝓝[>] (-1)) (𝓝 S)

noncomputable def complexNegativeEndpoint : Prop :=
  ∀ (a : ℕ → ℂ) (S : ℂ), complexSeriesHasSumValue (fun n => (-1 : ℂ) ^ n * a n) S →
    (∀ x : ℝ, -1 < x → x ≤ 0 →
      ComplexPowerSeriesAbsolutelyConvergesValue a 0 (x : ℂ) ∧
      ComplexPowerSeriesHasSumValue a 0 (x : ℂ) (∑' n, a n * (x : ℂ) ^ n)) ∧
    Filter.Tendsto (fun x : ℝ => ∑' n, a n * (x : ℂ) ^ n) (𝓝[>] (-1)) (𝓝 S)

end Specs.SingleVariableAnalysis.Ch13.Abel
