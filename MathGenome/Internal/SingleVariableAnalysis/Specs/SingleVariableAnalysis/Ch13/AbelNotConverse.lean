import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums
import Mathlib.Topology.Order.OrderClosed

/-!
Independent specification of K03.13.abel_not_converse (paper.tex:1509–1513).
The coefficients are exactly (-1)^n, starting at n = 0. Ordinary sums use
inclusive ordered partial sums. The Abel-limit statement applies to every
function representing these ordinary sums on [0,1); the power-series formula
below supplies such a function. Thus it does not assume ordinary convergence
of the coefficient series or a Tauber coefficient condition.
Both canonical scalar interpretations of the example are included.
-/

namespace Specs.SingleVariableAnalysis.Ch13.AbelNotConverse

open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open scoped Topology

def realAlternatingPowerSeries : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < 1 →
    realSeriesHasSumValue (fun n => (-1 : ℝ)^n * x^n) (1 / (1 + x))

def realAlternatingAbelLimit : Prop :=
  ∀ f : ℝ → ℝ,
    (∀ x : ℝ, 0 ≤ x → x < 1 →
      realSeriesHasSumValue (fun n => (-1 : ℝ)^n * x^n) (f x)) →
    Filter.Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (1/2 : ℝ))

def realAlternatingPartialSums : Prop :=
  ∀ N : ℕ,
    realPartialSumValue (fun n => (-1 : ℝ)^n) (2*N) = 1 ∧
    realPartialSumValue (fun n => (-1 : ℝ)^n) (2*N+1) = 0

def realAlternatingNoOrdinarySum : Prop :=
  realSeriesDivergesValue (fun n => (-1 : ℝ)^n)

def realAlternatingTauberFails : Prop :=
  ¬ realSequenceConvergesValue (fun n => (n : ℝ) * (-1 : ℝ)^n) 0

def complexAlternatingPowerSeries : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < 1 →
    complexSeriesHasSumValue (fun n => (-1 : ℂ)^n * (x : ℂ)^n)
      (1 / (1 + (x : ℂ)))

def complexAlternatingAbelLimit : Prop :=
  ∀ f : ℝ → ℂ,
    (∀ x : ℝ, 0 ≤ x → x < 1 →
      complexSeriesHasSumValue (fun n => (-1 : ℂ)^n * (x : ℂ)^n) (f x)) →
    Filter.Tendsto f (𝓝[<] (1 : ℝ)) (𝓝 (1/2 : ℂ))

def complexAlternatingPartialSums : Prop :=
  ∀ N : ℕ,
    complexPartialSumValue (fun n => (-1 : ℂ)^n) (2*N) = 1 ∧
    complexPartialSumValue (fun n => (-1 : ℂ)^n) (2*N+1) = 0

def complexAlternatingNoOrdinarySum : Prop :=
  complexSeriesDivergesValue (fun n => (-1 : ℂ)^n)

def complexAlternatingTauberFails : Prop :=
  ¬ complexSequenceConvergesValue (fun n => (n : ℂ) * (-1 : ℂ)^n) 0

end Specs.SingleVariableAnalysis.Ch13.AbelNotConverse
