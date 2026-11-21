import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import Mathlib.Order.Interval.Set.OrdConnected

/-!
Independent specification for the differential-equation comparison in
K03.07.construction_bridges, paper.tex:1873–1885.

Intervals are arbitrary order-connected subsets of ℝ containing zero, including
singletons and intervals with included endpoints. Ambient functions represent
functions restricted to the interval. Competitors are continuous on the whole
interval and solve the equation at its interior points. Thus endpoint continuity
is retained without imposing a two-sided endpoint derivative. The constructed
solution also has the available within derivatives, including at endpoints.
All derivatives, including those of complex-valued functions, use real increments.
The exponential here is the shared factorial-series construction.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.OdeComparison
open Set ExpConstruction

def realExistence : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → 0 ∈ I →
    ContinuousOn realSeriesExpValue I ∧
    (∀ t ∈ interior I, HasDerivAt realSeriesExpValue (realSeriesExpValue t) t) ∧
    (∀ t ∈ I, HasDerivWithinAt realSeriesExpValue (realSeriesExpValue t) I t) ∧
    realSeriesExpValue 0 = 1

def complexExistence : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → 0 ∈ I →
    ContinuousOn (fun t : ℝ => seriesExpValue (t : ℂ)) I ∧
    (∀ t ∈ interior I, HasDerivAt (fun t : ℝ => seriesExpValue (t : ℂ))
      (seriesExpValue (t : ℂ)) t) ∧
    (∀ t ∈ I, HasDerivWithinAt (fun t : ℝ => seriesExpValue (t : ℂ))
      (seriesExpValue (t : ℂ)) I t) ∧
    seriesExpValue 0 = 1

def realUniqueness : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → 0 ∈ I →
    ∀ (y : ℝ → ℝ), ContinuousOn y I →
      (∀ t ∈ interior I, HasDerivAt y (y t) t) → y 0 = 1 →
      EqOn y realSeriesExpValue I

def complexUniqueness : Prop :=
  ∀ (I : Set ℝ), I.OrdConnected → 0 ∈ I →
    ∀ (y : ℝ → ℂ), ContinuousOn y I →
      (∀ t ∈ interior I, HasDerivAt y (y t) t) → y 0 = 1 →
      EqOn y (fun t : ℝ => seriesExpValue (t : ℂ)) I

end Specs.SingleVariableAnalysis.Ch07.OdeComparison
