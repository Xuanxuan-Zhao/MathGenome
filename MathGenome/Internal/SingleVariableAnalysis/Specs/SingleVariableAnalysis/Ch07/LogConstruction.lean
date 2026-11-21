import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Independent specification for K03.07.log_construction, paper.tex:1593–1610.
The logarithm selects a preimage of the shared real factorial-series exponential.
Only positive arguments have mathematical meaning here; no value or law at a
nonpositive argument is prescribed. Existence, uniqueness, both inverse laws,
and agreement with the canonical real logarithm are separate obligations.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.LogConstruction

open Set Filter
open scoped Topology
open ExpConstruction

def seriesLogType : Type := ℝ → ℝ

def seriesLogValue : seriesLogType := Function.invFun realSeriesExpValue

def uniquePreimage : Prop :=
  ∀ y : ℝ, 0 < y → ∃! x : ℝ, realSeriesExpValue x = y

def expLog : Prop :=
  ∀ y : ℝ, 0 < y → realSeriesExpValue (seriesLogValue y) = y

def logExp : Prop :=
  ∀ x : ℝ, seriesLogValue (realSeriesExpValue x) = x

def canonical : Prop :=
  ∀ y : ℝ, 0 < y → seriesLogValue y = Real.log y

def continuity : Prop := ContinuousOn seriesLogValue (Ioi 0)

def strictIncrease : Prop := StrictMonoOn seriesLogValue (Ioi 0)

def atOne : Prop := seriesLogValue 1 = 0

def product : Prop :=
  ∀ u v : ℝ, 0 < u → 0 < v →
    seriesLogValue (u * v) = seriesLogValue u + seriesLogValue v

def reciprocal : Prop :=
  ∀ u : ℝ, 0 < u → seriesLogValue (1 / u) = -seriesLogValue u

def limitAtPosInfinity : Prop := Tendsto seriesLogValue atTop atTop

def limitAtZeroRight : Prop := Tendsto seriesLogValue (𝓝[>] 0) atBot

end Specs.SingleVariableAnalysis.Ch07.LogConstruction
