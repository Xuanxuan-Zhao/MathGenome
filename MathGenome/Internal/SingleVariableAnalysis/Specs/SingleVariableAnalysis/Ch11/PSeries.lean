import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.PartialSums

/-!
Independent specification for the real p-series assertion of
K03.11.geometric_p (paper.tex:1011–1020).
Lean index n represents the positive source index n+1. All bases are
therefore strictly positive, including when p ≤ 0. Powers use the source's
series-exponential/inverse-log construction. Convergence means a finite
limit of the ordered inclusive partial sums. The final canonical form
uses Real.rpow on those same positive bases.
-/

namespace Specs.SingleVariableAnalysis.Ch11.PSeries

open Specs.SingleVariableAnalysis.Ch07.RealPowers
open Specs.SingleVariableAnalysis.Ch01.SequenceLimit
open PartialSums

noncomputable section

def nonpositiveTermsNotNull : Prop :=
  ∀ p : ℝ, p ≤ 0 →
    ¬ realSequenceConvergesValue (fun n : ℕ => realPowerValue ((n : ℝ) + 1) (-p)) 0

def nonpositiveDivergence : Prop :=
  ∀ p : ℝ, p ≤ 0 →
    realSeriesDivergesValue (fun n : ℕ => realPowerValue ((n : ℝ) + 1) (-p))

def harmonicComparison : Prop :=
  ∀ p : ℝ, p ≤ 1 → ∀ n : ℕ,
    1 / ((n : ℝ) + 1) ≤ realPowerValue ((n : ℝ) + 1) (-p)

def positiveLeOneDivergence : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 →
    realSeriesDivergesValue (fun n : ℕ => realPowerValue ((n : ℝ) + 1) (-p))

def oneLtConvergence : Prop :=
  ∀ p : ℝ, 1 < p →
    realSeriesConvergesValue (fun n : ℕ => realPowerValue ((n : ℝ) + 1) (-p))

def convergenceIff : Prop :=
  ∀ p : ℝ,
    realSeriesConvergesValue (fun n : ℕ => realPowerValue ((n : ℝ) + 1) (-p)) ↔ 1 < p

def divergenceIff : Prop :=
  ∀ p : ℝ,
    realSeriesDivergesValue (fun n : ℕ => realPowerValue ((n : ℝ) + 1) (-p)) ↔ p ≤ 1

def rpowConvergenceIff : Prop :=
  ∀ p : ℝ,
    realSeriesConvergesValue (fun n : ℕ => ((n : ℝ) + 1) ^ (-p)) ↔ 1 < p

end
end Specs.SingleVariableAnalysis.Ch11.PSeries
