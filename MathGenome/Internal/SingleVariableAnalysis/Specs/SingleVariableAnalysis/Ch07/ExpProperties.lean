import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ExpConstruction
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Independent specification for K03.07.exp_properties, paper.tex:1578–1593.
The exponential here is the shared real factorial-series sum, identified
upstream with the real restriction of the complex series. The bijection is
onto the open positive half-line; the limits use the two distinct directions.
-/

noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.ExpProperties

open Filter Set
open scoped Topology
open ExpConstruction

def positivity : Prop := ∀ x : ℝ, 0 < realSeriesExpValue x

def derivative : Prop :=
  ∀ x : ℝ, HasDerivAt realSeriesExpValue (realSeriesExpValue x) x

def strictIncrease : Prop := StrictMono realSeriesExpValue

def positiveBijection : Prop := BijOn realSeriesExpValue univ (Ioi 0)

def limitAtNegInfinity : Prop := Tendsto realSeriesExpValue atBot (𝓝 0)

def limitAtPosInfinity : Prop := Tendsto realSeriesExpValue atTop atTop

def linearLowerBound : Prop :=
  ∀ x : ℝ, 0 ≤ x → 1 + x ≤ realSeriesExpValue x

end Specs.SingleVariableAnalysis.Ch07.ExpProperties
