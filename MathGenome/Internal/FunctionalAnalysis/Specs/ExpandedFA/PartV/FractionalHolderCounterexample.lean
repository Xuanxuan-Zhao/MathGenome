import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalHolder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The explicit real scalar counterexample in `fa2:p5:holder-repair`,
paper.tex:22152–22167. The operator is unnormalized, as in the source.
The punctured limit is two-sided. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ExpandedFA.PartV.FractionalHolderCounterexample.Spec
open ExpandedFA.PartV.FractionalHolder.Spec

def datum (s : ℝ) : ℝ := s

def amplitude (z : ℝ × ℝ) : ℝ := |z.1 - 1/2| ^ (1/4 : ℝ)

def output (t : ℝ) : ℝ := amplitudeValue (1/4) amplitude datum t

def quotient (h : ℝ) : ℝ :=
  ‖output (1/2+h) - output (1/2)‖ / |h| ^ (1/2 : ℝ)

def InputConditions : Prop :=
  HolderOnInterval (1/4) 1 datum ∧ datum 0 = 0 ∧ Continuous amplitude

def IntegralFormula : Prop := ∀ t ∈ Icc (0 : ℝ) 1,
  IntegrableOn (fun s : ℝ => (t-s) ^ (-3/4 : ℝ) * (amplitude (t,s) * datum s))
    (Ioc 0 t) ∧
  output t = (16/5 : ℝ) * t ^ (5/4 : ℝ) * |t-1/2| ^ (1/4 : ℝ)

def QuotientFormula : Prop := ∀ h : ℝ, 0 ≤ 1/2+h → h ≠ 0 →
  quotient h = (16/5 : ℝ) * (1/2+h) ^ (5/4 : ℝ) * |h| ^ (-1/4 : ℝ)

def QuotientDivergence : Prop := Tendsto quotient (𝓝[≠] (0 : ℝ)) atTop

/-- Failure even of a Hölder bound relative to the midpoint, in every
neighborhood of it (and therefore failure on the entire closed interval). -/
def LocalFailure : Prop := ¬ ∃ (C δ : ℝ), 0 < δ ∧
  ∀ t ∈ Icc (0 : ℝ) 1, |t-1/2| < δ →
    ‖output t - output (1/2)‖ ≤ C * |t-1/2| ^ (1/2 : ℝ)

def GlobalFailure : Prop := ¬ HolderOnInterval (1/2) 1 output

end ExpandedFA.PartV.FractionalHolderCounterexample.Spec
