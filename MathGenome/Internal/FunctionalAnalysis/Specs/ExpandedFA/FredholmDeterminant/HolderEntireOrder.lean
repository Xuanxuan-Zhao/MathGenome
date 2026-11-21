import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.HolderDeterminantBound
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The order is the extended-real limsup of the manuscript's expression.
The disk maximum is represented by the real supremum of its norm image;
for a continuous function and a nonnegative radius compactness makes it a maximum.
Finite positive Borel measures include the stated finite positive Radon measures. -/
open MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.FredholmDeterminant.HolderEntireOrder.Spec

noncomputable def diskMaximum (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' Metric.closedBall 0 r)

noncomputable def orderQuotient (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.log (Real.log (max (Real.exp 1) (diskMaximum f r))) / Real.log r

noncomputable def entireOrder (f : ℂ → ℂ) : EReal :=
  limsup (fun r : ℝ => (orderQuotient f r : EReal)) atTop

abbrev Interval := HolderDeterminantBound.Spec.Interval

def DiskMaximumIdentification : Prop :=
  ∀ (f : ℂ → ℂ), Continuous f → ∀ r : ℝ, 0 ≤ r →
    ∃ z : ℂ, ‖z‖ ≤ r ∧ diskMaximum f r = ‖f z‖ ∧
      ∀ w : ℂ, ‖w‖ ≤ r → ‖f w‖ ≤ ‖f z‖

def ZeroHolderPolynomial : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (μ : Measure (Interval a b)) [IsFiniteMeasure μ]
    (k : C(Interval a b × Interval a b, ℂ)) (M α : ℝ),
    0 < α → α ≤ 1 → HolderDeterminantBound.Spec.Bounded k M →
    (HolderDeterminantBound.Spec.HolderSecond k 0 α ∨
      HolderDeterminantBound.Spec.HolderFirst k 0 α) → ∀ z : ℂ,
    ClassicalDefinitions.Spec.FredholmDeterminantValue μ k z =
      1 + z * ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 1

def ZeroBoundConstant : Prop :=
  ∀ (a b : ℝ) (μ : Measure (Interval a b))
    (k : C(Interval a b × Interval a b, ℂ)),
    HolderDeterminantBound.Spec.Bounded k 0 → ∀ z : ℂ,
    ClassicalDefinitions.Spec.FredholmDeterminantValue μ k z = 1

def OrderBound : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (μ : Measure (Interval a b)) [IsFiniteMeasure μ]
    (k : C(Interval a b × Interval a b, ℂ)) (M H α : ℝ),
    0 < α → α ≤ 1 → HolderDeterminantBound.Spec.Bounded k M →
    (HolderDeterminantBound.Spec.HolderSecond k H α ∨
      HolderDeterminantBound.Spec.HolderFirst k H α) →
    entireOrder (ClassicalDefinitions.Spec.FredholmDeterminantValue μ k) ≤
      ((1 / (α + 1 / 2) : ℝ) : EReal)

/-- All quantitative assertions use the already fixed upstream interfaces. -/
def FullImprovedFredholmBound : Prop :=
  HolderDeterminantBound.Spec.SecondVariableBound ∧
  HolderDeterminantBound.Spec.FirstVariableBound ∧
  HolderDeterminantBound.Spec.CoefficientIdentification ∧
  HolderDeterminantBound.Spec.CoefficientBound ∧ OrderBound

end ExpandedFA.FredholmDeterminant.HolderEntireOrder.Spec
