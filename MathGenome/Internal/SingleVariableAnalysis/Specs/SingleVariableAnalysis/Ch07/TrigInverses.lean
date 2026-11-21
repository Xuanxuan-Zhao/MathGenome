import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.PiPeriod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
K03.07.trig_inverses, paper.tex:1720–1747. Ambient representatives of the
three principal inverses are restricted to the source domains below. Their
values outside [-1,1] carry no inverse or derivative assertion. The branch
identities use the upstream factorial series and the upstream analytic π.
`HasDerivWithinAt` at ±1 tests precisely the available side of [-1,1];
negating its existence excludes every finite one-sided derivative.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch07.TrigInverses
open Set Filter
open scoped Topology
open Ch07.SinCos Ch07.PiPeriod

def principalArcsinType : Type := ℝ → ℝ
def principalArcsinValue : principalArcsinType := Real.arcsin
def principalArccosType : Type := ℝ → ℝ
def principalArccosValue : principalArccosType := Real.arccos
def principalArctanType : Type := ℝ → ℝ
def principalArctanValue : principalArctanType := Real.arctan

def sineBranch : Prop :=
  StrictMonoOn realSeriesSinValue (Icc (-(analyticPiValue / 2)) (analyticPiValue / 2)) ∧
  BijOn realSeriesSinValue (Icc (-(analyticPiValue / 2)) (analyticPiValue / 2)) (Icc (-1) 1)

def cosineBranch : Prop :=
  StrictAntiOn realSeriesCosValue (Icc 0 analyticPiValue) ∧
  BijOn realSeriesCosValue (Icc 0 analyticPiValue) (Icc (-1) 1)

def tangentBranch : Prop :=
  (∀ x ∈ Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2), 0 < realSeriesCosValue x) ∧
  ContinuousOn (fun x => realSeriesSinValue x / realSeriesCosValue x)
    (Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2)) ∧
  StrictMonoOn (fun x => realSeriesSinValue x / realSeriesCosValue x)
    (Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2)) ∧
  BijOn (fun x => realSeriesSinValue x / realSeriesCosValue x)
    (Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2)) univ

def tangentEndpointLimits : Prop :=
  Tendsto (fun x => realSeriesSinValue x / realSeriesCosValue x)
    (𝓝[>] (-(analyticPiValue / 2))) atBot ∧
  Tendsto (fun x => realSeriesSinValue x / realSeriesCosValue x)
    (𝓝[<] (analyticPiValue / 2)) atTop

def tangentDerivative : Prop :=
  ∀ x ∈ Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2),
    HasDerivAt (fun x => realSeriesSinValue x / realSeriesCosValue x)
      (1 / realSeriesCosValue x ^ 2) x ∧ 0 < 1 / realSeriesCosValue x ^ 2

def arcsinInverse : Prop :=
  MapsTo principalArcsinValue (Icc (-1) 1) (Icc (-(analyticPiValue / 2)) (analyticPiValue / 2)) ∧
  (∀ x ∈ Icc (-1 : ℝ) 1, realSeriesSinValue (principalArcsinValue x) = x) ∧
  (∀ y ∈ Icc (-(analyticPiValue / 2)) (analyticPiValue / 2),
    principalArcsinValue (realSeriesSinValue y) = y)

def arccosInverse : Prop :=
  MapsTo principalArccosValue (Icc (-1) 1) (Icc 0 analyticPiValue) ∧
  (∀ x ∈ Icc (-1 : ℝ) 1, realSeriesCosValue (principalArccosValue x) = x) ∧
  (∀ y ∈ Icc 0 analyticPiValue, principalArccosValue (realSeriesCosValue y) = y)

def arctanInverse : Prop :=
  (∀ x : ℝ, principalArctanValue x ∈ Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2)) ∧
  (∀ x : ℝ, realSeriesSinValue (principalArctanValue x) /
    realSeriesCosValue (principalArctanValue x) = x) ∧
  (∀ y ∈ Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2),
    principalArctanValue (realSeriesSinValue y / realSeriesCosValue y) = y)

/-- These characterize the chosen branches without asserting global uniqueness. -/
def branchUniqueness : Prop :=
  (∀ x ∈ Icc (-1 : ℝ) 1, ∃! y : ℝ,
    y ∈ Icc (-(analyticPiValue / 2)) (analyticPiValue / 2) ∧ realSeriesSinValue y = x) ∧
  (∀ x ∈ Icc (-1 : ℝ) 1, ∃! y : ℝ,
    y ∈ Icc 0 analyticPiValue ∧ realSeriesCosValue y = x) ∧
  (∀ x : ℝ, ∃! y : ℝ,
    y ∈ Ioo (-(analyticPiValue / 2)) (analyticPiValue / 2) ∧
      realSeriesSinValue y / realSeriesCosValue y = x)

def inverseContinuity : Prop :=
  ContinuousOn principalArcsinValue (Icc (-1) 1) ∧
  ContinuousOn principalArccosValue (Icc (-1) 1) ∧ Continuous principalArctanValue

def inverseMonotonicity : Prop :=
  StrictMonoOn principalArcsinValue (Icc (-1) 1) ∧
  StrictAntiOn principalArccosValue (Icc (-1) 1) ∧ StrictMono principalArctanValue

def endpointValues : Prop :=
  principalArcsinValue (-1) = -(analyticPiValue / 2) ∧
  principalArcsinValue 1 = analyticPiValue / 2 ∧
  principalArccosValue (-1) = analyticPiValue ∧ principalArccosValue 1 = 0

def inverseDerivatives : Prop :=
  (∀ x : ℝ, |x| < 1 → HasDerivAt principalArcsinValue (1 / Real.sqrt (1 - x ^ 2)) x) ∧
  (∀ x : ℝ, |x| < 1 → HasDerivAt principalArccosValue (-(1 / Real.sqrt (1 - x ^ 2))) x) ∧
  (∀ x : ℝ, HasDerivAt principalArctanValue (1 / (1 + x ^ 2)) x)

def noFiniteEndpointDerivatives : Prop :=
  (¬ ∃ L : ℝ, HasDerivWithinAt principalArcsinValue L (Icc (-1) 1) (-1)) ∧
  (¬ ∃ L : ℝ, HasDerivWithinAt principalArcsinValue L (Icc (-1) 1) 1) ∧
  (¬ ∃ L : ℝ, HasDerivWithinAt principalArccosValue L (Icc (-1) 1) (-1)) ∧
  (¬ ∃ L : ℝ, HasDerivWithinAt principalArccosValue L (Icc (-1) 1) 1)

end Specs.SingleVariableAnalysis.Ch07.TrigInverses
