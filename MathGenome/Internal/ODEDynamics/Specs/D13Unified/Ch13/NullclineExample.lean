import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Nullclines
import Mathlib.Basic.Sign.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent specification of paper.tex, d13:13:nullcline-example.
The domain is the whole plane; time intervals remain the actual intervals of
solutions. The local departure assertion also witnesses the preceding source
claim that coordinate nullclines need not be invariant. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D13Unified.Ch13.NullclineExample
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open Ch01.AutonomousParameters
open Specs.D13Unified.Ch13.Nullclines
open _root_.D13Unified.Ch06.StateDerivative

def fieldValue (a : ℝ) (p : Plane) : Plane :=
  (p.1 * (1 - p.1 - p.2), p.2 * (p.1 - a))

def FieldType := ℝ → Plane → Plane

/-- A polynomial field on the full plane, including both coordinate axes. -/
def equationValue (a : ℝ) : AutonomousODE Plane where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => fieldValue a p.val
  continuous_field :=
    ((continuous_fst.mul ((continuous_const.sub continuous_fst).sub continuous_snd)).prodMk
      (continuous_snd.mul (continuous_fst.sub continuous_const))).comp continuous_subtype_val

def EquationType := ℝ → AutonomousODE Plane

def Regularity : Prop :=
  ∀ a : ℝ, ContDiff ℝ ⊤ (autonomousEvalValue (equationValue a))

def Nullclines : Prop :=
  ∀ a : ℝ,
    nullclineXValue (equationValue a) = {p | p.1 = 0 ∨ p.2 = 1 - p.1} ∧
    nullclineYValue (equationValue a) = {p | p.2 = 0 ∨ p.1 = a}

def Equilibria : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 →
    {p : Plane | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ autonomousEvalValue (equationValue a) p = 0} =
      {(0, 0), (1, 0), (a, 1 - a)}

/-- Equality of signs includes equality and both strict signs on the dividing lines. -/
def Signs : Prop :=
  ∀ (a : ℝ) (p : Plane), 0 < p.1 → 0 < p.2 →
    SignType.sign (autonomousEvalValue (equationValue a) p).1 =
      SignType.sign (1 - p.1 - p.2) ∧
    SignType.sign (autonomousEvalValue (equationValue a) p).2 =
      SignType.sign (p.1 - a)

/-- The four Boolean pairs give the complete open sign chart, using the
same tangent quadrants and phase regions as the shared nullcline theory. -/
def PhaseRegions : Prop :=
  ∀ (a : ℝ) (p : Plane), 0 < p.1 → 0 < p.2 → ∀ sx sy : Bool,
    p ∈ phaseRegionValue (equationValue a) sx sy ↔
      (if sx then p.2 < 1 - p.1 else 1 - p.1 < p.2) ∧
      (if sy then a < p.1 else p.1 < a)

/-- Every classical solution through zero, on any actual open interval.
In particular this applies on the entire maximal interval, on both sides of zero. -/
def SolutionFormulas : Prop :=
  ∀ (a : ℝ) (I : OpenTimeInterval) (z : ℝ → Plane),
    classicalAutonomousSolutionOnValue (equationValue a) I z → 0 ∈ I.carrier →
    ∀ t ∈ I.carrier,
      (z t).1 = (z 0).1 * Real.exp (∫ s in (0 : ℝ)..t, 1 - (z s).1 - (z s).2) ∧
      (z t).2 = (z 0).2 * Real.exp (∫ s in (0 : ℝ)..t, (z s).1 - a)

/-- Positivity and either zero coordinate are preserved in both time directions.
The equivalences also rule out a positive coordinate reaching zero. -/
def CoordinateInvariance : Prop :=
  ∀ (a : ℝ) (I : OpenTimeInterval) (z : ℝ → Plane),
    classicalAutonomousSolutionOnValue (equationValue a) I z → 0 ∈ I.carrier →
    ∀ t ∈ I.carrier,
      (0 < (z t).1 ↔ 0 < (z 0).1) ∧ (0 < (z t).2 ↔ 0 < (z 0).2) ∧
      ((z t).1 = 0 ↔ (z 0).1 = 0) ∧ ((z t).2 = 0 ↔ (z 0).2 = 0)

/-- Explicit specialization to the shared canonical maximal solution.
No infinite lifespan or boundedness assertion is imposed. -/
def MaximalFormulas : Prop :=
  ∀ (a : ℝ) (p : Plane), ∀ t ∈ (flowInterval (equationValue a) p).carrier,
    let z := fun s => flow (equationValue a) s p
    ((z t).1 = p.1 * Real.exp (∫ s in (0 : ℝ)..t, 1 - (z s).1 - (z s).2)) ∧
    ((z t).2 = p.2 * Real.exp (∫ s in (0 : ℝ)..t, (z s).1 - a)) ∧
    (0 < (z t).1 ↔ 0 < p.1) ∧ (0 < (z t).2 ↔ 0 < p.2) ∧
    ((z t).1 = 0 ↔ p.1 = 0) ∧ ((z t).2 = 0 ↔ p.2 = 0)

/-- At the specified point the first velocity is zero but the derivative
of the defining equation of the sloping nullcline is strictly negative. -/
def Departure : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 →
    let p : Plane := (a / 2, 1 - a / 2)
    p ∈ nullclineXValue (equationValue a) ∧
    (autonomousEvalValue (equationValue a) p).1 = 0 ∧
    (autonomousEvalValue (equationValue a) p).2 ≠ 0 ∧
    ∀ (I : OpenTimeInterval) (z : ℝ → Plane),
      classicalAutonomousSolutionOnValue (equationValue a) I z →
      0 ∈ I.carrier → z 0 = p →
      HasDerivAt (fun t => (z t).1 + (z t).2 - 1)
        ((1 - a / 2) * (a / 2 - a)) 0 ∧
      ((1 - a / 2) * (a / 2 - a) < 0) ∧
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ∈ I.carrier ∧ z t ∉ nullclineXValue (equationValue a)

/-- A genuine trajectory from the shared maximal flow supplies the witness;
this is not merely a conditional assertion about nonexistent solutions. -/
def Noninvariance : Prop :=
  ∀ a : ℝ, 0 < a → a < 1 →
    let p : Plane := (a / 2, 1 - a / 2)
    p ∈ nullclineXValue (equationValue a) ∧
    deriv (fun t => (flow (equationValue a) t p).1 +
      (flow (equationValue a) t p).2 - 1) 0 ≠ 0 ∧
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      t ∈ (flowInterval (equationValue a) p).carrier ∧
      flow (equationValue a) t p ∉ nullclineXValue (equationValue a)

end Specs.D13Unified.Ch13.NullclineExample
