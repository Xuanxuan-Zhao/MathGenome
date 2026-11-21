import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.HigherOrderReduction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Independent statements for paper.tex, d13:02:oscillator.
Ambient representatives are compared only on their actual open time interval.
The scalar predicate requires C² regularity, hence both derivatives are ordinary
local derivatives on that interval. The companion-system bridge uses exactly
the shared ODE and solution objects from Chapter 1. -/
noncomputable section
open Set

namespace D13Unified.HarmonicOscillator

/-- The second-order equation, on the entire time-state space. -/
def equation (ω : ℝ) : HigherOrder.Equation ℝ 1 where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => -(ω ^ 2 * p.val.2 0)
  continuous_field := (continuous_const.mul
    ((continuous_apply 0).comp (continuous_snd.comp continuous_subtype_val))).neg

/-- A classical scalar solution of y'' + ω²y = 0 on its recorded interval. -/
def IsOscillatorOn (ω : ℝ) (I : OpenTimeInterval) (y : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 y I.carrier ∧
    ∀ t ∈ I.carrier, HasDerivAt (deriv y) (-(ω ^ 2 * y t)) t

/-- The displayed global oscillatory formula. -/
def formula (ω s a b t : ℝ) : ℝ :=
  a * Real.cos (ω * (t - s)) + (b / ω) * Real.sin (ω * (t - s))

/-- The separate zero-frequency formula. -/
def affine (s a b t : ℝ) : ℝ := a + b * (t - s)

/-- Mechanical energy, with the normalization stated in the source. -/
def energy (ω : ℝ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  ((deriv y t) ^ 2 + ω ^ 2 * (y t) ^ 2) / 2

end D13Unified.HarmonicOscillator

namespace Specs.D13Unified.Ch02.HarmonicOscillator
open _root_.D13Unified _root_.D13Unified.HarmonicOscillator

/-- The scalar formulation is precisely the ordinary shared C¹ companion system.
The two state coordinates are position and its actual derivative. -/
def companionExpected : Prop :=
  ∀ (ω : ℝ) (I : OpenTimeInterval) (y : ℝ → ℝ),
    IsOscillatorOn ω I y ↔
      Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue
        (equation ω).toODE I (fun t => ![y t, deriv y t])

/-- Energy is constant for every solution on its whole interval, including ω=0. -/
def energyExpected : Prop :=
  ∀ (ω : ℝ) (I : OpenTimeInterval) (y : ℝ → ℝ), IsOscillatorOn ω I y →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier, energy ω y t = energy ω y s

/-- Global existence, initial conditions, uniqueness against every local solution,
and the value of the conserved energy for each positive frequency. -/
def positiveExpected : Prop :=
  ∀ (ω : ℝ), 0 < ω → ∀ (s a b : ℝ),
    (ContDiff ℝ 2 (formula ω s a b) ∧
      ∀ t, HasDerivAt (deriv (formula ω s a b))
        (-(ω ^ 2 * formula ω s a b t)) t) ∧
    formula ω s a b s = a ∧ deriv (formula ω s a b) s = b ∧
    (∀ (I : OpenTimeInterval) (y : ℝ → ℝ), s ∈ I.carrier →
      IsOscillatorOn ω I y → y s = a → deriv y s = b →
        EqOn y (formula ω s a b) I.carrier) ∧
    ∀ t, energy ω (formula ω s a b) t = (b ^ 2 + ω ^ 2 * a ^ 2) / 2

/-- The complete zero-frequency statement, with interval-wise uniqueness and its
corresponding conserved energy. -/
def zeroExpected : Prop :=
  ∀ (s a b : ℝ),
    (ContDiff ℝ 2 (affine s a b) ∧
      ∀ t, HasDerivAt (deriv (affine s a b)) 0 t) ∧
    affine s a b s = a ∧ deriv (affine s a b) s = b ∧
    (∀ (I : OpenTimeInterval) (y : ℝ → ℝ), s ∈ I.carrier →
      IsOscillatorOn 0 I y → y s = a → deriv y s = b →
        EqOn y (affine s a b) I.carrier) ∧
    ∀ t, energy 0 (affine s a b) t = b ^ 2 / 2

/-- Restriction uniqueness also holds on intervals with included endpoints,
using the shared within-derivative solution convention (including singletons). -/
def intervalUniquenessExpected : Prop :=
  (∀ (ω : ℝ), 0 < ω → ∀ (s a b : ℝ) (I : TimeInterval) (Y : ℝ → (Fin 2 → ℝ)),
    s ∈ I.carrier →
    Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue (equation ω).toODE I Y →
    Y s = ![a, b] → ∀ t ∈ I.carrier,
      Y t = ![formula ω s a b t, deriv (formula ω s a b) t]) ∧
  (∀ (s a b : ℝ) (I : TimeInterval) (Y : ℝ → (Fin 2 → ℝ)),
    s ∈ I.carrier →
    Specs.D13Unified.Ch01.SolutionConcepts.solutionOnValue (equation 0).toODE I Y →
    Y s = ![a, b] → ∀ t ∈ I.carrier, Y t = ![affine s a b t, b])

end Specs.D13Unified.Ch02.HarmonicOscillator
