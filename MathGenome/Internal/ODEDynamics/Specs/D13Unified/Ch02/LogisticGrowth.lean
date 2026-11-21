import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Independent statements for paper.tex, d13:02:logistic.
The scalar fields have the full time-state domain ℝ × ℝ. Actual intervals,
C¹ regularity, initial values, maximality and restriction of every competitor
are retained through the shared solution objects. Formula values outside the
actual interval are only an ambient representative (division is total in Lean).
-/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Logistic

def denominator (r K s ξ t : ℝ) : ℝ := K + ξ * (Real.exp (r * (t - s)) - 1)

def curve (r K s ξ t : ℝ) : ℝ :=
  K * ξ * Real.exp (r * (t - s)) / denominator r K s ξ t

def pole (r K s ξ : ℝ) : ℝ := s + r⁻¹ * Real.log (1 - K / ξ)

/-- The connected pole-free interval containing the initial time. -/
def domain (r K s ξ : ℝ) : Set ℝ :=
  if ξ < 0 then Iio (pole r K s ξ)
  else if K < ξ then Ioi (pole r K s ξ) else univ

def field (r K : ℝ) : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => r * p.val.2 * (1 - p.val.2 / K)
  continuous_field := ((continuous_const.mul (continuous_snd.comp continuous_subtype_val)).mul
    (continuous_const.sub ((continuous_snd.comp continuous_subtype_val).div_const K)))

def exponential (r s ξ t : ℝ) : ℝ := ξ * Real.exp (r * (t - s))

def exponentialField (r : ℝ) : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => r * p.val.2
  continuous_field := continuous_const.mul (continuous_snd.comp continuous_subtype_val)

/-- Full maximal-IVP assertion for a specified formula and time domain.
Equality of arbitrary representatives is required only on their actual domains. -/
def MaximalFormula (F : ODE ℝ) (D : Set ℝ) (g : ℝ → ℝ) (s ξ : ℝ) : Prop :=
  ∃ (I : OpenTimeInterval)
    (hx : Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue F I g),
    I.carrier = D ∧ s ∈ I.carrier ∧ g s = ξ ∧
    Specs.D13Unified.Ch01.SolutionConcepts.maximalValue (⟨I, g, hx⟩ : Solution F) ∧
    (∀ (J : OpenTimeInterval) (y : ℝ → ℝ),
      Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue F J y s ξ →
      J.carrier ⊆ D ∧ EqOn g y J.carrier
    ) ∧
    ∀ y : Solution F, s ∈ y.interval.carrier → y.representative s = ξ →
      Specs.D13Unified.Ch01.SolutionConcepts.maximalValue y →
      y.interval.carrier = D ∧ EqOn y.representative g y.interval.carrier

end D13Unified.Logistic

namespace Specs.D13Unified.Ch02.LogisticGrowth
open _root_.D13Unified.Logistic

/-- All real initial values, including both equilibria and both finite-pole cases. -/
def logisticSolutionExpected : Prop :=
  ∀ (r K : ℝ), 0 < r → 0 < K → ∀ s ξ : ℝ,
    MaximalFormula (field r K) (domain r K s ξ) (curve r K s ξ) s ξ

/-- Equilibria and the full two-sided asymptotics of the intermediate branch. -/
def logisticDynamicsExpected : Prop :=
  ∀ (r K : ℝ), 0 < r → 0 < K → ∀ s : ℝ,
    (domain r K s 0 = univ ∧ ∀ t, curve r K s 0 t = 0) ∧
    (domain r K s K = univ ∧ ∀ t, curve r K s K t = K) ∧
    ∀ ξ : ℝ, 0 < ξ → ξ < K →
      domain r K s ξ = univ ∧ (∀ t, 0 < denominator r K s ξ t) ∧
      StrictMono (curve r K s ξ) ∧
      Tendsto (curve r K s ξ) atBot (𝓝 0) ∧
      Tendsto (curve r K s ξ) atTop (𝓝 K)

/-- The finite endpoint is a simple denominator zero, with a nonzero numerator.
The norm diverges even along the full punctured neighborhood; in particular
it diverges when approached from within the actual maximal interval. -/
def logisticPolesExpected : Prop :=
  ∀ (r K : ℝ), 0 < r → 0 < K → ∀ s ξ : ℝ, ξ < 0 ∨ K < ξ →
    denominator r K s ξ (pole r K s ξ) = 0 ∧
    HasDerivAt (denominator r K s ξ)
      (ξ * Real.exp (r * (pole r K s ξ - s)) * r) (pole r K s ξ) ∧
    ξ * Real.exp (r * (pole r K s ξ - s)) * r ≠ 0 ∧
    K * ξ * Real.exp (r * (pole r K s ξ - s)) ≠ 0 ∧
    Tendsto (fun t => ‖curve r K s ξ t‖) (𝓝[≠] (pole r K s ξ)) atTop

/-- The unrestricted linear model is global for every real rate and datum. -/
def exponentialGrowthExpected : Prop :=
  ∀ r s ξ : ℝ,
    MaximalFormula (exponentialField r) univ (exponential r s ξ) s ξ

end Specs.D13Unified.Ch02.LogisticGrowth
