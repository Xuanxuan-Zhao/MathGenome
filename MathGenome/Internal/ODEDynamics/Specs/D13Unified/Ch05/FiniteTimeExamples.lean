import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.ScalarLinear
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.QuadraticBlowup
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Independent statements of paper.tex, Example d13:05:finite-time.
The convergence parameter is the real initial value, approaching zero from
both sides. The time interval is fixed before choosing a data neighborhood. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch05.FiniteTimeExamples

def growthODE : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => p.val.2
  continuous_field := continuous_snd.comp continuous_subtype_val

def growthCurve (ξ t : ℝ) : ℝ := ξ * Real.exp t

def wholeTime : OpenTimeInterval :=
  ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩

end D13Unified.Ch05.FiniteTimeExamples

namespace Specs.D13Unified.Ch05.FiniteTimeExamples
open _root_.D13Unified
open _root_.D13Unified.Ch05.FiniteTimeExamples
open _root_.D13Unified.Ch04.QuadraticBlowup
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap

/-- The global exponential IVP, with uniqueness on every actual open interval. -/
def growthSolutionsExpected : Prop :=
  ∀ ξ : ℝ,
    classicalIVPOnValue growthODE wholeTime (growthCurve ξ) 0 ξ ∧
    ∀ (J : OpenTimeInterval) (y : ℝ → ℝ),
      classicalIVPOnValue growthODE J y 0 ξ → EqOn y (growthCurve ξ) J.carrier

def differenceExpected : Prop :=
  ∀ ε t : ℝ, growthCurve ε t - growthCurve 0 t = ε * Real.exp t

/-- Each fixed compact interval, including times before zero. -/
def compactConvergenceExpected : Prop :=
  ∀ a b : ℝ, TendstoUniformlyOn
    (fun ε t => growthCurve ε t - growthCurve 0 t) (fun _ => 0) (𝓝 0) (Icc a b)

/-- The same family does not converge uniformly on the full forward half-line. -/
def nonUniformExpected : Prop :=
  ¬ TendstoUniformlyOn (fun ε t => growthCurve ε t - growthCurve 0 t)
    (fun _ => 0) (𝓝 0) (Ici 0)

/-- A neighborhood of zero works for each prescribed finite compact interval
containing zero. Inclusion is in the actual canonical maximal domain; the curve
also solves the endpoint-aware IVP on the whole compact interval. -/
def quadraticCommonIntervalExpected : Prop :=
  ∀ a b : ℝ, a ≤ 0 → 0 ≤ b → ∃ δ > 0, ∀ ξ : ℝ, |ξ| < δ →
    Icc a b ⊆ (maximalIntervalValue quadraticODE 0 ξ).carrier ∧
    compactSolutionOnValue quadraticODE a b (quadraticCurve 0 ξ) ∧
    quadraticCurve 0 ξ 0 = ξ

/-- Every fixed positive datum still has the finite right endpoint 1/ξ,
with blow-up there. Thus the preceding neighborhood can depend on the interval. -/
def quadraticFiniteLifespanExpected : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    (maximalIntervalValue quadraticODE 0 ξ).carrier = Iio (1 / ξ) ∧
    0 < 1 / ξ ∧
    Tendsto (solutionCurveValue quadraticODE 0 ξ) (𝓝[<] (1 / ξ)) atTop

end Specs.D13Unified.Ch05.FiniteTimeExamples
