import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap
import Mathlib.Topology.Algebra.Order.Field

/-! Independent specification of paper.tex, d13:04:quadratic-blowup.
The scalar state is ℝ, the field has full time-state domain, and all solution
comparisons use the actual recorded open intervals. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.Ch04.QuadraticBlowup

/-- The smooth scalar field x², on all of ℝ × ℝ. -/
def quadraticODE : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => p.val.2 ^ 2
  continuous_field := (continuous_snd.comp continuous_subtype_val).pow 2

/-- Its explicit ambient representative; only its recorded interval is used. -/
def quadraticCurve (s ξ t : ℝ) : ℝ := ξ / (1 - ξ * (t - s))

/-- The exact pole-free interval containing the initial time. -/
def quadraticInterval (s ξ : ℝ) : OpenTimeInterval :=
  if 0 < ξ then
    ⟨⟨Iio (s + 1 / ξ), nonempty_Iio, ordConnected_Iio⟩, isOpen_Iio⟩
  else if ξ < 0 then
    ⟨⟨Ioi (s + 1 / ξ), nonempty_Ioi, ordConnected_Ioi⟩, isOpen_Ioi⟩
  else ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩

end D13Unified.Ch04.QuadraticBlowup

namespace Specs.D13Unified.Ch04.QuadraticBlowup
open _root_.D13Unified
open _root_.D13Unified.Ch04.QuadraticBlowup
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap

/-- Smoothness is joint in time and state; local state control uses the common
predicate, uniform in time on each sufficiently small product neighborhood. -/
def regularityExpected : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × ℝ => quadraticODE.eval z.1 z.2) ∧
  Ch03.LocalLipschitz.locallyLipschitzInStateValue quadraticODE

/-- The explicit formula solves the IVP, its interval is the actual canonical
maximal interval, and every competing IVP is precisely a restriction of it. -/
def solutionExpected : Prop :=
  ∀ s ξ : ℝ,
    classicalIVPOnValue quadraticODE (quadraticInterval s ξ) (quadraticCurve s ξ) s ξ ∧
    (maximalIntervalValue quadraticODE s ξ).carrier = (quadraticInterval s ξ).carrier ∧
    EqOn (solutionCurveValue quadraticODE s ξ) (quadraticCurve s ξ)
      (quadraticInterval s ξ).carrier ∧
    (∀ (J : OpenTimeInterval) (y : ℝ → ℝ),
      classicalIVPOnValue quadraticODE J y s ξ →
        J.carrier ⊆ (quadraticInterval s ξ).carrier ∧
        EqOn y (quadraticCurve s ξ) J.carrier)

/-- Explicit maximality and uniqueness among maximal solutions, with equality
of actual domains and values rather than equality of ambient representatives. -/
def maximalityExpected : Prop :=
  ∀ s ξ : ℝ,
    (∃ h : classicalSolutionOnValue quadraticODE (quadraticInterval s ξ) (quadraticCurve s ξ),
      maximalValue (⟨quadraticInterval s ξ, quadraticCurve s ξ, h⟩ : Solution quadraticODE)) ∧
    (∀ y : Solution quadraticODE, s ∈ y.interval.carrier → y.representative s = ξ →
      maximalValue y → y.interval.carrier = (quadraticInterval s ξ).carrier ∧
        EqOn y.representative (quadraticCurve s ξ) y.interval.carrier)

/-- Positive data blow up to +∞ on the left of the finite right endpoint;
negative data have a pole tending to -∞ on the right of the finite left endpoint.
Zero data have the whole real line as domain and the identically zero curve. -/
def endpointExpected : Prop :=
  ∀ s ξ : ℝ,
    (0 < ξ → Tendsto (quadraticCurve s ξ) (𝓝[<] (s + 1 / ξ)) atTop) ∧
    (ξ < 0 → Tendsto (quadraticCurve s ξ) (𝓝[>] (s + 1 / ξ)) atBot) ∧
    (ξ = 0 → (quadraticInterval s ξ).carrier = univ ∧ quadraticCurve s ξ = fun _ => 0)

/-- No continuous extension agreeing with this solution on its interval can
contain the pole. This in particular rules out a classical ODE extension. -/
def nonextensionExpected : Prop :=
  ∀ s ξ : ℝ, ξ ≠ 0 → ∀ (J : OpenTimeInterval) (y : ℝ → ℝ),
    ContinuousOn y J.carrier →
    EqOn y (quadraticCurve s ξ) (quadraticInterval s ξ).carrier →
    s + 1 / ξ ∉ J.carrier

end Specs.D13Unified.Ch04.QuadraticBlowup
