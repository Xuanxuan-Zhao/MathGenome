import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.QuadraticBlowup
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.LinearGrowth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Independent statements for paper.tex, Example d13:04:local-not-global.
The scalar fields have full time-state domain. Globality refers to maximal
solutions; arbitrary solutions are restrictions of a global IVP solution. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal

namespace D13Unified.Ch04.LocalVersusGlobalExamples

/-- The bounded smooth field sin(x²) on the whole time-state plane. -/
def sineSquareODE : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => Real.sin (p.val.2 ^ 2)
  continuous_field := Real.continuous_sin.comp
    ((continuous_snd.comp continuous_subtype_val).pow 2)

end D13Unified.Ch04.LocalVersusGlobalExamples

namespace Specs.D13Unified.Ch04.LocalVersusGlobalExamples
open _root_.D13Unified
open _root_.D13Unified.Ch04.LocalVersusGlobalExamples
open _root_.D13Unified.Ch04.QuadraticBlowup
open Ch01.SolutionConcepts Ch03.LocalLipschitz

/-- The shared quadratic example is locally Lipschitz, but every positive datum
has a finite right pole, and every maximal solution through that datum has
exactly this domain and blows up there. -/
def quadraticExpected : Prop :=
  locallyLipschitzInStateValue quadraticODE ∧
  ∀ s ξ : ℝ, 0 < ξ →
    classicalIVPOnValue quadraticODE (quadraticInterval s ξ) (quadraticCurve s ξ) s ξ ∧
    (quadraticInterval s ξ).carrier = Iio (s + 1 / ξ) ∧
    Tendsto (quadraticCurve s ξ) (𝓝[<] (s + 1 / ξ)) atTop ∧
    (∀ y : Solution quadraticODE, s ∈ y.interval.carrier → y.representative s = ξ →
      maximalValue y → y.interval.carrier = Iio (s + 1 / ξ) ∧
        Tendsto y.representative (𝓝[<] (s + 1 / ξ)) atTop)

def sineRegularityExpected : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × ℝ => sineSquareODE.eval z.1 z.2) ∧
  locallyLipschitzInStateValue sineSquareODE

def sineBoundedExpected : Prop := ∀ x : ℝ, |Real.sin (x ^ 2)| ≤ 1

def sineDerivativeExpected : Prop :=
  ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.sin (y ^ 2))
    (2 * x * Real.cos (x ^ 2)) x

def sineDerivativeUnboundedExpected : Prop :=
  ∀ M : ℝ, ∃ x : ℝ, M < |deriv (fun y : ℝ => Real.sin (y ^ 2)) x|

def sineNotGloballyLipschitzExpected : Prop :=
  ¬ ∃ L : ℝ≥0, LipschitzWith L (fun x : ℝ => Real.sin (x ^ 2))

/-- All maximal solutions are global, and every IVP has a global solution
extending every competing solution on its actual interval. -/
def sineGlobalExpected : Prop :=
  (∀ x : Solution sineSquareODE, maximalValue x → globalValue x) ∧
  ∀ s ξ : ℝ, ∃ x : Solution sineSquareODE,
    s ∈ x.interval.carrier ∧ x.representative s = ξ ∧ globalValue x ∧
    ∀ (J : OpenTimeInterval) (y : ℝ → ℝ),
      classicalIVPOnValue sineSquareODE J y s ξ →
        J.carrier ⊆ x.interval.carrier ∧ EqOn x.representative y J.carrier

end Specs.D13Unified.Ch04.LocalVersusGlobalExamples
