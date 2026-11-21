import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch04.MaximalSolutionMap
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Independent specification of paper.tex, d13:05:initial-bound.
The estimate needs only a bound between the two graph values. The first
statement applies to solutions on any common interval, with any endpoint type;
the second states the same bound for the canonical Φ on its actual domains.
The scalar example is a field on all real time-state space. Its exact solution,
its identification with Φ, equality in the estimate for forward time, and the
failure of every finite uniform bound for L > 0 are retained separately.
-/
noncomputable section
open Set D13Unified

namespace Specs.D13Unified.Ch05.InitialValueBound
open Ch01.SolutionConcepts Ch03.LocalLipschitz Ch04.MaximalSolutionMap
universe u

def linearODEValue (L : ℝ) : ODE ℝ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun p => L * p.val.2
  continuous_field := continuous_const.mul (continuous_snd.comp continuous_subtype_val)

def linearCurveValue (L s ξ t : ℝ) : ℝ := ξ * Real.exp (L * (t - s))

def linearODEType : Type := ℝ → ODE ℝ

def linearCurveType : Type := ℝ → ℝ → ℝ → ℝ → ℝ

/-- No local Lipschitz hypothesis away from the given graphs is needed. -/
def initialValueBoundExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E) (I : TimeInterval)
    (x y : ℝ → E) (s : ℝ) (ξ η : E) (L : ℝ),
    ivpOnValue F I x s ξ → ivpOnValue F I y s η → 0 ≤ L →
    (∀ r ∈ I.carrier,
      ‖F.eval r (x r) - F.eval r (y r)‖ ≤ L * ‖x r - y r‖) →
    ∀ t ∈ I.carrier,
      ‖x t - y t‖ ≤ Real.exp (L * |t - s|) * ‖ξ - η‖

/-- Both maximal intervals contain the comparison interval, so no value of the
ambient totalization outside the solution domain is used. -/
def solutionValueBoundExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : ODE E), locallyLipschitzInStateValue F →
    ∀ (I : TimeInterval) (s : ℝ) (ξ η : E) (L : ℝ),
    (s, ξ) ∈ F.domain → (s, η) ∈ F.domain → s ∈ I.carrier →
    I.carrier ⊆ (maximalIntervalValue F s ξ).carrier →
    I.carrier ⊆ (maximalIntervalValue F s η).carrier → 0 ≤ L →
    (∀ r ∈ I.carrier,
      ‖F.eval r (solutionValueValue F r s ξ) -
        F.eval r (solutionValueValue F r s η)‖ ≤
          L * ‖solutionValueValue F r s ξ - solutionValueValue F r s η‖) →
    ∀ t ∈ I.carrier,
      ‖solutionValueValue F t s ξ - solutionValueValue F t s η‖ ≤
        Real.exp (L * |t - s|) * ‖ξ - η‖

/-- The example solves the shared IVP on every interval containing s,
including the whole real line. L can be any real number here. -/
def linearSolutionExpected : Prop :=
  ∀ (L : ℝ) (I : TimeInterval) (s ξ : ℝ), s ∈ I.carrier →
    ivpOnValue (linearODEValue L) I (linearCurveValue L s ξ) s ξ

def linearLipschitzExpected : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ t x y : ℝ,
    ‖(linearODEValue L).eval t x - (linearODEValue L).eval t y‖ = L * ‖x - y‖

/-- The example is global and is exactly the previously constructed Φ. -/
def linearSolutionValueExpected : Prop :=
  ∀ L s ξ : ℝ,
    (maximalIntervalValue (linearODEValue L) s ξ).carrier = univ ∧
    ∀ t : ℝ, solutionValueValue (linearODEValue L) t s ξ = linearCurveValue L s ξ t

/-- Equality for every forward time, including L = 0 and equal initial data. -/
def sharpnessExpected : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∀ s ξ η t : ℝ, s ≤ t →
    ‖solutionValueValue (linearODEValue L) t s ξ -
      solutionValueValue (linearODEValue L) t s η‖ =
        Real.exp (L * |t - s|) * ‖ξ - η‖

/-- Even for fixed distinct initial data, every finite proposed multiplier is
violated at a future time when L > 0. -/
def noUniformConstantExpected : Prop :=
  ∀ L : ℝ, 0 < L → ∀ s ξ η : ℝ, ξ ≠ η → ∀ C : ℝ,
    ∃ t : ℝ, s ≤ t ∧
      C * ‖ξ - η‖ < ‖solutionValueValue (linearODEValue L) t s ξ -
        solutionValueValue (linearODEValue L) t s η‖

end Specs.D13Unified.Ch05.InitialValueBound
