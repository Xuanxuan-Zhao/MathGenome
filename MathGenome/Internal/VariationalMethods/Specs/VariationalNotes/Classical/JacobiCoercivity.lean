import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.PositiveJacobiSolution
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.SecondVariation
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.SlabPoincare

/-! The coercivity clause of `thm:v07-06-01`, paper.tex:3419–3470.
The local-minimum/Taylor clause is allocated to JacobiSufficiency.
The Sobolev space below is the existing weak-derivative graph with its full
Euclidean H¹ norm, on the one-dimensional Euclidean interval. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace VariationalNotes.Classical.JacobiCoercivity
open VariationalNotes.Sobolev

/-- The open interval in the existing one-dimensional Euclidean domain. -/
def intervalDomain (I : Interval) : Opens (Domain 1) :=
  ⟨{x | I.a < x 0 ∧ x 0 < I.b},
    (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0)).inter
      (isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const)⟩

abbrev Variation (I : Interval) := H1Zero (intervalDomain I) 1

/-- The scalar unit vector in the source's Euclidean scalar fiber. -/
def scalarUnit : State 1 := WithLp.toLp 2 (fun _ => 1)

def coefficientP {I : Interval} (L : Lagrangian 1) (u : C1Curve I 1) (t : ℝ) : ℝ :=
  secondVariationVV L (t, stateField I 1 u t, velocityField I 1 u t)
    scalarUnit scalarUnit

def coefficientB {I : Interval} (L : Lagrangian 1) (u : C1Curve I 1) (t : ℝ) : ℝ :=
  secondVariationZV L (t, stateField I 1 u t, velocityField I 1 u t)
    scalarUnit scalarUnit

def coefficientC {I : Interval} (L : Lagrangian 1) (u : C1Curve I 1) (t : ℝ) : ℝ :=
  secondVariationZZ L (t, stateField I 1 u t, velocityField I 1 u t)
    scalarUnit scalarUnit

/-- Within derivatives include the one-sided endpoint derivatives. -/
def coefficientV {I : Interval} (L : Lagrangian 1) (u : C1Curve I 1) (t : ℝ) : ℝ :=
  coefficientC L u t - derivWithin (coefficientB L u) (Icc I.a I.b) t

/-- The reduced quadratic form on actual H¹₀ classes, using their weak
value and gradient fields. Representative choices do not change the integral. -/
def reducedForm (I : Interval) (P V : ℝ → ℝ) (η : Variation I) : ℝ :=
  ∫ x, P (x 0) * ‖gradient (intervalDomain I) 1 Exponent.two η.val x‖ ^ 2 +
    V (x 0) * ‖value (intervalDomain I) 1 Exponent.two η.val x‖ ^ 2
    ∂domainMeasure (intervalDomain I)

/-- The prescribed classical value/derivative pair of an H¹₀ class. -/
def Represents {I : Interval} (η : C1Curve I 1) (h : Variation I) : Prop :=
  (value (intervalDomain I) 1 Exponent.two h.val : Domain 1 → Vector 1) =ᵐ[
      domainMeasure (intervalDomain I)] (fun x => stateField I 1 η (x 0)) ∧
  (gradient (intervalDomain I) 1 Exponent.two h.val : Domain 1 → Gradient 1 1) =ᵐ[
      domainMeasure (intervalDomain I)]
    (fun x => WithLp.toLp 2 (fun _ => velocityField I 1 η (x 0) 0))

end VariationalNotes.Classical.JacobiCoercivity

namespace Specs.VariationalNotes.Classical.JacobiCoercivity
open _root_.VariationalNotes.Classical
open _root_.VariationalNotes.Classical.JacobiCoercivity

/-- Completed partial obligation: continuity of the actual reduced form. -/
def ContinuousReducedForm : Prop :=
  ∀ (I : Interval) {P V : ℝ → ℝ},
    ContinuousOn P (Icc I.a I.b) → ContinuousOn V (Icc I.a I.b) →
      Continuous (reducedForm I P V)

/-- Completed algebraic bridge to the actual classical second variation. -/
def ClassicalCoefficientForm : Prop :=
  ∀ (I : Interval) (L : Lagrangian 1) (u η : C1Curve I 1),
    secondVariationForm L u η = ∫ t in I.a..I.b,
      coefficientC L u t * (stateField I 1 η t 0) ^ 2 +
      2 * coefficientB L u t * stateField I 1 η t 0 * velocityField I 1 η t 0 +
      coefficientP L u t * (velocityField I 1 η t 0) ^ 2

/-- Full assigned conclusion. The normalized field is quantified universally,
so no stronger nonconjugacy or existence certificate is assumed. -/
def CoerciveSecondVariation : Prop :=
  ∀ (I : Interval) (L : Lagrangian 1) (u : C1Curve I 1),
    ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b) →
    stateStationary L u → regularNearGraph L u 3 →
    (∀ t ∈ Icc I.a I.b, 0 < coefficientP L u t) →
    ∀ Y₀ : ℝ → ℝ × ℝ,
      Jacobi.IsSolution (coefficientP L u) (coefficientV L u) I.a I.b Y₀ →
      Y₀ I.a = (0, coefficientP L u I.a) →
      (∀ t ∈ Ioc I.a I.b, (Y₀ t).1 ≠ 0) →
      Continuous (reducedForm I (coefficientP L u) (coefficientV L u)) ∧
      (∀ η : C1Curve I 1, η ∈ endpointZero I 1 →
        ∃ h : Variation I, Represents η h ∧
          reducedForm I (coefficientP L u) (coefficientV L u) h =
            secondVariationForm L u η) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ η : Variation I,
        κ * ‖η‖ ^ 2 ≤ reducedForm I (coefficientP L u) (coefficientV L u) η

end Specs.VariationalNotes.Classical.JacobiCoercivity
