import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.RelativeLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Basic

/-!
Independent specification of paper.tex:637–649, K03.04.derivative.
The input and the increments are real, also for complex values. A function on
an interval is represented by an ambient extension tested only on that domain.
The interior hypothesis makes the domain contain all sufficiently small real
increments. The generic normed-space formulation includes both scalar targets.
All derivative values below are finite elements of the target space.
-/

namespace Specs.SingleVariableAnalysis.Ch04.Derivative

open scoped Topology
universe u

def realIncrementQuotientType : Type (u + 1) :=
  {F : Type u} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
    (ℝ → F) → ℝ → ℝ → F

noncomputable def realIncrementQuotientValue : realIncrementQuotientType.{u} :=
  fun f a h => h⁻¹ • (f (a + h) - f a)

def hasRealIncrementDerivativeType : Type (u + 1) :=
  {F : Type u} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
    (ℝ → F) → F → ℝ → Prop

def hasRealIncrementDerivativeValue : hasRealIncrementDerivativeType.{u} :=
  fun f L a => Ch02.RelativeLimit.relativePuncturedLimitValue
    (realIncrementQuotientValue f a) Set.univ 0 L

def hasRealIncrementDerivativeWithinType : Type (u + 1) :=
  {F : Type u} → [NormedAddCommGroup F] → [NormedSpace ℝ F] →
    (ℝ → F) → F → Set ℝ → ℝ → Prop

def hasRealIncrementDerivativeWithinValue : hasRealIncrementDerivativeWithinType.{u} :=
  fun f L I a => Ch02.RelativeLimit.relativePuncturedLimitValue
    (realIncrementQuotientValue f a) {h : ℝ | a + h ∈ I} 0 L

def hasRealIncrementDerivativeIffHasDerivAt : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a : ℝ),
    hasRealIncrementDerivativeValue f L a ↔ HasDerivAt f L a

def realDerivativeEpsilonIff : Prop :=
  ∀ (f : ℝ → ℝ) (L a : ℝ), hasRealIncrementDerivativeValue f L a ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ → |(f (a + h) - f a) / h - L| < ε

def complexDerivativeEpsilonIff : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ), hasRealIncrementDerivativeValue f L a ↔
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, 0 < |h| → |h| < δ →
        ‖(f (a + h) - f a) / (h : ℂ) - L‖ < ε

def withinDerivativeEpsilonIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ),
    hasRealIncrementDerivativeWithinValue f L I a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, a + h ∈ I → 0 < |h| → |h| < δ →
          ‖realIncrementQuotientValue f a h - L‖ < ε

def withinDerivativeInteriorIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    (hasRealIncrementDerivativeWithinValue f L I a ↔ HasDerivAt f L a)

/-- The representation does not depend on values outside the stated domain. -/
def withinDerivativeCongr : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f g : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ I → Set.EqOn f g I →
    (hasRealIncrementDerivativeWithinValue f L I a ↔
      hasRealIncrementDerivativeWithinValue g L I a)

/-- Any function given only on I has an ambient representation. -/
def existsAmbientExtension : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] (I : Set ℝ) (f : I → F),
    ∃ g : ℝ → F, ∀ x : I, g x = f x

def complexIncrementDerivativeIffComponents : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ),
    hasRealIncrementDerivativeValue f L a ↔
      hasRealIncrementDerivativeValue (fun x => (f x).re) L.re a ∧
      hasRealIncrementDerivativeValue (fun x => (f x).im) L.im a

def complexHasDerivAtIffComponents : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ), HasDerivAt f L a ↔
    HasDerivAt (fun x => (f x).re) L.re a ∧
    HasDerivAt (fun x => (f x).im) L.im a

def complexDifferentiableAtIffComponents : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ), DifferentiableAt ℝ f a ↔
    DifferentiableAt ℝ (fun x => (f x).re) a ∧
    DifferentiableAt ℝ (fun x => (f x).im) a

def complexDerivEqComponents : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ), DifferentiableAt ℝ f a →
    deriv f a = Complex.ofReal (deriv (fun x => (f x).re) a) +
      Complex.ofReal (deriv (fun x => (f x).im) a) * Complex.I

def complexOfComponentsHasDerivAtIff : Prop :=
  ∀ (u v : ℝ → ℝ) (u' v' a : ℝ),
    HasDerivAt (fun x => (u x : ℂ) + (v x : ℂ) * Complex.I)
      ((u' : ℂ) + (v' : ℂ) * Complex.I) a ↔
    HasDerivAt u u' a ∧ HasDerivAt v v' a

end Specs.SingleVariableAnalysis.Ch04.Derivative
