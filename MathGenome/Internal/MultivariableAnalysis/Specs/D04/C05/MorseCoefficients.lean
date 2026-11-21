import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry
import Mathlib.Analysis.Matrix.Normed
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! The coefficients use the proper scalar Darboux integral, totalized by zero
only when the integrand is not integrable. All uses below assert integrability. -/
noncomputable section
open Set
open scoped BigOperators Matrix.Norms.Elementwise
namespace Specs.D04.C05.MorseCoefficients
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.Symmetry.Model
namespace Model

def riemannValue (v : ℝ → ℝ) : ℝ := by
  classical
  exact if hv : Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue v 0 1 then
    Specs.SingleVariableAnalysis.Ch08.Integral.realIntegralValue v hv else 0

def morseCoefficients {n : ℕ} (f : E n → ℝ) (x : E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => riemannValue (fun t => (1-t) * hessian f (t • x) i j)
end Model

def riemannValueType := (ℝ → ℝ) → ℝ
def riemannValueValue : riemannValueType := Model.riemannValue

def morseCoefficientsType := {n : ℕ} → (E n → ℝ) → E n → Matrix (Fin n) (Fin n) ℝ
def morseCoefficientsValue : morseCoefficientsType := @Model.morseCoefficients
/-- First parameter derivative, with no differentiability in t assumed.
The compact interval and joint continuity supply uniform control. -/
def riemann_hasFDerivAtType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (U : Set X), IsOpen U →
  ∀ (f : X → ℝ → ℝ) (f' : X → ℝ → X →L[ℝ] ℝ),
    ContinuousOn (Function.uncurry f) (U ×ˢ Icc (0 : ℝ) 1) →
    ContinuousOn (Function.uncurry f') (U ×ˢ Icc (0 : ℝ) 1) →
    (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun y => f y t) (f' x t) x) →
    ∀ x ∈ U, ∃ L : X →L[ℝ] ℝ,
      HasFDerivAt (fun y => Model.riemannValue (f y)) L x ∧
      ∀ h, L h = Model.riemannValue (fun t => f' x t h)

/-- Repeated parameter differentiation for the jointly regular integrands
used here. W may be any open neighborhood of U × [0,1]. -/
def riemann_contDiffOnType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (r : ℕ) (W : Set (X × ℝ)), IsOpen W →
  ∀ (F : X × ℝ → ℝ), ContDiffOn ℝ r F W →
  ∀ (U : Set X), IsOpen U →
    (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x,t) ∈ W) →
    ContDiffOn ℝ r (fun x => Model.riemannValue (fun t => F (x,t))) U

def morseCoefficients_integrableType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → CrOn 2 U f → ∀ x : E n,
    (∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) → ∀ i j : Fin n,
      Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
        (fun t : ℝ => (1-t) * hessian f (t • x) i j) 0 1

def morseCoefficients_identityType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → CrOn 2 U f → totalDerivative f 0 = 0 → ∀ x : E n,
    (∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) →
      f x - f 0 = ∑ i : Fin n, ∑ j : Fin n, Model.morseCoefficients f x i j * x i * x j

def morseCoefficients_symmetricType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → CrOn 2 U f → ∀ x : E n,
    (∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) → (Model.morseCoefficients f x).IsSymm

def morseCoefficients_zeroType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ), Model.morseCoefficients f 0 = (1/2 : ℝ) • hessian f 0

def morseCoefficients_crOnType : Prop :=
  ∀ {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → CrOn (r+2) U f → ∀ ρ : ℝ, 0 < ρ →
    Metric.ball (0 : E n) ρ ⊆ U → ∀ i j : Fin n,
      CrOn r (Metric.ball 0 ρ) (fun x => Model.morseCoefficients f x i j)

/-- Matrices use the elementwise supremum norm, so this also expresses the
usual finite coordinate regularity. -/
def morseCoefficients_matrix_crOnType : Prop :=
  ∀ {n : ℕ} (r : ℕ) (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → CrOn (r+2) U f → ∀ ρ : ℝ, 0 < ρ →
    Metric.ball (0 : E n) ρ ⊆ U →
      CrOn r (Metric.ball 0 ρ) (Model.morseCoefficients f)

def morseCoefficients_smoothOnType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → SmoothOn U f → ∀ ρ : ℝ, 0 < ρ →
    Metric.ball (0 : E n) ρ ⊆ U →
      SmoothOn (Metric.ball 0 ρ) (Model.morseCoefficients f)

def morseCoefficients_dimension_zeroType : Prop :=
  ∀ (f : E 0 → ℝ) (x : E 0),
    f x - f 0 = ∑ i : Fin 0, ∑ j : Fin 0, Model.morseCoefficients f x i j * x i * x j

/-- Full coefficient stage for finite r ≥ 1. No Hessian nondegeneracy is
needed until the subsequent square-completion stage. -/
def morse_coefficientsType : Prop :=
  ∀ {n : ℕ} (r : ℕ), 1 ≤ r → ∀ (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → (0 : E n) ∈ U → CrOn (r+2) U f → totalDerivative f 0 = 0 →
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : E n) ρ ⊆ U ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ i j : Fin n,
        Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
          (fun t : ℝ => (1-t) * hessian f (t • x) i j) 0 1) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ,
        f x - f 0 = ∑ i : Fin n, ∑ j : Fin n, Model.morseCoefficients f x i j * x i * x j) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, (Model.morseCoefficients f x).IsSymm) ∧
      Model.morseCoefficients f 0 = (1/2 : ℝ) • hessian f 0 ∧
      CrOn r (Metric.ball 0 ρ) (Model.morseCoefficients f)

/-- Smooth data give the same coefficients and all properties on one ball. -/
def morse_coefficients_smoothType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ),
    IsOpen U → (0 : E n) ∈ U → SmoothOn U f → totalDerivative f 0 = 0 →
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : E n) ρ ⊆ U ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, ∀ i j : Fin n,
        Specs.SingleVariableAnalysis.Ch08.Integral.realIntegrableValue
          (fun t : ℝ => (1-t) * hessian f (t • x) i j) 0 1) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ,
        f x - f 0 = ∑ i : Fin n, ∑ j : Fin n, Model.morseCoefficients f x i j * x i * x j) ∧
      (∀ x ∈ Metric.closedBall (0 : E n) ρ, (Model.morseCoefficients f x).IsSymm) ∧
      Model.morseCoefficients f 0 = (1/2 : ℝ) • hessian f 0 ∧
      SmoothOn (Metric.ball 0 ρ) (Model.morseCoefficients f)

end Specs.D04.C05.MorseCoefficients
