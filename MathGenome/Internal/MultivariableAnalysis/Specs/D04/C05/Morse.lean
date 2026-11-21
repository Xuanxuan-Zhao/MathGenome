import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.MorseCoefficients
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.SmoothSquareCompletion
import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-! Independent statements of the bounded Morse lemma, d04:05:morse.
The inertia indices are the invariant maximal dimensions of positive and
negative definite subspaces of the actual Hessian quadratic form. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Specs.D04.C05.Morse
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.Symmetry.Model

/-- Positive coordinates occur first; Fin is zero based. -/
def standardQuadratic {n : ℕ} (p : ℕ) (y : E n) : ℝ :=
  (∑ i : Fin n, if i.val < p then (y i)^2 else 0) -
    ∑ i : Fin n, if p ≤ i.val then (y i)^2 else 0

/-- Both maps are ambient representatives of mutually inverse maps on open
neighborhoods. Regularity is required on precisely those neighborhoods. -/
def NormalForm {n : ℕ} (r : ℕ∞ω) (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (p : ℕ) : Prop :=
  ∃ (X Y : Set (E n)) (χ ψ : E n → E n),
    IsOpen X ∧ IsOpen Y ∧ a ∈ X ∧ (0 : E n) ∈ Y ∧ X ⊆ U ∧
    BijOn χ X Y ∧ MapsTo ψ Y X ∧ LeftInvOn ψ χ X ∧ RightInvOn ψ χ Y ∧
    χ a = 0 ∧ ψ 0 = a ∧ ContDiffOn ℝ r χ X ∧ ContDiffOn ℝ r ψ Y ∧
    ∀ y ∈ Y, f (ψ y) = f a + standardQuadratic p y

def morse_finiteType : Prop :=
  ∀ {n : ℕ} (r : ℕ), 1 ≤ r → ∀ (U : Set (E n)) (f : E n → ℝ)
    (a : E n) (p q : ℕ), IsOpen U → a ∈ U → CrOn (r+2) U f →
    totalDerivative f a = 0 → (hessian f a).IsSymm → (hessian f a).det ≠ 0 →
    sigPos (hessian f a).toQuadraticForm' = p →
    sigNeg (hessian f a).toQuadraticForm' = q → p + q = n →
    NormalForm r U f a p

def morse_smoothType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n) (p q : ℕ),
    IsOpen U → a ∈ U → SmoothOn U f → totalDerivative f a = 0 →
    (hessian f a).IsSymm → (hessian f a).det ≠ 0 →
    sigPos (hessian f a).toQuadraticForm' = p →
    sigNeg (hessian f a).toQuadraticForm' = q → p + q = n →
    NormalForm ∞ U f a p

/-- A proof-stage interface, not an additional hypothesis in the Morse lemma.
It applies after a constant diagonalization and also covers dimension zero. -/
def diagonalCoefficientNormalFormType : Prop :=
  ∀ (n : ℕ) (r : ℕ∞), 1 ≤ r → ∀ (U : Set (E n))
    (A : E n → Matrix (Fin n) (Fin n) ℝ) (d₀ : Fin n → ℝ)
    (f : E n → ℝ), IsOpen U → (0 : E n) ∈ U →
    (∀ i j, ContDiffOn ℝ r (fun x => A x i j) U) →
    (∀ x ∈ U, ∀ i j, A x i j = A x j i) →
    A 0 = Matrix.diagonal d₀ → (∀ i, d₀ i ≠ 0) →
    (∀ x ∈ U, f x - f 0 =
      Specs.D04.C05.SmoothSquareCompletion.quadratic (A x) (fun i => x i)) →
    ∃ (X Y : Set (E n)) (χ ψ : E n → E n),
      IsOpen X ∧ IsOpen Y ∧ (0 : E n) ∈ X ∧ (0 : E n) ∈ Y ∧ X ⊆ U ∧
      BijOn χ X Y ∧ MapsTo ψ Y X ∧ LeftInvOn ψ χ X ∧ RightInvOn ψ χ Y ∧
      χ 0 = 0 ∧ ψ 0 = 0 ∧ ContDiffOn ℝ r χ X ∧ ContDiffOn ℝ r ψ Y ∧
      ∀ y ∈ Y, f (ψ y) = f 0 + ∑ i, Real.sign (d₀ i) * (y i)^2

end Specs.D04.C05.Morse
