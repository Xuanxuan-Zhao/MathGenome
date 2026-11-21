import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Independent specification of d04:04:implicit-function. Ambient extensions
represent functions on the indicated open sets. Both blocks are restrictions
of the same total derivative. All dimensions, including zero, are allowed. -/
noncomputable section
open Set
namespace Specs.D04.C04.ImplicitFunction
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

namespace Model
/-- Parameter block of the total derivative. -/
def parameterDerivative {p q : ℕ} (G : E p × E q → E q) (z : E p × E q) :
    E p →L[ℝ] E q :=
  (totalDerivative G z).comp (ContinuousLinearMap.inl ℝ (E p) (E q))

/-- Solved-variable block of the same total derivative. -/
def solvedDerivative {p q : ℕ} (G : E p × E q → E q) (z : E p × E q) :
    E q →L[ℝ] E q :=
  (totalDerivative G z).comp (ContinuousLinearMap.inr ℝ (E p) (E q))

/-- The full product-neighborhood conclusion, including uniqueness among
all functions into B solving the equation, and the derivative on the graph.
Uniqueness of ambient representatives is asserted on A. -/
def ImplicitNeighborhood {p q : ℕ} (W : Set (E p × E q))
    (G : E p × E q → E q) (a : E p) (b c : E q)
    (A : Set (E p)) (B : Set (E q)) (φ : E p → E q) : Prop :=
  IsOpen A ∧ IsOpen B ∧ a ∈ A ∧ b ∈ B ∧ A ×ˢ B ⊆ W ∧
  MapsTo φ A B ∧ φ a = b ∧
  (∀ x ∈ A, ∀ y ∈ B, G (x, y) = c ↔ y = φ x) ∧
  (∀ ψ : E p → E q, MapsTo ψ A B →
    (∀ x ∈ A, G (x, ψ x) = c) → EqOn ψ φ A) ∧
  (∀ x ∈ A, (solvedDerivative G (x, φ x)).IsInvertible ∧
    HasTotalDerivative A φ
      (-((solvedDerivative G (x, φ x)).inverse.comp (parameterDerivative G (x, φ x)))) x ∧
    totalDerivative φ x =
      -((solvedDerivative G (x, φ x)).inverse.comp (parameterDerivative G (x, φ x))))
end Model
open Model

def implicit_function_finiteType : Prop :=
  ∀ {p q : ℕ} (r : ℕ) (W : Set (E p × E q)) (G : E p × E q → E q)
    (a : E p) (b c : E q),
    1 ≤ r → IsOpen W → CrOn r W G → (a, b) ∈ W → G (a, b) = c →
    (solvedDerivative G (a, b)).IsInvertible →
    ∃ A B φ, ImplicitNeighborhood W G a b c A B φ ∧ CrOn r A φ

def implicit_function_smoothType : Prop :=
  ∀ {p q : ℕ} (W : Set (E p × E q)) (G : E p × E q → E q)
    (a : E p) (b c : E q),
    IsOpen W → SmoothOn W G → (a, b) ∈ W → G (a, b) = c →
    (solvedDerivative G (a, b)).IsInvertible →
    ∃ A B φ, ImplicitNeighborhood W G a b c A B φ ∧ SmoothOn A φ

end Specs.D04.C04.ImplicitFunction
