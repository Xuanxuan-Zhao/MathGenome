import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.InterpolationNorm
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.ChebyshevMinimax
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! Independent specifications for the Lebesgue assertions of W53.
The index `n` means `m = n + 1` roots, so the singleton case is included.
All constants and operator norms use the common real continuous-function
interface of W52. The logarithmic constant is quantified before the interval.
-/
noncomputable section
open Polynomial
open scoped BigOperators

namespace Specs.NumAnalysis206.Approximation.ChebyshevLebesgue
open _root_.NumAnalysis206.Approximation

def standardNodesValue (n : ℕ) : Fin (n + 1) → Set.Icc (-1 : ℝ) 1 :=
  fun j => ⟨Chebyshev.nodeValue (n + 1) j,
    Real.neg_one_le_cos _, Real.cos_le_one _⟩

def affinePointValue (a b : ℝ) (hab : a < b) (t : Set.Icc (-1 : ℝ) 1) :
    Set.Icc a b :=
  ⟨(a + b) / 2 + (b - a) / 2 * (t : ℝ), by
    constructor <;> nlinarith [t.property.1, t.property.2]⟩

def affineNodesValue (a b : ℝ) (hab : a < b) (n : ℕ) : Fin (n + 1) → Set.Icc a b :=
  fun j => affinePointValue a b hab (standardNodesValue n j)

def standardNodesType := ∀ n : ℕ, Fin (n + 1) → Set.Icc (-1 : ℝ) 1
def affinePointType := ∀ (a b : ℝ), a < b → Set.Icc (-1 : ℝ) 1 → Set.Icc a b
def affineNodesType := ∀ (a b : ℝ), a < b → ∀ n : ℕ, Fin (n + 1) → Set.Icc a b

def standardNodesInjective : Prop := ∀ n : ℕ, Function.Injective (standardNodesValue n)
def affineNodesInjective : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ), Function.Injective (affineNodesValue a b hab n)

def atNodes : Prop := ∀ (n : ℕ) (i : Fin (n + 1)),
  lebesgueFunction (standardNodesValue n) (standardNodesValue n i) = 1

def singleton : Prop := lebesgueConstantValue (standardNodesValue 0) = 1

def affineCardinalValues : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (i : Fin (n + 1)) (t : Set.Icc (-1 : ℝ) 1),
    (cardinalValue Finset.univ (fun j => (affineNodesValue a b hab n j : ℝ)) i).eval
        (affinePointValue a b hab t : ℝ) =
      (cardinalValue Finset.univ (fun j => (standardNodesValue n j : ℝ)) i).eval (t : ℝ)

def affineFunctionValues : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (t : Set.Icc (-1 : ℝ) 1),
    lebesgueFunction (affineNodesValue a b hab n) (affinePointValue a b hab t) =
      lebesgueFunction (standardNodesValue n) t

def affineConstant : Prop := ∀ (a b : ℝ) (hab : a < b) (n : ℕ),
  lebesgueConstantValue (affineNodesValue a b hab n) =
    lebesgueConstantValue (standardNodesValue n)

def affineOperatorNorm : Prop := ∀ (a b : ℝ) (hab : a < b) (n : ℕ),
  ‖interpolationOperatorValue (affineNodesValue a b hab n)‖ =
    ‖interpolationOperatorValue (standardNodesValue n)‖

def affineAtNodes : Prop := ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (i : Fin (n + 1)),
  lebesgueFunction (affineNodesValue a b hab n) (affineNodesValue a b hab n i) = 1

def logarithmicBound : Prop := ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
  lebesgueConstantValue (standardNodesValue n) ≤ C * (1 + Real.log (n + 1)) ∧
  ∀ (a b : ℝ) (hab : a < b),
    lebesgueConstantValue (affineNodesValue a b hab n) ≤ C * (1 + Real.log (n + 1)) ∧
    ‖interpolationOperatorValue (affineNodesValue a b hab n)‖ ≤
      C * (1 + Real.log (n + 1))

end Specs.NumAnalysis206.Approximation.ChebyshevLebesgue
