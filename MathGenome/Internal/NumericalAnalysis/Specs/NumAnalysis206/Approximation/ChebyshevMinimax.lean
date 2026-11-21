import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

/-! Independent specifications for the minimax and affine transport parts of W53.
The inverse natural power `((2 : ℝ) ^ (m - 1))⁻¹` represents `2^(1-m)` for m ≥ 1.
The norm is the actual supremum norm of the continuous polynomial on the closed interval.
The other assertions of W53 are allocated to separate Lebesgue and convergence goals. -/

noncomputable section
open Polynomial
namespace Specs.NumAnalysis206.Approximation.Chebyshev

def tValue (m : ℕ) : ℝ[X] := Polynomial.Chebyshev.T ℝ (m : ℤ)
def nodeValue (m j : ℕ) : ℝ := Real.cos (((j : ℝ) + 1 / 2) * Real.pi / m)
def normValue (a b : ℝ) (p : ℝ[X]) : ℝ :=
  ‖(⟨fun x : Set.Icc a b => p.eval x, p.continuous.comp continuous_subtype_val⟩ :
    C(Set.Icc a b, ℝ))‖
def monicValue (m : ℕ) : ℝ[X] := C (((2 : ℝ) ^ (m - 1))⁻¹) * tValue m
def affineValue (a b : ℝ) (m : ℕ) : ℝ[X] :=
  C (((b - a) / 2) ^ m) *
    (monicValue m).comp (C (2 / (b - a)) * X + C (-(a + b) / (b - a)))

def tType := ℕ → ℝ[X]
def nodeType := ℕ → ℕ → ℝ
def normType := ℝ → ℝ → ℝ[X] → ℝ
def monicType := ℕ → ℝ[X]
def affineType := ℝ → ℝ → ℕ → ℝ[X]

def cosine : Prop := ∀ (m : ℕ) (θ : ℝ), (tValue m).eval (Real.cos θ) = Real.cos (m * θ)
def degree : Prop := ∀ m : ℕ, (tValue m).degree = (m : WithBot ℕ)
def leadingCoefficient : Prop := ∀ m : ℕ, (tValue m).leadingCoeff = (2 : ℝ) ^ (m - 1)
def tNorm : Prop := ∀ m : ℕ, normValue (-1) 1 (tValue m) = 1
def roots : Prop := ∀ m : ℕ,
  (tValue m).roots = (Multiset.range m).map (nodeValue m)
def monicRoots : Prop := ∀ m : ℕ,
  (monicValue m).roots = (Multiset.range m).map (nodeValue m)

def distinctNodes : Prop := ∀ m : ℕ, Set.InjOn (nodeValue m) (Finset.range m)
def scaleIdentity : Prop := ∀ (m : ℕ), 1 ≤ m →
  ((2 : ℝ) ^ (m - 1))⁻¹ = (2 : ℝ) ^ (1 - (m : ℤ))

def monicProperties : Prop := ∀ (m : ℕ), 1 ≤ m →
  (monicValue m).Monic ∧ (monicValue m).degree = (m : WithBot ℕ) ∧
  normValue (-1) 1 (monicValue m) = ((2 : ℝ) ^ (m - 1))⁻¹

def minimax : Prop := ∀ (m : ℕ), 1 ≤ m → ∀ q : ℝ[X],
  q.Monic → q.degree = (m : WithBot ℕ) →
  ((2 : ℝ) ^ (m - 1))⁻¹ ≤ normValue (-1) 1 q ∧
  (normValue (-1) 1 q ≤ ((2 : ℝ) ^ (m - 1))⁻¹ ↔ q = monicValue m)

def affineProperties : Prop := ∀ (a b : ℝ), a < b → ∀ (m : ℕ), 1 ≤ m →
  (affineValue a b m).Monic ∧ (affineValue a b m).degree = (m : WithBot ℕ) ∧
  normValue a b (affineValue a b m) = ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹

def affineMinimax : Prop := ∀ (a b : ℝ), a < b → ∀ (m : ℕ), 1 ≤ m → ∀ q : ℝ[X],
  q.Monic → q.degree = (m : WithBot ℕ) →
  ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹ ≤ normValue a b q ∧
  (normValue a b q ≤ ((b - a) / 2) ^ m * ((2 : ℝ) ^ (m - 1))⁻¹ ↔
    q = affineValue a b m)

def affineNodalPolynomial : Prop := ∀ (a b : ℝ), a < b → ∀ (m : ℕ), 1 ≤ m →
  affineValue a b m = ∏ j ∈ Finset.range m,
    (X - C ((a + b) / 2 + (b - a) / 2 * nodeValue m j))

end Specs.NumAnalysis206.Approximation.Chebyshev
