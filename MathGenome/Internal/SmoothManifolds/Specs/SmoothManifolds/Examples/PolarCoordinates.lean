import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.SpheresAndTori
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace SmoothManifolds.PolarData
open ModelData Set

/-- Coordinates in the order (angle of period one, radius). -/
noncomputable def polar (x : Euclidean 2) : Euclidean 2 :=
  ![x 1 * Real.cos (2 * Real.pi * x 0), x 1 * Real.sin (2 * Real.pi * x 0)]

def reflect (x : Euclidean 2) : Euclidean 2 := ![-x 0, x 1]

def sector (a δ r₀ r₁ : ℝ) : Set (Euclidean 2) :=
  {x | |x 0 - a| < δ ∧ r₀ < x 1 ∧ x 1 < r₁}

noncomputable def positiveCollar (x : Euclidean 2) : Euclidean 2 :=
  polar ![x 0, 1 / 8 + x 1]

noncomputable def negativeCollar (x : Euclidean 2) : Euclidean 2 :=
  reflect (polar ![x 0, 1 / 8 - x 1])

end SmoothManifolds.PolarData

namespace Specs.SmoothManifolds.Examples.PolarCoordinates
open SmoothManifolds.ModelData SmoothManifolds.PolarData Set

def polarType := Euclidean 2 → Euclidean 2
noncomputable def polarValue : polarType := polar

def reflectType := Euclidean 2 → Euclidean 2
def reflectValue : reflectType := reflect

def sectorTypeOfDefinition := ℝ → ℝ → ℝ → ℝ → Set (Euclidean 2)
def sectorValue : sectorTypeOfDefinition := sector

def positiveCollarType := Euclidean 2 → Euclidean 2
noncomputable def positiveCollarValue : positiveCollarType := positiveCollar

def negativeCollarType := Euclidean 2 → Euclidean 2
noncomputable def negativeCollarValue : negativeCollarType := negativeCollar

def smoothType : Prop := ContDiff ℝ (⊤ : ℕ∞) polar

def localInverseType : Prop := ∀ x : Euclidean 2, 0 < x 1 →
  ∃ e : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2),
    x ∈ e.source ∧ (∀ y, e y = polar y) ∧
    (∀ y ∈ e.source, 0 < y 1) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target

def fibersType : Prop := ∀ x y : Euclidean 2, 0 < x 1 → 0 < y 1 →
  (polar x = polar y ↔ x 1 = y 1 ∧ ∃ k : ℤ, x 0 = y 0 + k)

def injectiveType : Prop := ∀ a b : ℝ, b - a < 1 →
  InjOn polar {x | a < x 0 ∧ x 0 < b ∧ 0 < x 1}

def sectorType : Prop := ∀ a δ r₀ r₁ : ℝ, 0 < δ → δ < 1 / 4 →
    0 < r₀ → r₀ < r₁ →
  ∃ e : OpenPartialHomeomorph (Euclidean 2) (Euclidean 2),
    e.source = sector a δ r₀ r₁ ∧ e.target = polar '' sector a δ r₀ r₁ ∧
    (∀ x, e x = polar x) ∧ ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target

def jacobianType : Prop := ∀ x : Euclidean 2,
  (fderiv ℝ polar x).det = -2 * Real.pi * x 1

def reflectionType : Prop :=
  (∀ x : Euclidean 2, (fderiv ℝ reflect x).det = -1) ∧
  ∀ s r : ℝ, reflect (polar ![s,r]) = polar ![1/2-s,r]

def collarType : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) positiveCollar ∧ ContDiff ℝ (⊤ : ℕ∞) negativeCollar ∧
  (∀ x : Euclidean 2, (fderiv ℝ positiveCollar x).det = -2 * Real.pi * (1/8+x 1)) ∧
  (∀ x : Euclidean 2, (fderiv ℝ negativeCollar x).det = -2 * Real.pi * (1/8-x 1)) ∧
  (∀ x : Euclidean 2, 0 < 1/8+x 1 → (fderiv ℝ positiveCollar x).det < 0) ∧
  (∀ x : Euclidean 2, 0 < 1/8-x 1 → (fderiv ℝ negativeCollar x).det < 0)

end Specs.SmoothManifolds.Examples.PolarCoordinates
