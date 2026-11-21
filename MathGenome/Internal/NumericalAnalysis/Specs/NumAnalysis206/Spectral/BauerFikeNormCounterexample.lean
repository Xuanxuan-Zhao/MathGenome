import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.BauerFikeResolvent
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

namespace NumAnalysis206.BauerFikeExampleData

abbrev X := Fin 2 → ℂ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def A : Mat := !![0, 0; 0, 1]
def S (M : ℝ) : Mat := !![1, (M : ℂ); 0, 1]
def B (M : ℝ) : Mat := !![0, 0; (M : ℂ)⁻¹, 0]
def E (M : ℝ) : Mat := (S M)⁻¹ * B M * S M

/-- Coordinates are mapped to `S x` in the ordinary sup-norm space. -/
def shear (M : ℝ) : X ≃ₗ[ℂ] X where
  toFun x := ![x 0 + (M : ℂ) * x 1, x 1]
  invFun x := ![x 0 - (M : ℂ) * x 1, x 1]
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' c x := by ext i; fin_cases i <;> simp; ring

def basis (M : ℝ) : Module.Basis (Fin 2) ℂ X :=
  (Pi.basisFun ℂ (Fin 2)).map (shear M)

def vectorNorm (M : ℝ) (x : X) : ℝ := ‖(S M).mulVec x‖
def matrixNorm (M : ℝ) (C : Mat) : ℝ :=
  MatrixDefinitions.subordinateNorm (basis M) (basis M) C

def rootPlus : ℝ := (1 + Real.sqrt 5) / 2
def rootMinus : ℝ := (1 - Real.sqrt 5) / 2
def gap : ℝ := (Real.sqrt 5 - 1) / 2

end NumAnalysis206.BauerFikeExampleData

namespace Specs.NumAnalysis206.BauerFikeNormCounterexample
open _root_.NumAnalysis206.BauerFikeExampleData

/-- The shear example, in its actual specified subordinate norm. The two
spectral equalities specify the complete spectra, with complex eigenvalues.
`infDist` is distance to the complete unperturbed spectrum. -/
def counterexample : Prop :=
  ∀ (M : ℝ), 2 < M →
    IsUnit (S M) ∧
    (∀ x : X, ‖(basis M).equivFun.symm x‖ = vectorNorm M x) ∧
    S M * E M * (S M)⁻¹ = B M ∧
    matrixNorm M (E M) = 1 / M ∧
    matrixNorm M (1 : Mat) * matrixNorm M ((1 : Mat)⁻¹) = 1 ∧
    spectrum ℂ A = {0, 1} ∧
    spectrum ℂ (A + E M) = {(rootPlus : ℂ), (rootMinus : ℂ)} ∧
    (∀ μ ∈ spectrum ℂ (A + E M),
      Metric.infDist μ (spectrum ℂ A) = gap ∧
      matrixNorm M (1 : Mat) * matrixNorm M ((1 : Mat)⁻¹) *
        matrixNorm M (E M) < Metric.infDist μ (spectrum ℂ A) ∧
      μ ∉ spectrum ℂ A ∧
      1 ≤ matrixNorm M ((μ • (1 : Mat) - A)⁻¹) * matrixNorm M (E M))

end Specs.NumAnalysis206.BauerFikeNormCounterexample
