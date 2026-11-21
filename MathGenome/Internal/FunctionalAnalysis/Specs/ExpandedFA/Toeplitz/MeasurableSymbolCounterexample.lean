import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Toeplitz.Definitions
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The singular inner function in paper.tex:10466–10519, on the actual
upstream Hardy space and normalized circle. The value at the exceptional
boundary point is immaterial; totalized division sets it to one. -/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology

namespace ExpandedFA.Toeplitz.MeasurableSymbolCounterexample.Spec
open ExpandedFA.Toeplitz.Definitions.Spec
open ExpandedFA.PartIV.HardyDiskSpec (disk eval)
abbrev Torus := ExpandedFA.Toeplitz.Definitions.Spec.Circle

/-- The specified function, not an arbitrary singular inner function. -/
def theta (z : ℂ) : ℂ := Complex.exp (-((1 + z) / (1 - z)))

/-- Boundary values away from the singular point, with a harmless value there. -/
def boundaryFunction (t : Torus) : ℂ := theta (fourier (T := 2 * π) 1 t)

def AnalyticBound : Prop := DifferentiableOn ℂ theta disk ∧
  ∀ z ∈ disk, ‖theta z‖ ≤ 1

def BoundaryConstruction : Prop := ∃ φ : ScalarSymbol,
  (φ : Torus → ℂ) =ᵐ[circleMeasure] boundaryFunction ∧
  (∀ᵐ t ∂circleMeasure, ‖φ t‖ = 1) ∧
  (∀ᵐ t ∂circleMeasure,
    Tendsto (fun r : ℝ => theta ((r : ℂ) * fourier (T := 2 * π) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (φ t)))

/-- Compression equals multiplication by the stated disk function, with its
full isometry, closed-range and infinite-cokernel consequences. -/
def Counterexample : Prop := AnalyticBound ∧ ∃ φ : ScalarSymbol,
  (φ : Torus → ℂ) =ᵐ[circleMeasure] boundaryFunction ∧
  (∀ᵐ t ∂circleMeasure, ‖φ t‖ = 1) ∧
  (∀ᵐ t ∂circleMeasure,
    Tendsto (fun r : ℝ => theta ((r : ℂ) * fourier (T := 2 * π) 1 t))
      (𝓝[<] (1 : ℝ)) (𝓝 (φ t))) ∧
  (∀ (f : H2) (z : ℂ), z ∈ disk →
    eval (toeplitz φ f) z = theta z * eval f z) ∧
  Isometry (toeplitz φ) ∧
  IsClosed (Set.range (toeplitz φ)) ∧
  ¬ FiniteDimensional ℂ (H2 ⧸ LinearMap.range (toeplitz φ).toLinearMap) ∧
  ¬ (toeplitz φ).IsFredholm

end ExpandedFA.Toeplitz.MeasurableSymbolCounterexample.Spec
