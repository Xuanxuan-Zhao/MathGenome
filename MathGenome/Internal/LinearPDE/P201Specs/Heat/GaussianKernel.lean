import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The positive-time Gaussian kernel stage of `pde:heat-gaussian`.
The convolution is stated as its defining pointwise Lebesgue integral.
All dimensions n ≥ 1, including n = 1, are covered. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace P201Specs.Heat

abbrev gaussianKernelType := (n : ℕ) → ℝ → Space n → ℝ

def gaussianKernel : gaussianKernelType := fun n t x =>
  (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

def gaussianNonnegativeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t → ∀ x : Space n,
    0 ≤ gaussianKernel n t x

def gaussianIntegrableStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
    Integrable (gaussianKernel n t) (spatialMeasure n)

def gaussianMassStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t →
    (∫ x, gaussianKernel n t x ∂spatialMeasure n) = 1

def gaussianSmoothStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ContDiffOn ℝ ∞ (fun z : Space n × ℝ => gaussianKernel n z.2 z.1)
      {z | 0 < z.2}

def gaussianHeatEquationStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℝ), 0 < t → ∀ x : Space n,
    deriv (fun s => gaussianKernel n s x) t = laplacian (gaussianKernel n t) x

def gaussianConvolutionStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t s : ℝ), 0 < t → 0 < s → ∀ x : Space n,
    (∫ y, gaussianKernel n t (x - y) * gaussianKernel n s y ∂spatialMeasure n) =
      gaussianKernel n (t + s) x

end P201Specs.Heat
