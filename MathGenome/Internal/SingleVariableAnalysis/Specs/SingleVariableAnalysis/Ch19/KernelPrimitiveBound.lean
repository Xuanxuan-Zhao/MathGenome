import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.DirichletKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The oscillatory estimate in K03.19.jordan, paper.tex:4836–4854.
All integrals below are proper Darboux integrals, including intervals starting
at zero. The kernel remains the finite exponential sum from the shared Spec. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.KernelPrimitiveBound
open Ch08.Integral

/-- Its value at zero is zero, the removable extension of the difference. -/
def correction (t : ℝ) : ℝ := 1 / Real.sin (t / 2) - 2 / t

def correctionAtZero : Prop := ContinuousAt correction 0

def correctionContinuous : Prop :=
  ContinuousOn correction (Set.Icc 0 Real.pi)

/-- The sinc estimate includes the neighborhood of zero and arbitrary finite
nonnegative endpoints; no upper bound on the endpoints is imposed. -/
def sincIntegralBound : Prop := ∃ C : ℝ, 0 ≤ C ∧
  ∀ (u v : ℝ), 0 ≤ u → u ≤ v →
    ∃ h : realIntegrableValue Real.sinc u v,
      |realIntegralValue Real.sinc h| ≤ C

def kernelPrimitiveBound : Prop := ∃ C : ℝ, 0 ≤ C ∧
  ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → u ≤ v → v ≤ Real.pi →
    ∃ h : complexIntegrableValue (DirichletKernel.kernelValue N) u v,
      ‖complexIntegralValue _ h‖ ≤ C

end Specs.SingleVariableAnalysis.Ch19.KernelPrimitiveBound
