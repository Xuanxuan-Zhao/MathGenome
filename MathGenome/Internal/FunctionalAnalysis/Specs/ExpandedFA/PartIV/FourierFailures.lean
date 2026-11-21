import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DirichletKernel
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! The three conclusions of `fa2:p4:fourier-failures`, with normalized Haar
measure and the actual symmetric integral Fourier sums from DirichletKernelSpec.
The discrete-space model C₀(ℤ, ℂ) is c₀(ℤ) with its supremum norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ZeroAtInfty
namespace ExpandedFA.PartIV.FourierFailuresSpec
open DirichletKernelSpec
abbrev Circle := DirichletKernelSpec.Circle
abbrev CoefficientSpace := C₀(ℤ, ℂ)

def ContinuousDivergence : Prop := ∀ x : Circle,
  ∃ f : C(Circle, ℂ), ∀ B : ℝ, ∃ N : ℕ, B < ‖partialSum N f x‖

def RealContinuousDivergence : Prop := ∀ x : Circle,
  ∃ f : C(Circle, ℝ), ∀ B : ℝ, ∃ N : ℕ,
    B < ‖partialSum N (fun t => (f t : ℂ)) x‖

def CoefficientDecay : Prop := ∀ f : L1,
  Tendsto (fourierCoeff f) cofinite (𝓝 0)

/-- Includes boundedness, c₀-valuedness, injectivity, and failure of surjectivity
for one and the same map, identified by every coefficient integral. -/
def CoefficientMapFailure : Prop := ∃ F : L1 →L[ℂ] CoefficientSpace,
  (∀ f n, F f n = fourierCoeff f n) ∧ ‖F‖ ≤ 1 ∧
    Function.Injective F ∧ ¬ Function.Surjective F

def L1Divergence : Prop := ∃ f : L1,
  (∀ B : ℝ, ∃ N : ℕ, B < ‖partialSumL1 N f‖) ∧
    ¬ ∃ g : L1, Tendsto (fun N => partialSumL1 N f) atTop (𝓝 g)

/-- For real data the real L¹ classes are identified a.e. with the same actual
complex exponential partial sums, and their real L¹ norms are unbounded. -/
def RealL1Divergence : Prop := ∃ f : RealL1, ∃ u : ℕ → RealL1,
  (∀ N, (fun x => ((u N x : ℝ) : ℂ)) =ᵐ[haar]
    (fun x => partialSum N (fun t => (f t : ℂ)) x)) ∧
  (∀ B : ℝ, ∃ N : ℕ, B < ‖u N‖) ∧
    ¬ ∃ g : RealL1, Tendsto u atTop (𝓝 g)
end ExpandedFA.PartIV.FourierFailuresSpec
