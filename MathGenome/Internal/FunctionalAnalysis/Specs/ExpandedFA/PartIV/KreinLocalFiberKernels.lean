import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinRealSpectralModel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2HilbertSchmidt

/-! Local vector kernels in the canonical coordinate fibers, for
paper.tex:21274–21287. The uniqueness statement deliberately has no fiber
hypothesis. The measure and the Hilbert space may both be zero. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ExpandedFA.PartIV.KreinLocalFiberKernels
open KreinSpectralKernel

/-- All local conclusions refer to the same representative. -/
structure LocalKernel {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure ℝ) (m : ℝ → ℕ∞) (v : ℝ → H)
    (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ) (R : ℝ) where
  h : ℝ → ℝ → FiberSpace
  measurable : AEStronglyMeasurable (Function.uncurry h) (μ.prod (intervalMeasure R))
  square : MemLp (Function.uncurry h) 2 (μ.prod (intervalMeasure R))
  rows : ∀ᵐ ξ ∂μ, MemLp (h ξ) 2 (intervalMeasure R)
  fibers : ∀ᵐ ξ ∂μ, ∀ᵐ t ∂intervalMeasure R, h ξ t ∈ coordinateFiber (m ξ)
  represents : ∀ f : Lp ℂ 2 (intervalMeasure R),
    (U (∫ t, f t • v t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[μ]
      fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R
  energy : (∫⁻ ξ, ∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂intervalMeasure R ∂μ) =
    ENNReal.ofReal (∫ t, ‖v t‖ ^ 2 ∂intervalMeasure R)

namespace Spec

def LocalKernelExistence : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (v : ℝ → H), Continuous v →
    ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (m : ℝ → ℕ∞), Measurable m →
    ∀ (U : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ),
    (∀ x : H, ∀ᵐ ξ ∂μ, U x ξ ∈ coordinateFiber (m ξ)) →
    ∀ R : ℝ, 0 < R → Nonempty (LocalKernel μ m v U R)

def KernelUniqueness : Prop :=
  ∀ (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (h k : ℝ → ℝ → FiberSpace),
    MemLp (Function.uncurry h) 2 (μ.prod ν) →
    MemLp (Function.uncurry k) 2 (μ.prod ν) →
    (∀ f : Lp ℂ 2 ν,
      (fun ξ => ∫ t, f t • h ξ t ∂ν) =ᵐ[μ]
        fun ξ => ∫ t, f t • k ξ t ∂ν) →
    Function.uncurry h =ᵐ[μ.prod ν] Function.uncurry k

/-- A reverse theorem, to be proved from matrix coefficients, not assumed. -/
def ReverseScalarKernel : Prop :=
  ∀ (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ),
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T →
    ∃! k : Lp ℂ 2 (μ.prod ν), PartV.L2KernelSpec.OperatorValue μ ν k = T

/-- The synthesis map is the actual Bochner integral. -/
def LocalSynthesisEnergy : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (v : ℝ → H), Continuous v → ∀ R : ℝ,
    ∃ J : Lp ℂ 2 (intervalMeasure R) →L[ℂ] H,
      (∀ f, J f = ∫ t, f t • v t ∂intervalMeasure R) ∧
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue J =
        ENNReal.ofReal (∫ t, ‖v t‖ ^ 2 ∂intervalMeasure R)
end Spec
end ExpandedFA.PartIV.KreinLocalFiberKernels
