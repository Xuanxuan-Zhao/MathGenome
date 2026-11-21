import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions

/-! The kernel correspondence in `fa2:p2:hilbert-schmidt` (paper.tex
11413–11436). All measures are positive and sigma-finite. L² is the ordinary
almost-everywhere quotient on the ordinary product, with no countability
assumption on either measurable space or either Hilbert basis. The operator
is exactly the canonical integral operator from Part V. -/
noncomputable section
open MeasureTheory
universe u v
namespace ExpandedFA.TraceIdeals.HilbertSchmidtKernels.Spec
open HilbertSchmidtDefinitions.Spec
open ExpandedFA.PartV

def KernelIsometry : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)),
    IsHilbertSchmidtValue (L2KernelSpec.OperatorValue μ ν k) ∧
      ∀ h : IsHilbertSchmidtValue (L2KernelSpec.OperatorValue μ ν k),
        HilbertSchmidtNormValue ⟨L2KernelSpec.OperatorValue μ ν k, h⟩ = ‖k‖

def UniqueKernel : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ),
    IsHilbertSchmidtValue T → ∃! k : Lp 𝕜 2 (μ.prod ν), L2KernelSpec.OperatorValue μ ν k = T

def KernelAEUniqueness : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k l : Lp 𝕜 2 (μ.prod ν)),
    L2KernelSpec.OperatorValue μ ν k = L2KernelSpec.OperatorValue μ ν l ↔ k =ᵐ[μ.prod ν] l

/-- The inverse correspondence satisfies the actual integration formula and norm. -/
def IntegralRepresentation : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ) (hT : IsHilbertSchmidtValue T),
    ∃ k : Lp 𝕜 2 (μ.prod ν),
      L2KernelSpec.OperatorValue μ ν k = T ∧
      (∀ f : Lp 𝕜 2 ν, (T f : X → 𝕜) =ᵐ[μ]
        fun x => ∫ y, k (x, y) * f y ∂ν) ∧
      HilbertSchmidtNormValue ⟨T, hT⟩ = ‖k‖

end ExpandedFA.TraceIdeals.HilbertSchmidtKernels.Spec
