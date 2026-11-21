import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions

/-! The Hilbert–Schmidt assertion of `fa2:p5:l2-kernel`.
The canonical operator and ordinary product L² spaces are the upstream objects.
Neither space nor either orthonormal basis is assumed separable. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v a
namespace ExpandedFA.PartV.L2HilbertSchmidtSpec
open ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec

def SquareIdentity : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)),
    HilbertSchmidtSquareValue (L2KernelSpec.OperatorValue μ ν k) =
      ENNReal.ofReal (∫ p, ‖k p‖ ^ 2 ∂μ.prod ν)

def Finiteness : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)), IsHilbertSchmidtValue (L2KernelSpec.OperatorValue μ ν k)

def NormIdentity : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)) (h : IsHilbertSchmidtValue (L2KernelSpec.OperatorValue μ ν k)),
    HilbertSchmidtNormValue ⟨L2KernelSpec.OperatorValue μ ν k, h⟩ ^ 2 =
      ∫ p, ‖k p‖ ^ 2 ∂μ.prod ν

def EveryBasisIdentity : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)) {ι : Type a} (e : ι → Lp 𝕜 2 ν),
    IsBasis (𝕜 := 𝕜) e →
    Summable (fun i => ‖L2KernelSpec.OperatorValue μ ν k (e i)‖ ^ 2) ∧
      (∑' i, ‖L2KernelSpec.OperatorValue μ ν k (e i)‖ ^ 2) =
        ∫ p, ‖k p‖ ^ 2 ∂μ.prod ν

end ExpandedFA.PartV.L2HilbertSchmidtSpec
