import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceClassDefinitions

/-! First-power trace index formula, paper.tex, fa2:p2:trace-index.
The index is an integer cast to the scalar field of the shared Hilbert trace.
No restriction on either Hilbert dimension is imposed. -/
noncomputable section
universe u v w
namespace ExpandedFA.Fredholm.TraceIndex.Spec
open TraceIdeals.TraceClassDefinitions.Spec

def FirstPowerTraceIndex : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (S : K →L[𝕜] H),
    IsTraceClassValue (ContinuousLinearMap.id 𝕜 H - S.comp T) →
    IsTraceClassValue (ContinuousLinearMap.id 𝕜 K - T.comp S) →
    ∃ h : DefinitionsSpec.IsFredholmValue T,
      (DefinitionsSpec.fredholmIndexValue T h : 𝕜) =
        TraceValue (ContinuousLinearMap.id 𝕜 H - S.comp T) -
          TraceValue (ContinuousLinearMap.id 𝕜 K - T.comp S)

end ExpandedFA.Fredholm.TraceIndex.Spec
