import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.TraceIndex

/-! Powered trace-index formula from `fa2:p2:trace-index`.
Both Hilbert spaces may have arbitrary dimension, including zero. The
unpowered defects are not required to be compact or trace class. -/
noncomputable section
universe u v w
namespace ExpandedFA.Fredholm.TraceIndexPowers.Spec
open TraceIdeals.TraceClassDefinitions.Spec

/-- A positive integral power is represented by a natural exponent `m ≥ 1`.
The index is the shared integer-valued Fredholm index, cast to the trace field. -/
def PoweredTraceIndex : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (S : K →L[𝕜] H) (m : ℕ),
    1 ≤ m →
    IsTraceClassValue ((ContinuousLinearMap.id 𝕜 H - S.comp T) ^ m) →
    IsTraceClassValue ((ContinuousLinearMap.id 𝕜 K - T.comp S) ^ m) →
    ∃ h : DefinitionsSpec.IsFredholmValue T,
      (DefinitionsSpec.fredholmIndexValue T h : 𝕜) =
        TraceValue ((ContinuousLinearMap.id 𝕜 H - S.comp T) ^ m) -
          TraceValue ((ContinuousLinearMap.id 𝕜 K - T.comp S) ^ m)

end ExpandedFA.Fredholm.TraceIndexPowers.Spec
