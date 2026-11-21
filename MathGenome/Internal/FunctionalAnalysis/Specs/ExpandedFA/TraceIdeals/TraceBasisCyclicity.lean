import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.TraceNormIdeal

/-! Trace on arbitrary real or complex Hilbert spaces. The shared trace is the
chosen-basis diagonal sum; the statements below identify it on every basis.
Rectangular cyclicity includes ideal membership of both endomorphisms. -/
noncomputable section
universe u v w z
namespace ExpandedFA.TraceIdeals.TraceBasisCyclicity.Spec
open TraceClassDefinitions.Spec

def DiagonalTrace : Prop := TraceClassDefinitions.Spec.DiagonalTrace.{u,v,z}
def TraceBound : Prop := TraceClassDefinitions.Spec.TraceBound.{u,v}
def RankOneTrace : Prop := TraceClassDefinitions.Spec.RankOneTrace.{u,v}

def RectangularCyclicity : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) (K : Type w)
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (A : K →L[𝕜] H),
    (IsTraceClassValue T ∨ IsTraceClassValue A) →
      IsTraceClassValue (A.comp T) ∧ IsTraceClassValue (T.comp A) ∧
        TraceValue (A.comp T) = TraceValue (T.comp A)

end ExpandedFA.TraceIdeals.TraceBasisCyclicity.Spec
