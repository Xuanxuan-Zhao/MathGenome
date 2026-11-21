import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Independent residual obligations of `fa2:p2:index` (paper.tex 10626–10635).
The Banach index calculus is allocated to IndexStability. These statements
cover arbitrary real/complex Hilbert spaces, including zero spaces and
nonseparable spaces. Local constancy is expressed by an ambient operator-norm
neighborhood, and includes both infinite values of the shared extended index. -/

namespace ExpandedFA.Fredholm.HilbertSemiFredholmIndexSpec
open scoped Topology
universe u v w

def AdjointFredholm : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K] (T : H →L[𝕜] K),
    DefinitionsSpec.IsFredholmValue T ↔ DefinitionsSpec.IsFredholmValue T.adjoint

def AdjointIndex : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (hT : DefinitionsSpec.IsFredholmValue T)
    (hstar : DefinitionsSpec.IsFredholmValue T.adjoint),
    DefinitionsSpec.fredholmIndexValue T.adjoint hstar =
      -DefinitionsSpec.fredholmIndexValue T hT

def SemiFredholmIndexLocallyConstant : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {K : Type w}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 K]
    [CompleteSpace H] [CompleteSpace K]
    (T : H →L[𝕜] K) (hT : DefinitionsSpec.IsSemiFredholmValue T),
    ∀ᶠ S in 𝓝 T, ∃ hS : DefinitionsSpec.IsSemiFredholmValue S,
      DefinitionsSpec.semiFredholmIndexValue S hS =
        DefinitionsSpec.semiFredholmIndexValue T hT

end ExpandedFA.Fredholm.HilbertSemiFredholmIndexSpec
