import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import Mathlib.Topology.Connected.PathConnected

/-! The norm-path classification in `fa2:p2:index-components`, paper.tex
10673–10694. The ambient operator space has its operator norm topology.
No restriction on the dimension of the complex Hilbert space is imposed. -/
noncomputable section
namespace ExpandedFA.Fredholm.IndexComponentsSpec
universe u
open DefinitionsSpec

def IndexComponents : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (hA : IsFredholmValue A) (hB : IsFredholmValue B),
    JoinedIn {T : H →L[ℂ] H | IsFredholmValue T} A B ↔
      fredholmIndexValue A hA = fredholmIndexValue B hB

end ExpandedFA.Fredholm.IndexComponentsSpec
