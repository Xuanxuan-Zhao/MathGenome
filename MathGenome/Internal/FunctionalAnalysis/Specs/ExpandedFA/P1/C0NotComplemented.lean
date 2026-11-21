import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import Mathlib.Topology.Algebra.Module.Complement

/-! Noncomplementation assertion of `fa2:p1:czero-uncomplemented`.
The submodule is the canonical null sequences inside the actual bounded scalar
sequences, with the inherited norm. `RCLike` covers both real and complex scalars.
The bidual and nondual assertions are allocated separately from this goal. -/
namespace ExpandedFA.P1.C0NotComplemented.Spec
open C01SequenceSpaces
universe u

def NoProjection : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ ∃ P : SequenceLInfinity 𝕜 →L[𝕜] SequenceLInfinity 𝕜,
      P.comp P = P ∧ P.range = sequenceC0Submodule 𝕜

def NotComplemented : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ (sequenceC0Submodule 𝕜).ClosedComplemented

end ExpandedFA.P1.C0NotComplemented.Spec
