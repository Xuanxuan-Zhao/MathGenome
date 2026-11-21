import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C0NotDual

/-! Independent statement of `fa2:p1:czero-uncomplemented`, paper.tex
4462–4467. The sequence spaces carry their native supremum and inherited
norms; canonical evaluation uses continuous scalar-linear functionals.
`ClosedComplemented` means existence of a continuous linear retraction,
equivalently a topological direct-sum complement. -/

namespace ExpandedFA.P1.CzeroUncomplemented.Spec
open C01SequenceSpaces
universe u v

/-- The full noncomplementation theorem, over either scalar field and with
no completeness assumption on a proposed predual. -/
def Noncomplementation : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜)) ∧
    ¬ (sequenceC0Submodule 𝕜).ClosedComplemented ∧
    ¬ (C0NotDual.evaluation 𝕜 (SequenceC0 𝕜)).range.ClosedComplemented ∧
    ∀ (Y : Type v) [NormedAddCommGroup Y] [NormedSpace 𝕜 Y],
      ¬ Nonempty (SequenceC0 𝕜 ≃L[𝕜] (Y →L[𝕜] 𝕜))

end ExpandedFA.P1.CzeroUncomplemented.Spec
