import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatExactTrace

/-! Full flat trace/lift lemma, paper.tex:2462–2539. The p>1 clause uses
exactly the existing fractional space and slice trace. At p=1 the constant
is uniform in the scalar field and the slice trace; the preimage may depend
nonlinearly on the datum. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace P102.Trace.FlatTraceLiftExpected

/-- Quantitative surjectivity of the same flat trace at the endpoint. -/
def Endpoint : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜],
      (∃ T : HalfSobolev m 𝕜 1 →L[𝕜] BoundaryLp m 𝕜 1, IsFlatTrace T) ∧
      ∀ T : HalfSobolev m 𝕜 1 →L[𝕜] BoundaryLp m 𝕜 1, IsFlatTrace T →
        ∀ g : BoundaryLp m 𝕜 1,
          ∃ u : HalfSobolev m 𝕜 1, T u = g ∧ ‖u‖ ≤ C * ‖g‖

/-- Both exponent ranges of the complete lemma, in the original sum norm. -/
def FlatTraceLift : Prop := FlatExactTraceExpected.ExactFlatTrace ∧ Endpoint

end P102.Trace.FlatTraceLiftExpected
