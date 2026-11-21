import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMaximalInterfaces

/-! Uniform grand-maximal bounds in the last proof of the fixed-kernel chapter.
The positive-dimension and admissible-order conditions are those of that chapter.
The input is the accepted atomic quotient, mapped to its actual L¹ representative.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.HardyGrandForwardSpec
open ExpandedFA.Fourier HardyMaximalSpec ExpandedFA.Hardy.AtomicHardySpaceSpec

/-- Uniform in the entire compact-test family and in every positive scale. -/
def AtomEstimate : Prop := ∀ (d N : ℕ), 0 < d → AdmissibleOrder d N →
  ∃ C : ℝ≥0, ∀ {𝕜 : Type} [RCLike 𝕜]
    (a : AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))),
    (∫⁻ x, grand N (a.val : Euclidean d → 𝕜) x) ≤ (C : ℝ≥0∞)

/-- The full forward estimate, with the genuine quotient atomic norm. -/
def Forward : Prop := ∀ (d N : ℕ), 0 < d → AdmissibleOrder d N →
  ∃ C : ℝ≥0, ∀ {𝕜 : Type} [RCLike 𝕜] (h : Hardy 𝕜 d),
    (∫⁻ x, grand N (EmbeddingValue volume h : Euclidean d → 𝕜) x) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal ‖h‖

end ExpandedFA.PartIV.HardyGrandForwardSpec
