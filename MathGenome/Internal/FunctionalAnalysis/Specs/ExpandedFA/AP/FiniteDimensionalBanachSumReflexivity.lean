import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.EnfloSpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! The dual and bidual identifications in paper.tex:12802–12825.
All norms on the summands remain the supremum norms of continuous functions.
The real continuous linear dual, rather than an antidual, is used throughout. -/
set_option maxSynthPendingDepth 5
set_option synthInstance.maxSize 512
noncomputable section
open scoped ENNReal
namespace ExpandedFA.AP.FiniteDimensionalBanachSumReflexivity.Spec
open EnfloSpace.Spec

abbrev DualSum (D : IncidenceData) := lp (fun m => Summand D m →L[ℝ] ℝ) 2
abbrev BidualSum (D : IncidenceData) :=
  lp (fun m => (Summand D m →L[ℝ] ℝ) →L[ℝ] ℝ) 2

/-- Both identifications are isometries, with the inverse dual map given by
restriction to individual blocks. The bidual formula specifies its action on
arbitrary bidual elements, as well as on the canonical image of Y. -/
def DualAndBidualIdentification : Prop := ∀ D : IncidenceData,
  ∃ e : DualSum D ≃ₗᵢ[ℝ] (Y D →L[ℝ] ℝ),
    (∀ f y, HasSum (fun m => f m (y m)) (e f y)) ∧
    (∀ F m x, e.symm F m x = F (lp.single 2 m x)) ∧
    ∃ b : ((Y D →L[ℝ] ℝ) →L[ℝ] ℝ) ≃ₗᵢ[ℝ] BidualSum D,
      (∀ B m f, b B m f = B (e (lp.single 2 m f))) ∧
      (∀ y m, b (ExpandedFA.P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ (Y D) y) m =
        ExpandedFA.P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ (Summand D m) (y m))

def AmbientReflexive : Prop := ∀ D : IncidenceData,
  ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ (Y D)

def ClosedSpanReflexive : Prop := ∀ D : IncidenceData,
  ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ (X D)

end ExpandedFA.AP.FiniteDimensionalBanachSumReflexivity.Spec
