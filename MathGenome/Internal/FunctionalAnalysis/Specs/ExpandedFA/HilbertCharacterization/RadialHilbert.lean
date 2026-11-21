import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.RadialCriterion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.Kakutani

/-! The radial characterization, paper.tex:9352–9356, fa2:p2:radial-hilbert.
The real cardinal dimension bound includes infinite-dimensional spaces.
No completeness is assumed, and the compatible inner product preserves the
original normed additive group and real scalar action. -/
namespace ExpandedFA.HilbertCharacterization.RadialHilbert.Spec
universe u

def Characterization : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    (3 : Cardinal) ≤ Module.rank ℝ X →
    ((∀ x y : X, ‖radialRetraction x - radialRetraction y‖ ≤ ‖x - y‖) ↔
      Kakutani.HasCompatibleInnerProduct X)

end ExpandedFA.HilbertCharacterization.RadialHilbert.Spec
