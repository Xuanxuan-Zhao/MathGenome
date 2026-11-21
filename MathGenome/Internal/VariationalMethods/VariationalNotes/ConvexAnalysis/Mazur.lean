import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Mazur
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.WeakLowerSemicontinuity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12Mazur

noncomputable section
universe u
open Filter
open scoped Topology BigOperators
namespace VariationalNotes.ConvexAnalysis

/-- Explicit finite convex combinations of successive tails converge in norm.
The library theorem works in incomplete normed spaces as required here. -/
theorem mazur_tail_combinations : Specs.mazur_tail_combinations.{u} := by
  intro X _ _ xseq x hx
  have hx' : Tendsto xseq atTop
      (@nhds X (ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue
        ℝ X (X →L[ℝ] ℝ) (topDualPairing ℝ X)) x) := by
    change Tendsto xseq atTop
      (@nhds X (TopologicalSpace.induced (toWeakSpace ℝ X)
        (instTopologicalSpaceWeakSpace ℝ X)) x)
    rw [nhds_induced, tendsto_comap_iff]
    exact hx
  exact ExpandedFA.P1.C12Mazur.mazur_tail_combinations ℝ X xseq x hx'

/-- Weak closedness, weak lower semicontinuity, and Mazur approximation,
with exactly the hypotheses of the three source assertions. -/
theorem convex_weak_closed : Specs.convex_weak_closed.{u} :=
  ⟨normClosed_convex_isWeaklyClosed,
    convex_normLowerSemicontinuous_isWeaklyLowerSemicontinuous,
    mazur_tail_combinations⟩

end VariationalNotes.ConvexAnalysis
