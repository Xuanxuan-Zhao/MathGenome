import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14ReflexiveExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14MilmanPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UcExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.NonreflexiveSequenceSpaces

/-! The reflexive and nonreflexive examples of paper.tex:2960–2965.
Completeness and uniform convexity give the positive claims by Milman–Pettis.
The endpoint claims reuse the canonical-bidual and weak-subsequence obstructions
proved for the same shared sequence spaces.
-/

noncomputable section
open scoped ENNReal

namespace ExpandedFA.P1.C14ReflexiveExamples
universe u v

theorem hilbert_reflexive : Spec.HilbertReflexive.{u,v} := by
  intro 𝕜 H _ _ _ _
  exact C14MilmanPettis.milman_pettis 𝕜 H
    (C14UcExamples.hilbert_uniformly_convex 𝕜 H)

theorem measure_lp_reflexive : Spec.MeasureLpReflexive.{u,v} := by
  intro 𝕜 _ X _ μ p hp
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  letI := FunctionSpaces.bochnerLp_complete (E := 𝕜) (ENNReal.ofReal p) μ
  exact C14MilmanPettis.milman_pettis 𝕜 _
    (C14UcExamples.lp_uniformly_convex 𝕜 X μ p hp)

theorem c0_not_reflexive : Spec.C0Nonreflexive.{u} :=
  NonreflexiveSequenceSpaces.c0_not_reflexive

theorem l1_not_reflexive : Spec.L1Nonreflexive.{u} :=
  NonreflexiveSequenceSpaces.l1_not_reflexive

theorem linfty_not_reflexive : Spec.LInfinityNonreflexive.{u} :=
  NonreflexiveSequenceSpaces.linfty_not_reflexive

end ExpandedFA.P1.C14ReflexiveExamples
