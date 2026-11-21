import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BidualClosedImage
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04EvaluationContractive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualComplete
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
The completeness clause of `fa2:p1:c05:bidual-isometry`.

First derive the isometry of the actual canonical evaluation map from
the accepted norming-functional and contractive-evaluation results.
An isometry identifies completeness of the domain with completeness of
its range. The bidual is complete since it is itself a continuous dual;
in this metric space completeness of a subset is equivalent to closedness.
-/

namespace ExpandedFA.P1.BidualClosedImage

universe u v

/-- Norm preservation, without completeness, including the zero vector. -/
theorem canonicalEvaluation_norm (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ = ‖x‖ := by
  apply le_antisymm (C04EvaluationContractive.canonicalEvaluation_norm_le 𝕜 E x)
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional 𝕜 E x
  calc
    ‖x‖ = ‖f x‖ := by
      rw [hfx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ * ‖f‖ :=
      (C04CanonicalMap.canonicalEvaluation 𝕜 E x).le_opNorm f
    _ ≤ ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ * 1 :=
      mul_le_mul_of_nonneg_left hf (norm_nonneg _)
    _ = ‖C04CanonicalMap.canonicalEvaluation 𝕜 E x‖ := mul_one _

/-- The shared scalar-linear canonical map is an isometry. -/
theorem canonicalEvaluation_isometry (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Isometry (C04CanonicalMap.canonicalEvaluation 𝕜 E) :=
  AddMonoidHomClass.isometry_of_norm (C04CanonicalMap.canonicalEvaluation 𝕜 E)
    (canonicalEvaluation_norm 𝕜 E)

theorem canonicalEvaluation_closed_range_iff_banach :
    Spec.CanonicalEvaluationClosedRangeIffBanach.{u, v} := by
  intro 𝕜 E _ _ _
  change IsClosed (Set.range (C04CanonicalMap.canonicalEvaluation 𝕜 E)) ↔
    C01Banach.IsBanachSpace E
  have hJ := canonicalEvaluation_isometry 𝕜 E
  let : CompleteSpace (C04Dual.Bidual 𝕜 E) :=
    C04DualComplete.dual_completeSpace 𝕜 (C04Dual.ContinuousDual 𝕜 E)
  constructor
  · intro hclosed
    apply (C01Banach.isBanachSpace_iff_completeSpace E).mpr
    exact (completeSpace_iff_isComplete_range hJ.isUniformInducing).mpr hclosed.isComplete
  · intro hbanach
    have hcomplete : CompleteSpace E :=
      (C01Banach.isBanachSpace_iff_completeSpace E).mp hbanach
    exact ((completeSpace_iff_isComplete_range hJ.isUniformInducing).mp hcomplete).isClosed

theorem reflexive_banach : Spec.ReflexiveBanach.{u, v} := by
  intro 𝕜 E _ _ _ hreflexive
  change C04CanonicalMap.IsReflexive 𝕜 E at hreflexive
  apply (canonicalEvaluation_closed_range_iff_banach 𝕜 E).mp
  change IsClosed (Set.range (C04CanonicalMap.canonicalEvaluation 𝕜 E))
  rw [((C04CanonicalMap.isReflexive_iff_surjective 𝕜 E).mp hreflexive).range_eq]
  exact isClosed_univ

end ExpandedFA.P1.BidualClosedImage
