import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.SchauderAdjoints

/-!
Independent specifications for `fa2:p2:schauder-adjoint`, paper.tex:9458–9487.
The new sequence assertion has the prescribed limit T x, and uses the original
norm-continuous scalar-linear dual over either ℝ or ℂ. It holds even without
completeness. The final statement assembles the whole source theorem for Banach
spaces. No assertion of continuity from the whole weak topology to the norm
topology is made. Zero spaces and constant sequences are included.
-/
namespace ExpandedFA.Compactness.CompactWeakSequences.Spec

universe u v w z
open Filter
open scoped Topology
open DefinitionsSpec

/-- Compactness implies the scalar-test definition of complete continuity. -/
def CompactCompletelyContinuous : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y),
    IsCompactLinearMapValue T.toLinearMap → IsCompletelyContinuousValue T

/-- Equivalent formulation in the shared weak topology σ(X,X'). -/
def CompactWeakToNorm : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y),
    IsCompactLinearMapValue T.toLinearMap →
    ∀ (s : ℕ → X) (x : X),
      Tendsto s atTop (@nhds X (P1.C12DualPairSpec.DualPairTopologyValue
        𝕜 X (X →L[𝕜] 𝕜) (topDualPairing 𝕜 X)) x) →
      Tendsto (fun n => T (s n)) atTop (𝓝 (T x))

/-- The closed linear space, two-sided ideal, transpose equivalence, and
sequential weak-to-norm property, under the chapter's Banach conventions. -/
def SchauderAndCompactIdeal : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y],
    (∃ M : Submodule 𝕜 (X →L[𝕜] Y), IsClosed (M : Set (X →L[𝕜] Y)) ∧
      ∀ T : X →L[𝕜] Y, T ∈ M ↔ IsCompactLinearMapValue T.toLinearMap) ∧
    (∀ T : X →L[𝕜] Y,
      (IsCompactLinearMapValue T.toLinearMap ↔ IsCompactLinearMapValue
        (P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 X Y T).toLinearMap) ∧
      (IsCompactLinearMapValue T.toLinearMap → IsCompletelyContinuousValue T)) ∧
    (∀ (Z : Type z) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
      (T : X →L[𝕜] Y), IsCompactLinearMapValue T.toLinearMap →
      (∀ A : Z →L[𝕜] X, IsCompactLinearMapValue (T.comp A).toLinearMap) ∧
      (∀ B : Y →L[𝕜] Z, IsCompactLinearMapValue (B.comp T).toLinearMap))

end ExpandedFA.Compactness.CompactWeakSequences.Spec
