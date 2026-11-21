import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.BanachAdjoints

/-!
Independent statements for the transpose clause of `fa2:p2:schauder-adjoint`,
paper.tex:9458–9485. Compact closure is in the original normed target;
the transpose is the shared continuous scalar-linear Banach transpose.
These statements include all real/complex Banach spaces and zero spaces.
The forward theorem needs no completeness, and completeness of the target
alone suffices for the converse. No reflexivity or approximation property
is assumed.
-/
namespace ExpandedFA.Compactness.SchauderAdjoints.Spec

universe u v w

open DefinitionsSpec
open P1.C04Annihilators.Spec (BanachTransposeValue)

def Forward : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] (T : X →L[𝕜] Y),
    IsCompactLinearMapValue T.toLinearMap →
      IsCompactLinearMapValue (BanachTransposeValue 𝕜 X Y T).toLinearMap

def Converse : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace Y] (T : X →L[𝕜] Y),
    IsCompactLinearMapValue (BanachTransposeValue 𝕜 X Y T).toLinearMap →
      IsCompactLinearMapValue T.toLinearMap

def Equivalence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace Y] (T : X →L[𝕜] Y),
    IsCompactLinearMapValue T.toLinearMap ↔
      IsCompactLinearMapValue (BanachTransposeValue 𝕜 X Y T).toLinearMap

end ExpandedFA.Compactness.SchauderAdjoints.Spec
