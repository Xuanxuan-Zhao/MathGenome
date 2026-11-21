import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.GantmacherCriterion

/-! Gantmacher's theorem, paper.tex 9573–9600. The standing assumption at
9427 is that the spaces are Banach over ℝ or ℂ. The weak compactness predicate
uses compact weak closure of the unit-ball image, with the original continuous
scalar-linear dual. Closedness below uses the operator norm topology. -/
namespace ExpandedFA.Compactness.GantmacherAdjointIdeal.Spec
universe u v w z
noncomputable section
open GantmacherCriterion.Spec

abbrev WC := @DefinitionsSpec.IsWeaklyCompactOperatorValue
abbrev transpose := P1.C04Annihilators.Spec.BanachTransposeValue

def GantmacherEquivalences : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y),
    (WC T ↔ BidualRange 𝕜 X Y T) ∧
    (WC T ↔ Continuous (fun f : WeakDual 𝕜 Y => toWeakSpace 𝕜 (X →L[𝕜] 𝕜)
      (transpose 𝕜 X Y T (WeakDual.toStrongDual f))))

def AdjointEquivalence : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[𝕜] Y), WC T ↔ WC (transpose 𝕜 X Y T)

def LinearSpace : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y],
    WC (0 : X →L[𝕜] Y) ∧
    (∀ S T : X →L[𝕜] Y, WC S → WC T → WC (S + T)) ∧
    (∀ (a : 𝕜) (T : X →L[𝕜] Y), WC T → WC (a • T))

def NormClosed : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X] [CompleteSpace Y],
    IsClosed {T : X →L[𝕜] Y | WC T}

def TwoSidedIdeal : Prop :=
  ∀ (𝕜 : Type u) (X : Type v) (Y : Type w) (Z : Type z) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]
    [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
    (T : X →L[𝕜] Y), WC T →
    (∀ A : Y →L[𝕜] Z, WC (A.comp T)) ∧
    (∀ B : Z →L[𝕜] X, WC (T.comp B))

end
end ExpandedFA.Compactness.GantmacherAdjointIdeal.Spec
