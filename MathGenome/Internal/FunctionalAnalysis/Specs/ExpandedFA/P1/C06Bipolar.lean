import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Polars

/-! Independent statements for the elementary identities of `fa2:p1:c06:bipolar`,
paper.tex 1186–1213. All sets are arbitrary and closures are in norm. The
zero-inclusive hull and the continuous scalar-linear dual are the shared ones.
Positive real dilations act through their canonical image in the scalar field.
No completeness, boundedness, nonemptiness, or nonzero-space hypothesis occurs. -/

namespace ExpandedFA.P1.C06Bipolar.Spec

universe u v w
open scoped Pointwise
open C06Polars.Spec

def PolarAntitone : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A C : Set E),
    A ⊆ C → PolarValue 𝕜 E C ⊆ PolarValue 𝕜 E A

def PrepolarAntitone : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (B D : Set (E →L[𝕜] 𝕜)),
    B ⊆ D → PrepolarValue 𝕜 E D ⊆ PrepolarValue 𝕜 E B

/-- Arbitrary indexed unions, including the empty family. -/
def PolarUnion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : Type w) (A : I → Set E),
    PolarValue 𝕜 E (⋃ i, A i) = ⋂ i, PolarValue 𝕜 E (A i)

def PrepolarUnion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : Type w) (B : I → Set (E →L[𝕜] 𝕜)),
    PrepolarValue 𝕜 E (⋃ i, B i) = ⋂ i, PrepolarValue 𝕜 E (B i)

def PolarClosedHull : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    PolarValue 𝕜 E (ClosedAbsolutelyConvexHullValue 𝕜 E A) = PolarValue 𝕜 E A

def PrepolarClosedHull : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (B : Set (E →L[𝕜] 𝕜)),
    PrepolarValue 𝕜 E (ClosedAbsolutelyConvexHullValue 𝕜 (E →L[𝕜] 𝕜) B) =
      PrepolarValue 𝕜 E B

def PolarScaling : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E)
    (r : ℝ), 0 < r →
    PolarValue 𝕜 E ((r : 𝕜) • A) = (r : 𝕜)⁻¹ • PolarValue 𝕜 E A

def PrepolarScaling : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (B : Set (E →L[𝕜] 𝕜))
    (r : ℝ), 0 < r →
    PrepolarValue 𝕜 E ((r : 𝕜) • B) = (r : 𝕜)⁻¹ • PrepolarValue 𝕜 E B

def PolarClosedUnitBall : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    PolarValue 𝕜 E (Metric.closedBall (0 : E) 1) =
      Metric.closedBall (0 : E →L[𝕜] 𝕜) 1

def BipolarTheorem : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    PrepolarValue 𝕜 E (PolarValue 𝕜 E A) = ClosedAbsolutelyConvexHullValue 𝕜 E A

end ExpandedFA.P1.C06Bipolar.Spec
