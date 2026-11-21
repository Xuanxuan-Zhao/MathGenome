import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.StrongRotundityCriteria
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap

/-! Slices and minimizing sequences, paper.tex:4865–4920.
Strong rotundity refers to the actual given norm. Convex sets need not be
closed. Convergence of minimizing sequences is in the ambient Banach space;
no membership of the limit in a nonclosed set is asserted. Reflexivity means
surjectivity of canonical evaluation and already forces completeness. -/
namespace ExpandedFA.P1.StrongRotundity.Spec
universe u v
open Filter
open scoped Topology
noncomputable section

def StrongRotundType := RotundDefinitions.Spec.PredicateType.{u,v}
def StrongRotundValue : StrongRotundType.{u,v} :=
  StrongRotundityCriteria.Spec.ShrinkingSlices

def Criteria : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    (StrongRotundValue 𝕜 E ↔ StrongRotundityCriteria.Spec.UnitMaximizersCauchy 𝕜 E) ∧
    (StrongRotundValue 𝕜 E ↔ StrongRotundityCriteria.Spec.MinimizersCauchy 𝕜 E)

def StrictConvexity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    StrongRotundValue 𝕜 E → RotundDefinitions.Spec.RotundValue 𝕜 E

def RadonRiesz : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    StrongRotundValue 𝕜 E → RotundDefinitions.Spec.RadonRieszValue 𝕜 E

def BanachMinimizersConverge : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    StrongRotundValue 𝕜 E →
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    ∀ (C : Set E), C.Nonempty → Convex ℝ C → ∀ (p : E) (x : ℕ → E),
      (∀ n, x n ∈ C) →
      Tendsto (fun n => dist (x n) p) atTop (𝓝 (Metric.infDist p C)) →
      ∃ z : E, Tendsto x atTop (𝓝 z)

def ReflexiveConverse : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    RotundDefinitions.Spec.RotundValue 𝕜 E →
    RotundDefinitions.Spec.RadonRieszValue 𝕜 E → StrongRotundValue 𝕜 E

def ReflexiveLocallyUniformlyConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E →
    RotundDefinitions.Spec.LocallyUniformlyConvexValue 𝕜 E → StrongRotundValue 𝕜 E
end
end ExpandedFA.P1.StrongRotundity.Spec
