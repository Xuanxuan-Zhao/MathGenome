import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakSequentialRelativeCompact
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakClusterToSubsequence
import Mathlib.Topology.Compactness.CountablyCompact

/-!
Independent statements for `fa2:p1:eberlein-smulian`, paper.tex 3077–3153.
The continuous linear dual and all algebraic structures are formed with the
original norm topology. Compactness, closedness, convergence and cluster points
below use its weak topology. Limits in the relative statements may lie anywhere
in E. No completeness or nonemptiness is assumed.
-/
namespace ExpandedFA.P1.EberleinSmulian.Spec

universe u v
open Filter
open scoped Topology

abbrev weakTopology := WeakSequentialRelativeCompact.Spec.weakTopology
abbrev HasWeaklyConvergentSubsequences :=
  WeakSequentialRelativeCompact.Spec.HasWeaklyConvergentSubsequences

/-- Every sequence in A has a cluster point in the ambient weak space. -/
def HasWeakClusterPoints (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E) : Prop :=
  ∀ s : ℕ → E, (∀ n, s n ∈ A) → ∃ x : E,
    @ClusterPt E (weakTopology 𝕜 E) x (map s atTop)

def CompactImpliesSubsequences : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    @IsCompact E (weakTopology 𝕜 E) (@closure E (weakTopology 𝕜 E) A) →
      HasWeaklyConvergentSubsequences 𝕜 E A

/-- The three relative conditions of Eberlein–Šmulian. -/
def RelativeEquivalences : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    (@IsCompact E (weakTopology 𝕜 E) (@closure E (weakTopology 𝕜 E) A) ↔
      HasWeaklyConvergentSubsequences 𝕜 E A) ∧
    (HasWeaklyConvergentSubsequences 𝕜 E A ↔ HasWeakClusterPoints 𝕜 E A)

/-- On a weakly closed set, compactness, sequential compactness and countable
compactness agree; these are the usual set predicates in the weak topology. -/
def ClosedEquivalences : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    letI : TopologicalSpace E := weakTopology 𝕜 E
    IsClosed A → (IsCompact A ↔ IsSeqCompact A) ∧
      (IsCompact A ↔ IsCountablyCompact A)

/-- Relative countable compactness means countable compactness of the weak
closure, exactly as in the final sentence of the source theorem. -/
def RelativeCountableEquivalence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    letI : TopologicalSpace E := weakTopology 𝕜 E
    IsCompact (closure A) ↔ IsCountablyCompact (closure A)

end ExpandedFA.P1.EberleinSmulian.Spec
