import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import Mathlib.Topology.Sequences

/-!
Independent statements for `fa2:p1:weak-compact-sequential-density`,
paper.tex 3148–3171. The dual is the continuous scalar-linear dual for the
original norm topology. Relative weak compactness means compactness of the
weak closure. No completeness, separability, or nonemptiness is assumed.
The second statement concerns every subset of a weakly compact set with its
induced weak topology; it makes no assertion about weak-star compact sets.
-/
namespace ExpandedFA.P1.WeakCompactSequentialDensity.Spec

universe u v
open Filter
open scoped Topology

abbrev weakTopology := EberleinSmulian.Spec.weakTopology

/-- Every weak closure point is a weak sequential limit from the original set. -/
def SequentialDensity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E),
    @IsCompact E (weakTopology 𝕜 E) (@closure E (weakTopology 𝕜 E) A) →
    ∀ x ∈ @closure E (weakTopology 𝕜 E) A,
      ∃ s : ℕ → E, (∀ n, s n ∈ A) ∧
        Tendsto s atTop (@nhds E (weakTopology 𝕜 E) x)

/-- The weak subspace topology on a weakly compact set is Fréchet–Urysohn. -/
def CompactFrechetUrysohn : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (K : Set E),
    letI : TopologicalSpace E := weakTopology 𝕜 E
    IsCompact K → FrechetUrysohnSpace K

end ExpandedFA.P1.WeakCompactSequentialDensity.Spec
