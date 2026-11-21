import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Unconditional

/-! Independent specification of Orlicz–Pettis, paper.tex 4259–4263.
A subseries is selected by an arbitrary set of indices, retaining the original
order and inserting zeros at omitted indices. Its limit is a vector of E and
may depend on that set. Weak convergence is expressed by all original continuous
scalar-linear dual tests. The conclusion is convergence in the displayed norm
of the finite-subset net, not merely of the ordered partial sums. -/

open Filter Topology
open scoped BigOperators
universe u v
namespace ExpandedFA.P1.OrliczPettis.Spec

/-- Every ordered subseries has a weak limit in the space itself. -/
def EveryWeakSubseries {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : ℕ → E) : Prop :=
  ∀ A : Set ℕ, ∃ u : E, ∀ f : E →L[𝕜] 𝕜,
    Tendsto (fun N => ∑ n ∈ Finset.range N, A.indicator (fun i => f (x i)) n)
      atTop (𝓝 (f u))

def OrliczPettis : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (x : ℕ → E), EveryWeakSubseries (𝕜 := 𝕜) x →
      C15Unconditional.Spec.UnconditionallyConvergentValue x

end ExpandedFA.P1.OrliczPettis.Spec
