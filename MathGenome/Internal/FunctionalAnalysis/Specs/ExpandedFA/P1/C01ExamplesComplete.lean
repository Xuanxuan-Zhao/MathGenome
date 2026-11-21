import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Banach
import Mathlib.Topology.ContinuousMap.Compact

/-!
Independent statements for `fa2:p1:c01:examples-complete`, paper.tex 259–265.

The sequence spaces and their norms are the canonical objects fixed by
`C01SequenceSpaces`: all extended exponents `p ≥ 1` are allowed, including
infinity, and `c₀` has the norm inherited from bounded scalar sequences.
For finite real exponents, the accepted `FiniteLpIdentification` gives exactly
the manuscript's power-sum norm. Natural coordinate `n` represents index `n+1`.

The continuous functions have their standard supremum norm. The domain may be
any compact Hausdorff space, including the empty space. Neither completeness
nor nontriviality of any of these function spaces is assumed. `RCLike` supplies
both real and complex scalars and their scalar completeness.
-/

open scoped Topology ENNReal

universe u v
namespace ExpandedFA.P1.C01ExamplesComplete.Spec
open C01SequenceSpaces

/-- Every norm Cauchy sequence in `ℓᵖ`, for every `1 ≤ p ≤ ∞`, converges in
that same norm. -/
def LpBanach : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
    C01Banach.Spec.IsBanachSpaceValue (SequenceLp 𝕜 p)

/-- The zero-limit sequences form a closed subspace of bounded sequences. -/
def C0Closed : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜))

/-- Completeness of `c₀` with its inherited supremum norm. -/
def C0Banach : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    C01Banach.Spec.IsBanachSpaceValue (SequenceC0 𝕜)

/-- Compactness makes the scalar continuous functions bounded. -/
def ContinuousFunctionsBounded : Prop :=
  ∀ (𝕜 : Type u) (K : Type v) [RCLike 𝕜] [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (f : C(K, 𝕜)),
    Bornology.IsBounded (Set.range f) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M

/-- The actual norm used for completeness is precisely the supremum norm.
The nonnegative-bound characterization includes the empty domain. -/
def SupremumNorm : Prop :=
  ∀ (𝕜 : Type u) (K : Type v) [RCLike 𝕜] [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (f : C(K, 𝕜)),
    ‖f‖ = ⨆ t : K, ‖f t‖ ∧
      ∀ M : ℝ, 0 ≤ M → (‖f‖ ≤ M ↔ ∀ t, ‖f t‖ ≤ M)

/-- Every Cauchy sequence of continuous functions converges in their
supremum norm, with no nonemptiness or metrizability assumption on K. -/
def ContinuousFunctionsBanach : Prop :=
  ∀ (𝕜 : Type u) (K : Type v) [RCLike 𝕜] [TopologicalSpace K]
    [CompactSpace K] [T2Space K],
    C01Banach.Spec.IsBanachSpaceValue C(K, 𝕜)

/-- On the empty domain the space consists only of zero, with norm zero. -/
def EmptyDomain : Prop :=
  ∀ (𝕜 : Type u) (K : Type v) [RCLike 𝕜] [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [IsEmpty K],
    ∀ f : C(K, 𝕜), f = 0 ∧ ‖f‖ = 0

end ExpandedFA.P1.C01ExamplesComplete.Spec
