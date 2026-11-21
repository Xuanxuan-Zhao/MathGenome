import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UcQuotients
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UcSums
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LurRadonRiesz

/-! Independent specification of all clauses of `fa2:p1:uc-stability`,
paper.tex:4656–4711, using the shared predicates from the definitions at
paper.tex:4613–4628. Subspaces need not be closed; quotients use the distance
norm and a closed scalar-linear subspace. The sum norm is the canonical `lp`
norm, including arbitrary index sets and the empty family. Neither completeness
nor nontriviality is assumed. -/
namespace ExpandedFA.P1.UcStability.Spec

universe u v w
open scoped ENNReal

def Subspace : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 M

def Quotient : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 E →
      letI : IsClosed (M : Set E) := hM
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E ⧸ M)

def LocallyUniformlyConvexRadonRiesz : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    RotundDefinitions.Spec.LocallyUniformlyConvexValue 𝕜 E →
      RotundDefinitions.Spec.RadonRieszValue 𝕜 E

def FiniteSum : Prop :=
  ∀ (𝕜 : Type w) {I : Type u} [Finite I] (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    (∀ i, C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E i)) →
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p)

def ArbitrarySum : Prop :=
  ∀ (𝕜 : Type w) {I : Type u} (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    (∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
      ∀ i, δ ≤ RotundDefinitions.Spec.ModulusValue 𝕜 (E i) ε) →
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p)

end ExpandedFA.P1.UcStability.Spec
