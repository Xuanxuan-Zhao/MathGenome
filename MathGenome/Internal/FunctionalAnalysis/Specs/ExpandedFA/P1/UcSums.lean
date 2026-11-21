import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.RotundDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.BanachSumDefinitions

/-! Independent statements of the sum clauses of `fa2:p1:uc-stability`,
paper.tex:4656–4711. The sum is the canonical dependent `lp`, whose norm
is identified with finite-subset power suprema by BanachSumDefinitions.
No completeness, nontriviality, or nonemptiness is assumed. -/
noncomputable section
open scoped ENNReal
universe u v w
namespace ExpandedFA.P1.UcSums.Spec

/-- A strictly positive common lower bound at every relevant positive argument.
The modulus has the upstream empty-pair convention, including zero summands. -/
def CommonModulus (𝕜 : Type w) {I : Type u} (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
    ∀ i, δ ≤ RotundDefinitions.Spec.ModulusValue 𝕜 (E i) ε

def ArbitrarySum : Prop :=
  ∀ (𝕜 : Type w) {I : Type u} (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ → CommonModulus 𝕜 E →
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p)

def FiniteSum : Prop :=
  ∀ (𝕜 : Type w) {I : Type u} [Finite I] (E : I → Type v)
    [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    (∀ i, C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E i)) →
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p)

end ExpandedFA.P1.UcSums.Spec
