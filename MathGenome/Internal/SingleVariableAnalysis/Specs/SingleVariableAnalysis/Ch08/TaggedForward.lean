import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral

/-! The forward real-valued part of K03.08.tagged_equivalence,
paper.tex:1967–1986. The mesh threshold applies to every partition and
every choice of closed-cell tags, without a refinement condition. -/
namespace Specs.SingleVariableAnalysis.Ch08.TaggedForward

open _root_.SingleVariableAnalysis.Riemann

def taggedForward : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ} (_hab : a < b)
    (hf : DarbouxSums.boundedOnIntervalValue f a b)
    (hi : Integral.realIntegrableValue f a b) (I : ℝ),
    Integral.realIntegralValue f hi = I →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (Q : PartitionData a b) (ξ : Partitions.taggingValue Q),
        Partitions.meshValue Q < δ → |Partitions.sumValue Q ξ f - I| < ε

end Specs.SingleVariableAnalysis.Ch08.TaggedForward
