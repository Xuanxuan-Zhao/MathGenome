import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedForward
import Mathlib.Analysis.Complex.Basic

/-! Independent statements for K03.08.tagged_equivalence (paper.tex:1967–2001).
The limit quantifies over every finite strict partition and every closed-cell
tagging, with only a mesh restriction. Integral values are the existing Darboux
values. Ordered intervals include the singleton, whose sums are empty.
Complex boundedness is a bound on the usual modulus, not an order on ℂ. -/

namespace SingleVariableAnalysis.Riemann

/-- Convergence of all tagged sums as their mesh tends to zero. -/
def FineTaggedLimit {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (f : ℝ → E) (a b : ℝ) (I : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (P : PartitionData a b) (ξ : Specs.SingleVariableAnalysis.Ch08.Partitions.taggingValue P),
      Specs.SingleVariableAnalysis.Ch08.Partitions.meshValue P < δ →
        ‖Specs.SingleVariableAnalysis.Ch08.Partitions.sumValue P ξ f - I‖ < ε

end SingleVariableAnalysis.Riemann

namespace Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence
open _root_.SingleVariableAnalysis.Riemann

def realTaggedEquivalence : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b → ∀ I : ℝ,
    (∃ hi : Integral.realIntegrableValue f a b, Integral.realIntegralValue f hi = I) ↔
      FineTaggedLimit f a b I

def complexTaggedComponentwise : Prop :=
  ∀ (f : ℝ → ℂ) (a b : ℝ) (I : ℂ),
    FineTaggedLimit f a b I ↔
      FineTaggedLimit (fun x => (f x).re) a b I.re ∧
      FineTaggedLimit (fun x => (f x).im) a b I.im

def complexTaggedEquivalence : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) → ∀ I : ℂ,
    (∃ hi : Integral.complexIntegrableValue f a b, Integral.complexIntegralValue f hi = I) ↔
      FineTaggedLimit f a b I

/-- On a singleton every tagged sum is the empty sum, so its only limit is zero.
This applies in particular to both scalar choices without any boundedness premise. -/
def degenerateTaggedLimit : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [Module ℝ E]
    (f : ℝ → E) (a : ℝ) (I : E), FineTaggedLimit f a a I ↔ I = 0

end Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence
