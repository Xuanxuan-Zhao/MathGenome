import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence

/-! Independent specifications for K03.08.cauchy, paper.tex:1998–2014.
Both partitions and both closed-cell taggings are arbitrary, subject only to
the same positive mesh threshold. Scalars are exactly the canonical real and
complex fields. Ordered intervals include the empty-sum singleton convention.
The value assertions use the existing proper Darboux integral and establish
integrability, rather than assuming it as a completeness certificate. -/

namespace Specs.SingleVariableAnalysis.Ch08.Cauchy
open _root_.SingleVariableAnalysis.Riemann

abbrev taggedCauchyType := {E : Type} → [NormedAddCommGroup E] → [Module ℝ E] →
  (ℝ → E) → ℝ → ℝ → Prop

def taggedCauchyValue : taggedCauchyType := fun {_} _ _ f a b =>
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ (P : PartitionData a b) (ξ : Partitions.taggingValue P)
      (Q : PartitionData a b) (ζ : Partitions.taggingValue Q),
      Partitions.meshValue P < δ → Partitions.meshValue Q < δ →
        ‖Partitions.sumValue P ξ f - Partitions.sumValue Q ζ f‖ < ε

def realCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b →
    ((∃ I : ℝ, FineTaggedLimit f a b I) ↔ taggedCauchyValue f a b)

def complexCauchyCriterion : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) →
    ((∃ I : ℂ, FineTaggedLimit f a b I) ↔ taggedCauchyValue f a b)

/-- The Cauchy condition produces proper integrability and its value is the
common limit; every other claimed fine-mesh limit has that same value. -/
def realCauchyIntegral : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue f a b → taggedCauchyValue f a b →
    ∃ hi : Integral.realIntegrableValue f a b,
      FineTaggedLimit f a b (Integral.realIntegralValue f hi) ∧
      ∀ I : ℝ, FineTaggedLimit f a b I → Integral.realIntegralValue f hi = I

def complexCauchyIntegral : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) → taggedCauchyValue f a b →
    ∃ hi : Integral.complexIntegrableValue f a b,
      FineTaggedLimit f a b (Integral.complexIntegralValue f hi) ∧
      ∀ I : ℂ, FineTaggedLimit f a b I → Integral.complexIntegralValue f hi = I

end Specs.SingleVariableAnalysis.Ch08.Cauchy
