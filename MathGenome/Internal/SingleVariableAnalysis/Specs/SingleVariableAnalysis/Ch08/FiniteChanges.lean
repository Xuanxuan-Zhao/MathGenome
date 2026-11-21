import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence

/-! Independent statements for K03.08.finite_changes, paper.tex:2110–2126.
Exceptional sets need only be finite on the closed interval. Values elsewhere
are unrestricted. All integral predicates and values are the upstream Darboux
objects. The quantitative statements count closed cells, including both cells
at an internal endpoint, and include the zero-cell singleton convention. -/
namespace Specs.SingleVariableAnalysis.Ch08.FiniteChanges
open _root_.SingleVariableAnalysis.Riemann

/-- The total tagged contribution from N exceptional points is ≤ 2MN mesh. -/
def finiteSupportTaggedBound : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) {a b : ℝ} (s : Finset ℝ) (M : ℝ), 0 ≤ M →
    (∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M) →
    (∀ x ∈ Set.Icc a b, x ∉ s → h x = 0) →
    ∀ (P : PartitionData a b) (ξ : Partitions.taggingValue P),
      ‖Partitions.sumValue P ξ h‖ ≤ 2 * M * (s.card : ℝ) * Partitions.meshValue P

/-- The corresponding real Darboux gap is ≤ 4MN mesh. -/
def finiteSupportDarbouxBound : Prop :=
  ∀ (h : ℝ → ℝ) {a b : ℝ} (s : Finset ℝ) (M : ℝ), 0 ≤ M →
    (∀ x ∈ Set.Icc a b, |h x| ≤ M) →
    (∀ x ∈ Set.Icc a b, x ∉ s → h x = 0) →
    ∀ (P : PartitionData a b) (hh : DarbouxSums.boundedOnIntervalValue h a b),
      DarbouxSums.upperSumValue h P hh - DarbouxSums.lowerSumValue h P hh ≤
        4 * M * (s.card : ℝ) * Partitions.meshValue P

def realFiniteSupport : Prop :=
  ∀ (h : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    DarbouxSums.boundedOnIntervalValue h a b →
    {x | x ∈ Set.Icc a b ∧ h x ≠ 0}.Finite →
    ∃ hh : Integral.realIntegrableValue h a b, Integral.realIntegralValue h hh = 0

def complexFiniteSupport : Prop :=
  ∀ (h : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖h x‖ ≤ M) →
    {x | x ∈ Set.Icc a b ∧ h x ≠ 0}.Finite →
    ∃ hh : Integral.complexIntegrableValue h a b, Integral.complexIntegralValue h hh = 0

def realFiniteChanges : Prop :=
  ∀ (f g : ℝ → ℝ) {a b : ℝ},
    DarbouxSums.boundedOnIntervalValue f a b →
    DarbouxSums.boundedOnIntervalValue g a b →
    {x | x ∈ Set.Icc a b ∧ f x ≠ g x}.Finite →
    ∀ hf : Integral.realIntegrableValue f a b,
    ∃ hg : Integral.realIntegrableValue g a b,
      Integral.realIntegralValue g hg = Integral.realIntegralValue f hf

def complexFiniteChanges : Prop :=
  ∀ (f g : ℝ → ℂ) {a b : ℝ},
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) →
    (∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ M) →
    {x | x ∈ Set.Icc a b ∧ f x ≠ g x}.Finite →
    ∀ hf : Integral.complexIntegrableValue f a b,
    ∃ hg : Integral.complexIntegrableValue g a b,
      Integral.complexIntegralValue g hg = Integral.complexIntegralValue f hf

end Specs.SingleVariableAnalysis.Ch08.FiniteChanges
