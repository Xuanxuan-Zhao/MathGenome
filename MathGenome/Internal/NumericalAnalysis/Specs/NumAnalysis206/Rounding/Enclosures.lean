import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Operations

/-! Independent statements for paper.tex W03 (lines 159–177).
The directed statements use only order and finite representability; they do not
assume the nearest-rounding relative model. Nonemptiness is required separately
on each side, so no directed endpoint is asserted beyond the finite range.
-/
namespace NumAnalysis206.Rounding.Specs

def relative_enclosure : Prop :=
  ∀ (x z u δ : ℝ), 0 ≤ u → u < 1 → |δ| ≤ u → z = x * (1 + δ) →
    min (z / (1 - u)) (z / (1 + u)) ≤ x ∧
    x ≤ max (z / (1 - u)) (z / (1 + u))

def relative_zero_exact : Prop :=
  ∀ (x z u δ : ℝ), 0 ≤ u → u < 1 → |δ| ≤ u → z = x * (1 + δ) →
    z = 0 → x = 0

def absolute_enclosure : Prop :=
  ∀ (x z η : ℝ), 0 ≤ η → |z - x| ≤ η → x ∈ Set.Icc (z - η) (z + η)

def directed_enclosure : Prop :=
  ∀ (x zdown zup : ℝ), zdown ≤ x → x ≤ zup → x ∈ Set.Icc zdown zup

/-- A lower directed choice is the greatest representable value at most x. -/
def finite_directed_lower : Prop :=
  ∀ (P : RadixFormat) (x : ℝ), {y : ℝ | y ∈ FValue P ∧ y ≤ x}.Nonempty →
    ∃ zdown : ℝ, IsGreatest {y : ℝ | y ∈ FValue P ∧ y ≤ x} zdown

/-- An upper directed choice is the least representable value at least x. -/
def finite_directed_upper : Prop :=
  ∀ (P : RadixFormat) (x : ℝ), {y : ℝ | y ∈ FValue P ∧ x ≤ y}.Nonempty →
    ∃ zup : ℝ, IsLeast {y : ℝ | y ∈ FValue P ∧ x ≤ y} zup

def finite_directed_enclosure : Prop :=
  ∀ (P : RadixFormat) (x : ℝ),
    {y : ℝ | y ∈ FValue P ∧ y ≤ x}.Nonempty →
    {y : ℝ | y ∈ FValue P ∧ x ≤ y}.Nonempty →
    ∃ zdown zup : ℝ,
      IsGreatest {y : ℝ | y ∈ FValue P ∧ y ≤ x} zdown ∧
      IsLeast {y : ℝ | y ∈ FValue P ∧ x ≤ y} zup ∧ x ∈ Set.Icc zdown zup

/-- Application at a safe exact result in the shared abstract relative model. -/
def relativeModel_enclosure : Prop :=
  ∀ (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ), RelativeModelValue round u D →
    ∀ x ∈ D,
      (min (round x / (1 - u)) (round x / (1 + u)) ≤ x ∧
       x ≤ max (round x / (1 - u)) (round x / (1 + u))) ∧
      (round x = 0 → x = 0)

end NumAnalysis206.Rounding.Specs
