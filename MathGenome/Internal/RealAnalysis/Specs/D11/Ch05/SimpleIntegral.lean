import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.SimpleApproximation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.MeasureDefinitions

/-! Independent specification of paper.tex:1488–1526. `ℝ≥0` consists of
finite nonnegative real numbers; the upstream `nonnegative_simple_iff`
identifies the bundled domain below with precisely the paper's measurable
nonnegative simple functions. No restriction on support or total mass occurs.
All products and sums of integral values use `ℝ≥0∞`, including `0 * ∞ = 0`.
-/
open Set MeasureTheory
open scoped ENNReal NNReal
universe u v w
noncomputable section
namespace Specs.D11.Ch05.SimpleIntegral

def simpleIntegral_type :=
  ∀ {X : Type u} [MeasurableSpace X], Measure X → SimpleFunc X ℝ≥0 → ℝ≥0∞

def simpleIntegral_value : simpleIntegral_type.{u} :=
  fun μ s => (s.map (fun a : ℝ≥0 => (a : ℝ≥0∞))).lintegral μ

def level_formula : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (s : SimpleFunc X ℝ≥0),
    simpleIntegral_value μ s = ∑ a ∈ s.range, (a : ℝ≥0∞) * μ (s ⁻¹' {a})

/-- The literal real-coefficient formula, with a finite, possibly empty,
disjoint measurable family. The family need not cover the space. -/
def representation_formula : Prop :=
  ∀ {X : Type u} {ι : Type v} [MeasurableSpace X] (μ : Measure X)
    (s : SimpleFunc X ℝ≥0) (I : Finset ι) (a : ι → ℝ) (E : ι → Set X),
    (∀ i ∈ I, 0 ≤ a i) → (∀ i ∈ I, MeasurableSet (E i)) →
    (↑I : Set ι).PairwiseDisjoint E →
    (∀ x, (s x : ℝ) = ∑ i ∈ I, (E i).indicator (fun _ => a i) x) →
    simpleIntegral_value μ s = ∑ i ∈ I, ENNReal.ofReal (a i) * μ (E i)

/-- Equality of represented functions gives equality of the two sums, even
with repeated coefficients, empty levels, or infinite-measure levels. -/
def representation_independent : Prop :=
  ∀ {X : Type u} {ι : Type v} {κ : Type w} [MeasurableSpace X] (μ : Measure X)
    (I : Finset ι) (J : Finset κ) (a : ι → ℝ≥0) (b : κ → ℝ≥0)
    (E : ι → Set X) (F : κ → Set X),
    (∀ i ∈ I, MeasurableSet (E i)) → (∀ j ∈ J, MeasurableSet (F j)) →
    (↑I : Set ι).PairwiseDisjoint E → (↑J : Set κ).PairwiseDisjoint F →
    (∀ x, (∑ i ∈ I, (E i).indicator (fun _ => a i) x) =
      ∑ j ∈ J, (F j).indicator (fun _ => b j) x) →
    (∑ i ∈ I, (a i : ℝ≥0∞) * μ (E i)) =
      ∑ j ∈ J, (b j : ℝ≥0∞) * μ (F j)

def homogeneity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (s : SimpleFunc X ℝ≥0)
    (a : ℝ≥0),
    simpleIntegral_value μ (SimpleFunc.const X a * s) =
      (a : ℝ≥0∞) * simpleIntegral_value μ s

def additivity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (s t : SimpleFunc X ℝ≥0),
    simpleIntegral_value μ (s + t) = simpleIntegral_value μ s + simpleIntegral_value μ t

def monotonicity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (s t : SimpleFunc X ℝ≥0),
    (∀ x, s x ≤ t x) → simpleIntegral_value μ s ≤ simpleIntegral_value μ t

def zero_integral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X),
    simpleIntegral_value μ (0 : SimpleFunc X ℝ≥0) = 0

def indicator_integral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (a : ℝ≥0)
    (E : Set X), MeasurableSet E →
    simpleIntegral_value μ ((SimpleFunc.const X a).restrict E) = (a : ℝ≥0∞) * μ E

end Specs.D11.Ch05.SimpleIntegral
