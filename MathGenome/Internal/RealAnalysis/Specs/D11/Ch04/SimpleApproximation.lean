import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.ScalarOperationsLimits
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements for paper.tex:1290–1334. A simple scalar function
means finite range, without any support or measure assumption. The native
`SimpleFunc` bundles finite range and measurable fibers. Nonnegative simple
functions in the approximation conclusions take finite real values. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u v
namespace Specs.D11.Ch04.SimpleApproximation

def isSimple {X : Type u} {K : Type v} (f : X → K) : Prop := (Set.range f).Finite

def isNonnegativeSimple {X : Type u} (f : X → ℝ) : Prop :=
  isSimple f ∧ ∀ x, 0 ≤ f x

set_option linter.checkUnivs false in
def isSimple_type := ∀ {X : Type u} {K : Type v}, (X → K) → Prop
def isSimple_value : isSimple_type.{u,v} := fun {_} {_} f => (Set.range f).Finite

def isNonnegativeSimple_type := ∀ {X : Type u}, (X → ℝ) → Prop
def isNonnegativeSimple_value : isNonnegativeSimple_type.{u} :=
  fun {_} f => (Set.range f).Finite ∧ ∀ x, 0 ≤ f x

def measurable_iff_nonzero_levels : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [MeasurableSpace K]
    [MeasurableSingletonClass K] [Zero K] (f : X → K), isSimple f →
    (Measurable f ↔ ∀ c : K, c ≠ 0 → MeasurableSet (f ⁻¹' {c}))

def zero_level_formula : Prop :=
  ∀ {X : Type u} {K : Type v} [Zero K] (f : X → K),
    f ⁻¹' {0} = (⋃ c ∈ Set.range f \ {0}, f ⁻¹' {c})ᶜ

def measurable_zero_level : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [Zero K] (f : X → K),
    isSimple f → (∀ c : K, c ≠ 0 → MeasurableSet (f ⁻¹' {c})) →
    MeasurableSet (f ⁻¹' {0})

/-- A finite disjoint measurable indicator representation, allowing the empty
index set and zero coefficients. The scalar family includes real and complex. -/
def indicator_representation : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [MeasurableSpace K]
    [MeasurableSingletonClass K] [AddCommMonoid K]
    (f : X → K),
    (isSimple f ∧ Measurable f) ↔
    ∃ (I : Finset K) (E : K → Set X),
      (∀ c ∈ I, MeasurableSet (E c)) ∧
      (∀ c ∈ I, ∀ d ∈ I, c ≠ d → Disjoint (E c) (E d)) ∧
      ∀ x, f x = ∑ c ∈ I, (E c).indicator (fun _ => c) x

def empty_representation : Prop :=
  ∀ {X : Type u} {K : Type v} [AddCommMonoid K] (E : K → Set X) (x : X),
    (∑ c ∈ (∅ : Finset K), (E c).indicator (fun _ => c) x) = 0

def zero_coefficient : Prop :=
  ∀ {X : Type u} {K : Type v} [Zero K] (E : Set X),
    E.indicator (fun _ => (0 : K)) = fun _ => 0

def bundled_iff : Prop :=
  ∀ {X : Type u} {K : Type v} [MeasurableSpace X] [MeasurableSpace K]
    [MeasurableSingletonClass K] (f : X → K),
    (isSimple f ∧ Measurable f) ↔ ∃ s : SimpleFunc X K, (s : X → K) = f

def nonnegative_simple_iff : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℝ),
    (isNonnegativeSimple f ∧ Measurable f) ↔
      ∃ s : SimpleFunc X ℝ≥0, ∀ x, (s x : ℝ) = f x

def nonnegative_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℝ≥0∞), Measurable f →
    ∃ s : ℕ → SimpleFunc X ℝ,
      (∀ n x, 0 ≤ s n x) ∧
      (∀ x, Monotone (fun n => s n x)) ∧
      (∀ n x, ENNReal.ofReal (s n x) ≤ f x) ∧
      ∀ x, Tendsto (fun n => ENNReal.ofReal (s n x)) atTop (𝓝 (f x))

/-- `max a (-a)` is the absolute value in the extended real order, including
absolute value infinity at either endpoint. -/
def extended_real_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → EReal), Measurable f →
    ∃ s : ℕ → SimpleFunc X ℝ,
      (∀ n x, |s n x| ≤ |s (n+1) x|) ∧
      (∀ n x, ((|s n x| : ℝ) : EReal) ≤ max (f x) (-f x)) ∧
      ∀ x, Tendsto (fun n => (s n x : EReal)) atTop (𝓝 (f x))

def real_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℝ), Measurable f →
    ∃ s : ℕ → SimpleFunc X ℝ,
      (∀ n x, |s n x| ≤ |s (n+1) x|) ∧
      (∀ n x, |s n x| ≤ |f x|) ∧
      ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x))

def bounded_real_uniform_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℝ), Measurable f →
    (∃ B : ℝ, ∀ x, |f x| ≤ B) →
    ∃ s : ℕ → SimpleFunc X ℝ,
      (∀ n x, |s n x| ≤ |s (n+1) x|) ∧
      (∀ n x, |s n x| ≤ |f x|) ∧
      TendstoUniformly (fun n x => s n x) f atTop

def complex_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℂ), Measurable f →
    ∃ s : ℕ → SimpleFunc X ℂ, ∀ x,
      Tendsto (fun n => s n x) atTop (𝓝 (f x))

def bounded_complex_uniform_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (f : X → ℂ), Measurable f →
    (∃ B : ℝ, ∀ x, ‖f x‖ ≤ B) →
    ∃ s : ℕ → SimpleFunc X ℂ, TendstoUniformly (fun n x => s n x) f atTop

end Specs.D11.Ch04.SimpleApproximation
