import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.SimpleIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-! Independent specification for paper.tex:1523–1552.
The canonical integral is the supremum of the earlier simple integral over
finite nonnegative real simple minorants. `ℝ≥0` has no infinite element;
upstream `nonnegative_simple_iff` identifies this domain with all measurable
nonnegative real simple functions. The definition also gives a lower integral
on arbitrary functions; the source conclusions below concern measurable inputs.
No assumption on total mass, support, sigma-finiteness, or completeness is made.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
universe u
noncomputable section
namespace Specs.D11.Ch05.NonnegativeIntegral

def nonnegativeIntegral_type :=
  ∀ {X : Type u} [MeasurableSpace X], Measure X → (X → ℝ≥0∞) → ℝ≥0∞

def nonnegativeIntegral_value : nonnegativeIntegral_type.{u} :=
  fun μ f => ⨆ (s : SimpleFunc _ ℝ≥0) (_ : ∀ x, (s x : ℝ≥0∞) ≤ f x),
    SimpleIntegral.simpleIntegral_value μ s

/-- The same supremum written literally as the supremum of a set of values. -/
def finite_simple_supremum : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → nonnegativeIntegral_value μ f =
      sSup {a | ∃ s : SimpleFunc X ℝ≥0,
        (∀ x, (s x : ℝ≥0∞) ≤ f x) ∧ SimpleIntegral.simpleIntegral_value μ s = a}

/-- Explicit bridge to the library integral, whose defining simple functions
may take the value infinity. This is a theorem, not an assumed identification. -/
def eq_lintegral : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → nonnegativeIntegral_value μ f = ∫⁻ x, f x ∂μ

/-- A version with ordinary real-valued simple functions and an explicit
nonnegativity hypothesis. `toNNReal` is exact on these coefficients. -/
def finite_real_supremum : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → nonnegativeIntegral_value μ f =
      ⨆ (s : SimpleFunc X ℝ) (_ : ∀ x, 0 ≤ s x)
        (_ : ∀ x, ENNReal.ofReal (s x) ≤ f x),
        SimpleIntegral.simpleIntegral_value μ (s.map Real.toNNReal)

def simple_agreement : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (s : SimpleFunc X ℝ≥0),
    nonnegativeIntegral_value μ (fun x => (s x : ℝ≥0∞)) =
      SimpleIntegral.simpleIntegral_value μ s

/-- Every increasing simple approximation has this limit, including when
its integral or the total measure is infinite. -/
def increasing_simple_approximation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → ∀ s : ℕ → SimpleFunc X ℝ≥0,
    (∀ x, Monotone (fun n => s n x)) →
    (∀ x, Tendsto (fun n => (s n x : ℝ≥0∞)) atTop (𝓝 (f x))) →
    Monotone (fun n => SimpleIntegral.simpleIntegral_value μ (s n)) ∧
      nonnegativeIntegral_value μ f = ⨆ n, SimpleIntegral.simpleIntegral_value μ (s n) ∧
      Tendsto (fun n => SimpleIntegral.simpleIntegral_value μ (s n)) atTop
        (𝓝 (nonnegativeIntegral_value μ f))

end Specs.D11.Ch05.NonnegativeIntegral
