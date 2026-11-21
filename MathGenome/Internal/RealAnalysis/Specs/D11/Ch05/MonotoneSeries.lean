import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.AlgebraNull

/-! Independent statements for paper.tex:1594–1635. All integrals use the
shared supremum over finite nonnegative simple minorants. The a.e. premise
uses one measurable null envelope for both successive inequalities and
convergence. Measures, spaces, and integral values are unrestricted.
Natural indices start at zero; reindexing enumerates the paper's sequence
starting at one. `ENNReal` sums include infinite values and use `0 * ∞ = 0`.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch05.MonotoneSeries

open NonnegativeIntegral
open _root_.Specs.D11.Ch04.AeCommonException
open _root_.Specs.D11.Ch01.ExhaustionRestriction

def monotone_convergence : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞) (F : X → ℝ≥0∞),
    (∀ n, Measurable (f n)) → Measurable F →
    almostEverywhere_value μ (fun x =>
      (∀ n, f n x ≤ f (n + 1) x) ∧
      Tendsto (fun n => f n x) atTop (𝓝 (F x))) →
    Monotone (fun n => nonnegativeIntegral_value μ (f n)) ∧
    nonnegativeIntegral_value μ F = ⨆ n, nonnegativeIntegral_value μ (f n) ∧
    Tendsto (fun n => nonnegativeIntegral_value μ (f n)) atTop
      (𝓝 (nonnegativeIntegral_value μ F))

def nonnegative_series : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : ℕ → X → ℝ≥0∞), (∀ n, Measurable (f n)) →
    nonnegativeIntegral_value μ (fun x => ∑' n, f n x) =
      ∑' n, nonnegativeIntegral_value μ (f n)

/-- The source's set integral is the shared integral against the ambient
restriction; upstream `restriction_indicator` and `restriction_subtype`
identify it with extension by zero and the trace-space integral. -/
def disjoint_domain_additivity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) (E : ℕ → Set X), Measurable f →
    (∀ n, MeasurableSet (E n)) →
    Pairwise (fun i j => Disjoint (E i) (E j)) →
    nonnegativeIntegral_value (restrictOnSpace_value μ (⋃ n, E n)) f =
      ∑' n, nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f

end Specs.D11.Ch05.MonotoneSeries
