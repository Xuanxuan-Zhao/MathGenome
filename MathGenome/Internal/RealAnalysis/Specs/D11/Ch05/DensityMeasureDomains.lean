import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Continuity

/-! Independent statements for paper.tex:1687–1703 and 1732–1743.
The density measure lives on precisely the given measurable space. Its
prescription on measurable sets uses the shared source integral and restriction.
The native construction also accepts arbitrary densities; all source conclusions
below retain the source hypothesis that the density is measurable. No finite,
sigma-finite, completeness, or nonemptiness hypothesis is imposed.
The arrows in domain continuity include monotonicity, the supremum/infimum
identity, and convergence in the extended nonnegative real topology.
-/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace Specs.D11.Ch05.DensityMeasureDomains

open NonnegativeIntegral
open Specs.D11.Ch01.ExhaustionRestriction

def densityMeasure_type :=
  ∀ {X : Type u} [MeasurableSpace X], Measure X → (X → ℝ≥0∞) → Measure X

def densityMeasure_value : densityMeasure_type.{u} := fun μ h => μ.withDensity h

/-- Evaluation is asserted on the original sigma-algebra, without completing it. -/
def densityMeasure_apply : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ≥0∞),
    Measurable h → ∀ E : Set X, MeasurableSet E →
      densityMeasure_value μ h E = nonnegativeIntegral_value (restrictOnSpace_value μ E) h

def densityMeasure_mass : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ≥0∞),
    Measurable h → densityMeasure_value μ h univ = nonnegativeIntegral_value μ h

def densityMeasure_finite : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ≥0∞),
    Measurable h → nonnegativeIntegral_value μ h < ∞ →
      IsFiniteMeasure (densityMeasure_value μ h)

def densityMeasure_null : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ≥0∞),
    Measurable h → ∀ N : Set X, MeasurableSet N → μ N = 0 →
      densityMeasure_value μ h N = 0

/-- The countable additivity of the prescription itself, including infinite
integrals. The measure type already includes the empty-set axiom. -/
def densityMeasure_countable_additivity : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (h : X → ℝ≥0∞),
    Measurable h → ∀ E : ℕ → Set X, (∀ n, MeasurableSet (E n)) →
      Pairwise (fun i j => Disjoint (E i) (E j)) →
      nonnegativeIntegral_value (restrictOnSpace_value μ (⋃ n, E n)) h =
        ∑' n, nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) h

def domain_continuity_from_below : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → ∀ (E : ℕ → Set X) (s : Set X),
      (∀ n, MeasurableSet (E n)) → Monotone E → (⋃ n, E n) = s →
      Monotone (fun n => nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f) ∧
      (⨆ n, nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f) =
        nonnegativeIntegral_value (restrictOnSpace_value μ s) f ∧
      Tendsto (fun n => nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f)
        atTop (𝓝 (nonnegativeIntegral_value (restrictOnSpace_value μ s) f))

def domain_continuity_from_above : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ≥0∞),
    Measurable f → ∀ (E : ℕ → Set X) (s : Set X),
      (∀ n, MeasurableSet (E n)) → Antitone E → (⋂ n, E n) = s →
      (∃ N, nonnegativeIntegral_value (restrictOnSpace_value μ (E N)) f < ∞) →
      Antitone (fun n => nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f) ∧
      (⨅ n, nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f) =
        nonnegativeIntegral_value (restrictOnSpace_value μ s) f ∧
      Tendsto (fun n => nonnegativeIntegral_value (restrictOnSpace_value μ (E n)) f)
        atTop (𝓝 (nonnegativeIntegral_value (restrictOnSpace_value μ s) f))

end Specs.D11.Ch05.DensityMeasureDomains
