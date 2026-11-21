import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements for paper.tex:1903–1949. All functions are finite
real or complex scalars, measurable on the original sigma-algebra. The absolute
integral is the shared nonnegative integral. Its convergence is in ℝ≥0∞;
all these error integrals are finite by the integrability conclusions.
No completeness or sigma-finiteness of the measure is assumed. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch06.DominatedConvergence
open ScalarIntegral
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch04.AeCommonException

/-- The full common conclusion, including integrability before scalar evaluation. -/
def convergenceConclusions {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ℕ → X → 𝕜) (f : X → 𝕜) : Prop :=
  ∃ (hF : ∀ n, scalarIntegrable_value μ (F n)) (hf : scalarIntegrable_value μ f),
    (∀ n, scalarIntegrable_value μ (fun x => ‖F n x - f x‖)) ∧
    Tendsto (fun n => nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖F n x - f x‖))
      atTop (𝓝 0) ∧
    Tendsto (fun n => scalarIntegral_value μ (F n) (hF n))
      atTop (𝓝 (scalarIntegral_value μ f hf))

/-- Dominated convergence on an arbitrary positive measure space. -/
def dominated_convergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (g : X → ℝ),
    (∀ n, Measurable (F n)) → Measurable f → scalarIntegrable_value μ g →
    (∀ x, 0 ≤ g x) →
    (∀ n, almostEverywhere_value μ (fun x => ‖F n x‖ ≤ g x)) →
    almostEverywhere_value μ (fun x => Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    convergenceConclusions μ F f

/-- A common finite real bound on a finite-measure space; the bound need not
be strictly positive, so null spaces and the zero bound are included. -/
def bounded_convergence : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (M : ℝ),
    μ univ < ∞ → (∀ n, Measurable (F n)) → Measurable f →
    (∀ n, almostEverywhere_value μ (fun x => ‖F n x‖ ≤ M)) →
    almostEverywhere_value μ (fun x => Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    convergenceConclusions μ F f

/-- The fixed support version allows arbitrary mass outside E. No pointwise
support condition is imposed on the limit at exceptional null points. -/
def bounded_convergence_fixed_support : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (F : ℕ → X → 𝕜)
    (f : X → 𝕜) (E : Set X) (M : ℝ),
    MeasurableSet E → μ E < ∞ → (∀ n, Measurable (F n)) → Measurable f →
    (∀ n x, x ∉ E → F n x = 0) →
    (∀ n, almostEverywhere_value μ (fun x => ‖F n x‖ ≤ M)) →
    almostEverywhere_value μ (fun x => Tendsto (fun n => F n x) atTop (𝓝 (f x))) →
    convergenceConclusions μ F f

end Specs.D11.Ch06.DominatedConvergence
