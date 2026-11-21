import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for paper.tex:1974–1991. The scalar predicate
includes measurability on the original sigma-algebra and finite absolute
integral. Domain integrals use the canonical restricted measure. Every
scalar integral below is accompanied by its integrability proof. No
finiteness, sigma-finiteness, or completeness of the measure is assumed.
`RCLike` includes both real and complex scalars. -/
open Set Filter MeasureTheory
open scoped Topology
universe u
noncomputable section
namespace Specs.D11.Ch06.DomainAdditivity
open Specs.D11.Ch06.ScalarIntegral

/-- Countable disjoint-domain additivity, including absolute convergence of
the scalar series and its actual sum (not merely an equality of totalized sums). -/
def disjoint_domain_additivity : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ E : ℕ → Set X,
    (∀ n, MeasurableSet (E n)) → Pairwise (fun i j => Disjoint (E i) (E j)) →
    ∃ (hE : ∀ n, scalarIntegrable_value (μ.restrict (E n)) f)
      (hU : scalarIntegrable_value (μ.restrict (⋃ n, E n)) f),
      Summable (fun n => ‖scalarIntegral_value (μ.restrict (E n)) f (hE n)‖) ∧
      HasSum (fun n => scalarIntegral_value (μ.restrict (E n)) f (hE n))
        (scalarIntegral_value (μ.restrict (⋃ n, E n)) f hU) ∧
      scalarIntegral_value (μ.restrict (⋃ n, E n)) f hU =
        ∑' n, scalarIntegral_value (μ.restrict (E n)) f (hE n)

/-- The increasing limit domain is its union. No finite-mass assumption is needed. -/
def continuity_from_below : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ E : ℕ → Set X,
    (∀ n, MeasurableSet (E n)) → Monotone E →
    ∃ (hE : ∀ n, scalarIntegrable_value (μ.restrict (E n)) f)
      (hU : scalarIntegrable_value (μ.restrict (⋃ n, E n)) f),
      Tendsto (fun n => scalarIntegral_value (μ.restrict (E n)) f (hE n)) atTop
        (𝓝 (scalarIntegral_value (μ.restrict (⋃ n, E n)) f hU))

/-- The decreasing limit domain is its intersection; even its first term
may have infinite measure, since the function itself is integrable. -/
def continuity_from_above : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ E : ℕ → Set X,
    (∀ n, MeasurableSet (E n)) → Antitone E →
    ∃ (hE : ∀ n, scalarIntegrable_value (μ.restrict (E n)) f)
      (hI : scalarIntegrable_value (μ.restrict (⋂ n, E n)) f),
      Tendsto (fun n => scalarIntegral_value (μ.restrict (E n)) f (hE n)) atTop
        (𝓝 (scalarIntegral_value (μ.restrict (⋂ n, E n)) f hI))

end Specs.D11.Ch06.DomainAdditivity
