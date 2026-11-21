import MathGenome.Internal.RealAnalysis.Specs.D11.Ch07.ConvergenceDefinitions
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction

/-!
Independent statements for paper.tex:2143–2155 and the a.e.-to-local clause
at paper.tex:2395–2403. The scalar field may be real or complex. All functions
are finite and measurable on the given sigma-algebra, and a.e. convergence
uses a measurable null envelope. No completeness or sigma-finiteness is assumed.

The global conclusion uses the strict deviation sets of the shared interface.
Both the ambient restriction and the trace-space restriction are included;
the last statement spells out convergence on every measurable finite-mass set.
-/
open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u

namespace Specs.D11.Ch07.FiniteAeToMeasure

open Specs.D11.Ch07.ConvergenceDefinitions
open Specs.D11.Ch01.ExhaustionRestriction

def finite_ae_to_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜),
    μ univ < ∞ → (∀ n, Measurable (F n)) → Measurable f →
    aeConverges_value μ F f → inMeasureConverges_value μ F f

def ae_to_measure_restrict : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜) (A : Set X),
    MeasurableSet A → μ A < ∞ → (∀ n, Measurable (F n)) → Measurable f →
    aeConverges_value μ F f →
    inMeasureConverges_value (restrictOnSpace_value μ A) F f

def ae_to_measure_subtype : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜) (A : Set X),
    MeasurableSet A → μ A < ∞ → (∀ n, Measurable (F n)) → Measurable f →
    aeConverges_value μ F f →
    inMeasureConverges_value (restrictToSubtype_value μ A)
      (fun n x => F n x.val) (fun x => f x.val)

def ae_to_local_measure : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X)
    (F : ℕ → X → 𝕜) (f : X → 𝕜),
    (∀ n, Measurable (F n)) → Measurable f →
    aeConverges_value μ F f → locallyInMeasureConverges_value μ F f

end Specs.D11.Ch07.FiniteAeToMeasure
