import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.HaarDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportNonnegative
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
Independent statements for paper.tex:5880–5887, measure invariance and
translated integrals. All measures have precisely the Borel domain. Scalars
are real or complex, and scalar integrability includes actual measurability
and finite absolute integral. The nonnegative integral admits infinity.
No countability, sigma-compactness, or measure size assumption is imposed.
-/
namespace Specs.D11.Ch21.HaarTranslationIntegral

open MeasureTheory
open scoped ENNReal
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch05.NonnegativeIntegral
universe u

local instance {G : Type u} [TopologicalSpace G] : MeasurableSpace G := borel G

/-- Invariance for every nonnegative Borel function, including infinite values. -/
def nonnegative_translation : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    Specs.D11.Ch21.HaarDefinition.leftHaarValue μ →
    ∀ (a : G) (f : G → ℝ≥0∞), Measurable f →
      nonnegativeIntegral_value μ (fun x => f (a⁻¹ * x)) =
        nonnegativeIntegral_value μ f

/-- The translated scalar function remains integrable, and its integral agrees. -/
def scalar_translation : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : @Measure G (borel G)), Specs.D11.Ch21.HaarDefinition.leftHaarValue μ →
    ∀ (a : G) (f : G → 𝕜) (hf : scalarIntegrable_value μ f),
      ∃ ht : scalarIntegrable_value μ (fun x => f (a⁻¹ * x)),
        scalarIntegral_value μ (fun x => f (a⁻¹ * x)) ht = scalarIntegral_value μ f hf

/-- For Radon measures the real Cc tests and their translates are integrable;
the displayed test identities force set invariance. Nonzeroness is retained. -/
def leftHaar_of_test_translation : Prop :=
  ∀ {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (μ : @Measure G (borel G)),
    μ ≠ 0 → Specs.D11.Ch18.RadonPredicates.isRadonValue μ →
    (∀ (a : G) (f : CompactlySupportedContinuousMap G ℝ),
      (∫ x, f (a⁻¹ * x) ∂μ) = ∫ x, f x ∂μ) →
    Specs.D11.Ch21.HaarDefinition.leftHaarValue μ

end Specs.D11.Ch21.HaarTranslationIntegral
