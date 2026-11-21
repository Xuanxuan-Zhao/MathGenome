import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CzeroDuality
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveRieszMarkov
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch18.RadonSigmaFiniteInner
import Mathlib.Topology.ContinuousMap.Compact

/-! Independent statements for paper.tex:5611–5618. The domain is the native
space of all continuous functions on a compact Hausdorff space, with its uniform
norm. Measures have exactly the Borel sigma-algebra. Positive regularity includes
compact inner regularity on every Borel set. No nonemptiness or countability
assumption is imposed; scalar integration always includes absolute integrability. -/
namespace Specs.D11.Ch19.CompactRepresentation
open Set MeasureTheory
open Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch14.ScalarIntegration Specs.D11.Ch14.TotalVariation
open Specs.D11.Ch19.ComplexRadonVariation
universe u
local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X

/-- Equality of the three function classes, expressed without identifying bundled types. -/
def function_spaces : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (𝕜 : Type) [RCLike 𝕜] (f : C(X, 𝕜)),
    (∃! g : CompactlySupportedContinuousMap X 𝕜, (g : X → 𝕜) = f) ∧
    (∃! g : ZeroAtInftyContinuousMap X 𝕜, (g : X → 𝕜) = f)

/-- Positivity alone suffices for a linear functional on all of C(X,ℝ). -/
def positive_real_representation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (I : C(X, ℝ) →ₗ[ℝ] ℝ),
    (∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f) →
    ∃! μ : @Measure X (borel X),
      Ch18.RadonPredicates.isFullyRegularValue μ ∧ IsFiniteMeasure μ ∧
      ∀ f : C(X, ℝ), ∃ hf : scalarIntegrable_value μ f,
        I f = scalarIntegral_value μ f hf

/-- Representation and the exact operator norm for bounded real-linear functionals. -/
def bounded_real_representation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (L : C(X, ℝ) →L[ℝ] ℝ),
    ∃ ν : SignedMeasure X,
      isSignedRadon_value ν ∧
      (∀ f : C(X, ℝ), ∃ hf : signedIntegrable_value ν f,
        L f = signedIntegral_value ν f hf) ∧
      ‖L‖ = (totalVariation_value ν univ).toReal ∧
      ∀ η : SignedMeasure X, isSignedRadon_value η →
        (∀ f : C(X, ℝ), ∃ hf : signedIntegrable_value η f,
          L f = signedIntegral_value η f hf) → η = ν

/-- The complex pairing is complex-linear and has no conjugation. -/
def bounded_complex_representation : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (L : C(X, ℂ) →L[ℂ] ℂ),
    ∃ ν : ComplexMeasure X,
      isComplexRadon_value ν ∧
      (∀ f : C(X, ℂ), ∃ hf : complexIntegrable_value ν f,
        L f = complexIntegral_value ν f hf) ∧
      ‖L‖ = (totalVariation_value ν univ).toReal ∧
      ∀ η : ComplexMeasure X, isComplexRadon_value η →
        (∀ f : C(X, ℂ), ∃ hf : complexIntegrable_value η f,
          L f = complexIntegral_value η f hf) → η = ν

end Specs.D11.Ch19.CompactRepresentation
