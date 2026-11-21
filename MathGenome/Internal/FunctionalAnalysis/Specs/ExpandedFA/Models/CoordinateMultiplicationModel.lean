import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationFourierModel

/-!
Replacement independent interface for the coordinate-generator child of
`fa2:p3:translation-model`.  The whole-line conclusion is for an arbitrary
complex Hilbert multiplicity, including zero and nonseparable spaces.
The restricted scalar model is a required construction, not an input
certificate: `RestrictedSpectralModel` is a full proposition and its existence
is an independent theorem target.  No full-support hypothesis is imposed on E.
-/
noncomputable section
open MeasureTheory Set

namespace ExpandedFA.Models.FullTranslationModel
open Unbounded Unbounded.SymmetryAndDeficienciesSpec
open Unbounded.MeasurableSpectralCalculus
open Semigroups.Stone
universe u

/-- The genuine scalar Bochner L2 space for restricted Lebesgue measure. -/
abbrev RestrictedL2 (E : Set ℝ) := Lp ℂ 2 (volume.restrict E)

/-- The maximal restricted coordinate graph.  The square-integrability clause
uses MemLp, so it is not a totalized-integral finiteness condition. -/
def RestrictedCoordinateGraph (E : Set ℝ) (f g : RestrictedL2 E) : Prop :=
  MemLp (fun r : ℝ => (r : ℂ) * f r) 2 (volume.restrict E) ∧
    (g : ℝ → ℂ) =ᵐ[volume.restrict E] (fun r : ℝ => (r : ℂ) * f r)

/-- The concrete restricted coordinate PVM, bounded multiplication realization,
and exact self-adjoint coordinate graph, with the absolute-continuity and
interval-support conclusions used by the translation-multiplicity warning. -/
def RestrictedSpectralModel (E : Set ℝ) : Prop :=
  ∃ (P : SpectralMeasure.ProjectionValuedMeasure ℝ (RestrictedL2 E))
    (C : BoundedRealization P) (A : Operator ℂ (RestrictedL2 E) (RestrictedL2 E)),
    (∀ B : Set ℝ, MeasurableSet B → ∀ f : RestrictedL2 E,
      (P B f : ℝ → ℂ) =ᵐ[volume.restrict E] B.indicator (fun r => f r)) ∧
    (∀ m : ℝ → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable m →
      ∀ f : RestrictedL2 E,
        (C.integral m f : ℝ → ℂ) =ᵐ[volume.restrict E] (fun r => m r * f r)) ∧
    measurableIntegral C (fun r : ℝ => (r : ℂ)) = A ∧
    selfAdjointValue A ∧
    (∀ f g : RestrictedL2 E, (f, g) ∈ A.graph ↔ RestrictedCoordinateGraph E f g) ∧
    (∀ f : RestrictedL2 E, C.measure f ≪ (volume : Measure ℝ)) ∧
    (∀ a b : ℝ, 0 < volume (E ∩ Ioo a b) → P (Ioo a b) ≠ 0)

namespace CoordinateSpec

/-- Every measurable restriction has the actual coordinate spectral model,
including zero measure and arbitrary measurable sets. -/
def RestrictedModelExistence : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → RestrictedSpectralModel E

/-- The coordinate group and its exact Stone operator.  Equality of graphs
requires both domain necessity and sufficiency, as well as the operator value. -/
def CoordinateGenerator : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    ∃ (W : UnitaryGroup (L2 M)) (B : Operator ℂ (L2 M) (L2 M)),
      IsCoordinateGroup W ∧ selfAdjointValue B ∧ SpectralExponential B W ∧
      DerivativeGraph W B ∧
      (∀ f g : L2 M, (f, g) ∈ B.graph ↔ CoordinateGraph f g)

end CoordinateSpec
end ExpandedFA.Models.FullTranslationModel
