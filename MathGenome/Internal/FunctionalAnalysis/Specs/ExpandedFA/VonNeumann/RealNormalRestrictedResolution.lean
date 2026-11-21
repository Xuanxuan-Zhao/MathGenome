import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.RealNormalControlMeasure
noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace ExpandedFA.VonNeumann.RealNormalRestrictedResolution.Spec
universe u
open TraceIdeals.RealComplexification
open TraceIdeals.RealComplexification.Spec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := completeSpace

/-- Any closed E-invariant subspace containing the control vector has the
SAME full spectral support, restricted PVM and vector control measure. -/
def RestrictedResolution : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H), IsStarNormal N →
    ∀ (C : RealNormalControlMeasure.Spec.AlgebraModel N)
      (S : Submodule ℂ (Space H)) (hS : IsClosed (S : Set (Space H))),
    letI : CompleteSpace S := hS.completeSpace_coe
    ∀ eS : S, (eS : Space H) = inclusion C.e →
      (∀ B, MeasurableSet B → ∀ s : S, C.E B s ∈ S) →
      ∃ (R : S →L[ℂ] S)
        (F : SpectralMeasure.ProjectionValuedMeasure (RealNormalControlMeasure.Spec.Spectrum N) S),
        (∀ s : S, (R s : Space H) = operator N s) ∧ IsStarNormal R ∧
        spectrum ℂ R = RealNormalControlMeasure.Spec.Spectrum N ∧
        (∀ B, MeasurableSet B → ∀ s : S, (F B s : Space H) = C.E B s) ∧
        (∀ B, MeasurableSet B → C.μ B = ENNReal.ofReal (‖F B eS‖ ^ 2)) ∧
        (∃ ΦR : (RealNormalControlMeasure.Spec.Spectrum N → ℂ) → S →L[ℂ] S,
          SpectralMeasure.BorelNormSpectrum.Spec.BorelCalculus F ΦR ∧
          ΦR (fun z => (z : ℂ)) = R)
end ExpandedFA.VonNeumann.RealNormalRestrictedResolution.Spec
