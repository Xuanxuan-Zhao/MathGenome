import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Algebra.Star.StarAlgHom

/-!
Independent statements for the bounded Borel extension stage of
`fa2:p2:representation-pvm`, paper.tex 12404–12420. The Hilbert space is
arbitrary, and the compact Hausdorff space may be empty. All integrations
use multiplication against native complex measures, with no conjugation.
The construction of the PVM and its strong additivity belong to the next stage.
-/
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set

namespace ExpandedFA.SpectralMeasure.RepresentationBorelExtension.Spec
universe u v

variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Representation of each coefficient by a finite regular complex measure,
including the source's variation bound and uniqueness among all such measures. -/
def RepresentsCoefficients (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (μ : H → H → ComplexMeasure S) : Prop :=
  (∀ x y, FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon (μ x y)) ∧
  (∀ x y (f : C(S, ℂ)),
    Integrable f (μ x y).variation ∧
    ⟪x, π f y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral (μ x y) f) ∧
  (∀ x y, (μ x y).variation univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖)) ∧
  (∀ x y (η : ComplexMeasure S),
    FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon η →
    (∀ f : C(S, ℂ), Integrable f η.variation ∧
      ⟪x, π f y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral η f) →
    η = μ x y)

def ScalarMeasures : Prop :=
  ∀ (S : Type u) (H : Type v) [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)),
    ∃ μ : H → H → ComplexMeasure S, RepresentsCoefficients π μ

/-- Operators representing the bounded coefficient forms. Every law below
is on actual bounded Borel functions, with no control measure, a.e. quotient,
separability, or countability assumption. The product law has two arbitrary
bounded Borel factors. -/
def BorelExtension : Prop :=
  ∀ (S : Type u) (H : Type v) [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : C(S, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)),
    ∃ (μ : H → H → ComplexMeasure S) (Φ : (S → ℂ) → H →L[ℂ] H),
      RepresentsCoefficients π μ ∧
      (∀ g, SpectralMeasure.Spec.IsBoundedMeasurable g → ∀ x y,
        Integrable g (μ x y).variation ∧
        ⟪x, Φ g y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral (μ x y) g) ∧
      (∀ f : C(S, ℂ), Φ f = π f) ∧
      Φ (fun _ => 1) = 1 ∧
      (∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
        SpectralMeasure.Spec.IsBoundedMeasurable g → Φ (f + g) = Φ f + Φ g) ∧
      (∀ (c : ℂ) f, SpectralMeasure.Spec.IsBoundedMeasurable f → Φ (c • f) = c • Φ f) ∧
      (∀ f g, SpectralMeasure.Spec.IsBoundedMeasurable f →
        SpectralMeasure.Spec.IsBoundedMeasurable g → Φ (f * g) = Φ f * Φ g) ∧
      (∀ f, SpectralMeasure.Spec.IsBoundedMeasurable f → Φ (star f) = star (Φ f)) ∧
      (∀ f C, SpectralMeasure.Spec.IsBoundedMeasurable f →
        0 ≤ C → (∀ s, ‖f s‖ ≤ C) → ‖Φ f‖ ≤ C) ∧
      (∀ (Ψ : (S → ℂ) → H →L[ℂ] H),
        (∀ g, SpectralMeasure.Spec.IsBoundedMeasurable g → ∀ x y,
          ⟪x, Ψ g y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral (μ x y) g) →
        ∀ g, SpectralMeasure.Spec.IsBoundedMeasurable g → Ψ g = Φ g)

end ExpandedFA.SpectralMeasure.RepresentationBorelExtension.Spec
