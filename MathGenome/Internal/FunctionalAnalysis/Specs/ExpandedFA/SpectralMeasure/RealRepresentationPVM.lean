import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealRepresentationBorelExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RepresentationPVM

/-! The representation theorem on the original real Hilbert space, including
regularity, identification with the actual Borel extension, and uniqueness only
on measurable sets. No countability or nontriviality hypotheses are imposed. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

namespace ExpandedFA.SpectralMeasure.RealRepresentationPVM.Spec
universe u v
open FunctionSpaces.ScalarRieszMarkovSpec
open RealRepresentationBorelExtension.Spec

variable {S : Type u} {H : Type v} [TopologicalSpace S] [CompactSpace S]
  [T2Space S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Regularity is a property of the actual coefficients of this realization.
The competing realization need not come from the chosen Borel extension. -/
def Represents (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
    (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)) : Prop :=
  (∀ x y, FiniteScalarRadon (C.coefficient x y)) ∧
  ∀ f : C(S, ℝ),
    C.integral ⟨f, f.continuous.measurable, ‖f‖, norm_nonneg _, f.norm_coe_le_norm⟩ = π f

/-- Existence and uniqueness of a regular PVM on the original real space,
with the same signed measures and operators as the bounded Borel extension.
The realization structure includes strong-calculus, norm-square and mass laws. -/
def RealRepresentationTheorem : Prop :=
  ∀ (S : Type u) (H : Type v) [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [MeasurableSpace S] [BorelSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (π : C(S, ℝ) →⋆ₐ[ℝ] (H →L[ℝ] H)),
    ∃ (E : RealProjectionValuedMeasure S H) (C : RealBoundedRealization E)
      (μ : H → H → VectorMeasure S ℝ) (Φ : (S → ℝ) → H →L[ℝ] H),
      CoefficientSystem π μ ∧ BorelExtension π μ Φ ∧
      (∀ B, MeasurableSet B → E B = Φ (B.indicator (fun _ => 1))) ∧
      (∀ x y, C.coefficient x y = μ x y) ∧
      (∀ x, C.scalar x = (μ x x).variation) ∧
      (∀ x, Measure.Regular (C.scalar x)) ∧
      Represents E C π ∧
      (∀ g : RealBoundedFunction S, C.integral g = Φ g) ∧
      (∀ (F : RealProjectionValuedMeasure S H) (D : RealBoundedRealization F),
        Represents F D π → ∀ B, MeasurableSet B → F B = E B)

/-- Both scalar cases, with the existing complex theorem unchanged. -/
def FullScalarRepresentationTheorem : Prop :=
  RealRepresentationTheorem.{u, v} ∧ RepresentationPVM.Spec.RepresentationTheorem.{u, v}

end ExpandedFA.SpectralMeasure.RealRepresentationPVM.Spec
