import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-! Independent statements for paper.tex:1149–1156 (U3-02).
The signed and complex integrals use the library vector-measure integral,
with scalar multiplication and complex multiplication as the pairings.
Finiteness in the complex case means finite total variation. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace P102.Specs.U3.FiniteMeasureFourier

def kernelType := {d : ℕ} → Euclidean d → Euclidean d → ℂ
def kernelValue : kernelType := fun ξ x =>
  Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I)

def signedTransformType := {d : ℕ} → SignedMeasure (Euclidean d) → Euclidean d → ℂ
def signedTransformValue : signedTransformType := fun ν ξ =>
  ∫ᵛ x, kernelValue ξ x ∂<•ν

def complexTransformType := {d : ℕ} → ComplexMeasure (Euclidean d) → Euclidean d → ℂ
def complexTransformValue : complexTransformType := fun ν ξ =>
  ∫ᵛ x, kernelValue ξ x ∂[ContinuousLinearMap.mul ℝ ℂ; ν]

def signedBoundStatement : Prop :=
  ∀ {d : ℕ} (ν : SignedMeasure (Euclidean d)) (ξ : Euclidean d),
    ‖signedTransformValue ν ξ‖ ≤ ν.totalVariation.real Set.univ

def complexBoundStatement : Prop :=
  ∀ {d : ℕ} (ν : ComplexMeasure (Euclidean d)) [IsFiniteMeasure ν.variation]
    (ξ : Euclidean d), ‖complexTransformValue ν ξ‖ ≤ ν.variation.real Set.univ

def signedContinuousStatement : Prop :=
  ∀ {d : ℕ} (ν : SignedMeasure (Euclidean d)), Continuous (signedTransformValue ν)

def complexContinuousStatement : Prop :=
  ∀ {d : ℕ} (ν : ComplexMeasure (Euclidean d)) [IsFiniteMeasure ν.variation],
    Continuous (complexTransformValue ν)

def signedInjectiveStatement : Prop :=
  ∀ {d : ℕ} (ν η : SignedMeasure (Euclidean d)),
    (∀ ξ, signedTransformValue ν ξ = signedTransformValue η ξ) → ν = η

def complexInjectiveStatement : Prop :=
  ∀ {d : ℕ} (ν η : ComplexMeasure (Euclidean d))
    [IsFiniteMeasure ν.variation] [IsFiniteMeasure η.variation],
    (∀ ξ, complexTransformValue ν ξ = complexTransformValue η ξ) → ν = η

end P102.Specs.U3.FiniteMeasureFourier
