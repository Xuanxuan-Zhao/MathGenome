import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Tensor integrals, paper.tex:2928–2972. The measurable spaces are arbitrary
and the product is ordinary, without completion. The rectangle identity is the
only assumption on the measure η; no finiteness or existence/uniqueness assertion
for arbitrary product extensions is implicit. ENNReal has zero times infinity
zero. Scalar integrability retains actual measurability on the given spaces. -/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace Specs.D11.Ch08.TensorIntegrals
open Specs.D11.Ch05.NonnegativeIntegral (nonnegativeIntegral_value)
open Specs.D11.Ch06.ScalarIntegral (scalarIntegrable_value scalarIntegral_value)

def nonnegative_tensor : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (η : Measure (X × Y)),
    (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
      η (A ×ˢ B) = μ A * ν B) →
    ∀ (u : X → ℝ≥0∞) (v : Y → ℝ≥0∞), Measurable u → Measurable v →
      Measurable (fun z : X × Y => u z.1 * v z.2) ∧
      nonnegativeIntegral_value η (fun z => u z.1 * v z.2) =
        nonnegativeIntegral_value μ u * nonnegativeIntegral_value ν v

def scalar_tensor : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) (η : Measure (X × Y)),
    (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
      η (A ×ˢ B) = μ A * ν B) →
    ∀ (u : X → 𝕜) (v : Y → 𝕜)
      (hu : scalarIntegrable_value μ u) (hv : scalarIntegrable_value ν v),
    ∃ hh : scalarIntegrable_value η (fun z : X × Y => u z.1 * v z.2),
      nonnegativeIntegral_value η (fun z => ENNReal.ofReal ‖u z.1 * v z.2‖) =
        nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖u x‖) *
        nonnegativeIntegral_value ν (fun y => ENNReal.ofReal ‖v y‖) ∧
      scalarIntegral_value η (fun z => u z.1 * v z.2) hh =
        scalarIntegral_value μ u hu * scalarIntegral_value ν v hv

def sigmafinite_uniqueness : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y), SigmaFinite μ → SigmaFinite ν →
    ∀ (η : Measure (X × Y)),
    (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
      η (A ×ˢ B) = μ A * ν B) →
    η = Specs.D11.Ch08.ProductMeasure.productMeasure_value μ ν ∧
    ∀ θ : Measure (X × Y),
      (∀ (A : Set X) (B : Set Y), MeasurableSet A → MeasurableSet B →
        θ (A ×ˢ B) = μ A * ν B) → θ = η

end Specs.D11.Ch08.TensorIntegrals
