import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.LinearAlgebra.Determinant

/-! Independent statements for paper.tex:3051–3080. `Point n` carries the
Euclidean norm. Every domain below is the full Carathéodory Lebesgue space,
including for scalar integrability, rather than its Borel restriction.
The scalar integral requires an actual integrability proof. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch09.LinearJacobian
open _root_.D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch06.ScalarIntegral

def lebesgue_image_iff : Prop := ∀ (n : ℕ) [NeZero n]
    (T : Point n ≃ₗ[ℝ] Point n) (E : Set (Point n)),
  MeasurableSet[lebesgueSpace_value n] (T '' E) ↔
    MeasurableSet[lebesgueSpace_value n] E

def lebesgue_image_measure : Prop := ∀ (n : ℕ) [NeZero n]
    (T : Point n ≃ₗ[ℝ] Point n) (E : Set (Point n)),
  MeasurableSet[lebesgueSpace_value n] E →
    MeasurableSet[lebesgueSpace_value n] (T '' E) ∧
    lebesgue_value n (T '' E) =
      ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| * lebesgue_value n E

def nonnegative_jacobian : Prop := ∀ (n : ℕ) [NeZero n]
    (T : Point n ≃ₗ[ℝ] Point n),
  letI : MeasurableSpace (Point n) := lebesgueSpace_value n
  ∀ h : Point n → ℝ≥0∞, Measurable h →
    nonnegativeIntegral_value (lebesgue_value n)
        (fun x => ENNReal.ofReal |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| * h (T x)) =
      nonnegativeIntegral_value (lebesgue_value n) h

def scalar_integrable_iff : Prop := ∀ (n : ℕ) [NeZero n]
    (T : Point n ≃ₗ[ℝ] Point n) (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace (Point n) := lebesgueSpace_value n
  ∀ h : Point n → 𝕜,
    scalarIntegrable_value (lebesgue_value n) h ↔
      scalarIntegrable_value (lebesgue_value n) (h ∘ T)

def scalar_jacobian : Prop := ∀ (n : ℕ) [NeZero n]
    (T : Point n ≃ₗ[ℝ] Point n) (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  letI : MeasurableSpace (Point n) := lebesgueSpace_value n
  ∀ (h : Point n → 𝕜) (hh : scalarIntegrable_value (lebesgue_value n) h),
    ∃ hw : scalarIntegrable_value (lebesgue_value n)
        (fun x => |LinearMap.det (T : Point n →ₗ[ℝ] Point n)| • h (T x)),
      scalarIntegral_value (lebesgue_value n) _ hw =
        scalarIntegral_value (lebesgue_value n) h hh

end Specs.D11.Ch09.LinearJacobian
