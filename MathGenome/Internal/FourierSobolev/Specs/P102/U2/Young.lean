import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent full proposition types for Young's inequality (paper.tex:793–819).
`eLpNorm` records the usual Lp norm as a nonnegative extended real; all inputs and
outputs in the statements have finite norm. The completion is explicit. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace P102.U2.YoungExpected

/-- Absolute existence a.e., Lr membership and norm bound, and independence of
both representatives. The integral order is the manuscript's f(x-y)g(y). -/
def Result {G 𝕜 : Type*} [Sub G] [MeasurableSpace G] [RCLike 𝕜]
    (μ : Measure G) (p q r : ℝ≥0∞) (f g : G → 𝕜) : Prop :=
  (∀ᵐ x ∂μ, Integrable (fun y => f (x - y) * g y) μ) ∧
  MemLp (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ∧
  eLpNorm (fun x => ∫ y, f (x - y) * g y ∂μ) r μ ≤
    eLpNorm f p μ * eLpNorm g q μ ∧
  ∀ (f' g' : G → 𝕜), f =ᵐ[μ] f' → g =ᵐ[μ] g' →
    ∀ x, (∫ y, f (x - y) * g y ∂μ) = ∫ y, f' (x - y) * g' y ∂μ

/-- The same conclusions with completed measures in every integral and norm. -/
def CompletedResult {G 𝕜 : Type*} [Sub G] [MeasurableSpace G] [RCLike 𝕜]
    (μ : Measure G) (p q r : ℝ≥0∞) (f g : G → 𝕜) : Prop :=
  (∀ᵐ x ∂μ.completion, Integrable (fun y : NullMeasurableSpace G μ => f (@Sub.sub G _ x y) * g y)
    μ.completion) ∧
  MemLp (fun x : NullMeasurableSpace G μ =>
    ∫ y : NullMeasurableSpace G μ, f (@Sub.sub G _ x y) * g y ∂μ.completion) r μ.completion ∧
  eLpNorm (fun x : NullMeasurableSpace G μ =>
    ∫ y : NullMeasurableSpace G μ, f (@Sub.sub G _ x y) * g y ∂μ.completion) r μ.completion ≤
    eLpNorm (α := NullMeasurableSpace G μ) f p μ.completion *
    eLpNorm (α := NullMeasurableSpace G μ) g q μ.completion ∧
  ∀ (f' g' : G → 𝕜), f =ᵐ[μ.completion] f' → g =ᵐ[μ.completion] g' →
    ∀ x : G,
      (∫ y : NullMeasurableSpace G μ, f (@Sub.sub G _ x y) * g y ∂μ.completion) =
      ∫ y : NullMeasurableSpace G μ, f' (@Sub.sub G _ x y) * g' y ∂μ.completion

def EuclideanYoung : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p q r : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 1 ≤ r →
    1 + r⁻¹ = p⁻¹ + q⁻¹ →
    ∀ (f g : EuclideanSpace ℝ (Fin d) → 𝕜), MemLp f p volume → MemLp g q volume →
      Result volume p q r f g

def CircleYoung : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜]
    (p q r : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 1 ≤ r →
    1 + r⁻¹ = p⁻¹ + q⁻¹ →
    ∀ (f g : P102.Periodic.Expected.Circle T → 𝕜),
      MemLp f p (P102.Periodic.Expected.haar T) →
      MemLp g q (P102.Periodic.Expected.haar T) →
      Result (P102.Periodic.Expected.haar T) p q r f g

def EuclideanCompletedYoung : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜]
    (p q r : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 1 ≤ r →
    1 + r⁻¹ = p⁻¹ + q⁻¹ →
    ∀ (f g : EuclideanSpace ℝ (Fin d) → 𝕜),
      MemLp (α := NullMeasurableSpace _ volume) f p volume.completion →
      MemLp (α := NullMeasurableSpace _ volume) g q volume.completion →
      CompletedResult volume p q r f g

def CircleCompletedYoung : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (𝕜 : Type) [RCLike 𝕜]
    (p q r : ℝ≥0∞), 1 ≤ p → 1 ≤ q → 1 ≤ r →
    1 + r⁻¹ = p⁻¹ + q⁻¹ →
    ∀ (f g : P102.Periodic.Expected.Circle T → 𝕜),
      MemLp (α := NullMeasurableSpace _ (P102.Periodic.Expected.haar T))
        f p (P102.Periodic.Expected.haar T).completion →
      MemLp (α := NullMeasurableSpace _ (P102.Periodic.Expected.haar T))
        g q (P102.Periodic.Expected.haar T).completion →
      CompletedResult (P102.Periodic.Expected.haar T) p q r f g

end P102.U2.YoungExpected
